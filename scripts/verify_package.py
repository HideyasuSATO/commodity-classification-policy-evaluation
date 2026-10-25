"""Check release files, correspondence, and Lean type and axiom records."""
from pathlib import Path
import argparse
import csv
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def read(path):
    return json.loads(path.read_text(encoding='utf8'))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(condition, message):
    if not condition:
        raise ValueError(message)


def check_lean_log(path, declarations):
    raw = path.read_bytes()
    encoding = 'utf-16' if raw.startswith((b'\xff\xfe', b'\xfe\xff')) else 'utf-8-sig'
    text = raw.decode(encoding).replace('\r\n', '\n').replace('\r', '\n')
    check('error:' not in text, f'Lean error in {path.name}')
    axioms = {name: [x.strip() for x in ax.split(',') if x.strip()]
              for name, ax in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", text)}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
        axioms[name] = []
    for d in declarations:
        name, kernel = d['name'], d['resolved_kernel_name']
        check(axioms.get(kernel) == d['axioms'], f'Axiom record differs: {name}')
        match = re.search(r'(?:^|\n)@?' + re.escape(name) + r' : ([\s\S]*?)(?=\n\x27' + re.escape(kernel) + r'\x27)', text)
        check(match is not None and match[1].strip() == d['exact_type_from_lean'], f'Type differs: {name}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean-log', type=Path, help='Output of CheckAllManuscript.lean')
    parser.add_argument('--manuscript', type=Path, help='Optional external manuscript.tex to compare with the recorded edition')
    args = parser.parse_args()
    with (ROOT / 'SHA256SUMS.csv').open(encoding='utf8', newline='') as f:
        rows = list(csv.DictReader(f))
    names = [r['file'] for r in rows]
    check(len(names) == len(set(names)), 'Duplicate checksum entry')
    for row in rows:
        path = (ROOT / row['file']).resolve()
        check(path.is_relative_to(ROOT) and path.is_file(), f'Missing file: {row["file"]}')
        check(sha(path) == row['sha256'], f'File differs: {row["file"]}')
    check((ROOT / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0', 'Lean version differs')
    pins = read(ROOT / 'lake-manifest.json')
    check(next(p for p in pins['packages'] if p['name'] == 'mathlib')['rev'] == '56a005855ea17e0b0958f73ec801ae140b0a1679', 'Mathlib revision differs')
    check(sha(ROOT / 'lake-manifest.json') == '80ef1e517330217c750b498be94566322a30b1c93a2297cfab668a34de7b99eb', 'Dependency manifest differs')
    version = read(ROOT / 'docs/manuscript_version.json')
    claims = read(ROOT / 'docs/claims.json')
    check(claims['manuscript_version'] == version['id'], 'Manuscript version mismatch')
    claims = claims['claims']
    declarations = read(ROOT / 'docs/declarations.json')['declarations']
    by_name = {d['name']: d for d in declarations}
    ids = {c['claim_id'] for c in claims}
    check(len(by_name) == len(declarations) and len(ids) == len(claims), 'Duplicate correspondence key')
    for c in claims:
        check(bool(c['declarations']) and set(c['declarations']) <= by_name.keys(), c['claim_id'])
        check(set(c['dependencies']) <= ids, f'Unknown dependency: {c["claim_id"]}')
        status = 'definition_implemented_and_typechecked' if c['kind'] == 'definition' else 'proved_and_semantically_reviewed'
        check(c['status'] == status, f'Claim status differs: {c["claim_id"]}')
        check(bool(c['anchor']) and bool(c['manuscript_ranges']), f'Missing paper reference: {c["claim_id"]}')
        check(bool(c['paper_reference']) and bool(c['paper_sections']), f'Missing printed location: {c["claim_id"]}')
        check(all(1 <= x['first_page'] <= 24 for x in c['paper_sections']), f'Invalid paper page: {c["claim_id"]}')
        for v in c['manuscript_ranges']:
            check(1 <= v['start'] <= v['end'], f'Invalid source range: {c["claim_id"]}')
    with (ROOT / 'docs/correspondence.csv').open(encoding='utf8', newline='') as f:
        table = list(csv.DictReader(f))
    check(len(table) == len(claims), 'CSV row count differs')
    for row, claim in zip(table, claims):
        check(row['claim_id'] == claim['claim_id'] and row['paper_reference'] == claim['paper_reference'], 'CSV correspondence differs')
    source_cache = {}
    for d in declarations:
        if d['file'] not in source_cache:
            p = ROOT / d['file']
            source_cache[d['file']] = (sha(p), p.read_text(encoding='utf8').splitlines())
        file_sha, lines = source_cache[d['file']]
        check(file_sha == d['sha256'], f'Source differs: {d["file"]}')
        check(d['name'].split('.')[-1] in lines[d['line'] - 1], f'Declaration location differs: {d["name"]}')
        check(bool(d['exact_type_from_lean']), f'Missing type: {d["name"]}')
        refs = set(d['claim_ids'] + d['support_for_claim_ids'])
        check(bool(refs) and refs <= ids, f'Unknown claim: {d["name"]}')
        check(set(d['axioms']) <= ALLOWED_AXIOMS, f'Unexpected axiom: {d["name"]}')
    pending = {c['claim_id']: set(c['dependencies']) for c in claims}
    while pending:
        ready = {key for key, deps in pending.items() if not deps}
        check(bool(ready), 'Claim dependency cycle')
        pending = {key: deps - ready for key, deps in pending.items() if key not in ready}
    audit = read(ROOT / 'audit/public_axioms.json')
    check(audit['unexpected'] == [], 'Unexpected axioms recorded')
    for d in declarations:
        check(audit['declarations'][d['name']] == d['axioms'], f'Axiom metadata differs: {d["name"]}')
    build = read(ROOT / 'audit/build_report.json')
    check(build['build_exit_code'] == 0 and build['direct_audit_exit_code'] == 0, 'Build/audit did not pass')
    check(build['all_research_modules_built'] and build['exact_types_and_axioms_match'], 'Build/audit incomplete')
    check_lean_log(ROOT / 'audit/lean_direct.log', declarations)
    for p in [ROOT / 'LeanMath.lean', *(ROOT / 'LeanMath').rglob('*.lean')]:
        text = re.sub(r'/\-.*?\-/', '', p.read_text(encoding='utf8'), flags=re.S)
        text = re.sub(r'--[^\n]*', '', text)
        check(not re.search(r'\b(?:sorry|admit|sorryAx|axiom|native_decide|unsafe)\b', text), f'Unapproved proof construct: {p.name}')
    if args.lean_log:
        check_lean_log(args.lean_log, declarations)
    if args.manuscript:
        check(sha(args.manuscript) == version['source_sha256'], 'External manuscript is a different edition')
        count = len(args.manuscript.read_text(encoding='utf8').splitlines())
        check(all(v['end'] <= count for c in claims for v in c['manuscript_ranges']), 'Manuscript source range exceeds file')
    print(json.dumps({'status': 'passed', 'correspondence_units': len(claims), 'declarations': len(declarations), 'release_files': len(rows)}, indent=2))


if __name__ == '__main__':
    main()
