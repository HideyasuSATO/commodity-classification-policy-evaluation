"""Run the three numerical suites and compare their recorded results."""
from pathlib import Path
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
SUITES = [
    ('verify_presubmission_manuscript_20261022.py', 'presubmission_mathematical_audit_20261022.json', 'count'),
    ('verify_demand_aggregation_policy_classification_20261022.py', 'demand_aggregation_policy_classification_audit_20261022.json', 'assertions'),
    ('verify_integrated_classification_frontier_20261022.py', 'integrated_classification_frontier_audit_20261022.json', 'recorded_assertions'),
]


def read(path):
    return json.loads(path.read_text(encoding='utf8'))


def main():
    if not __debug__:
        raise SystemExit('Run without Python optimization (-O).')
    (ROOT / 'notes').mkdir(exist_ok=True)
    total = 0
    for script, output, count_key in SUITES:
        subprocess.run([sys.executable, '-X', 'utf8', str(ROOT / 'tools' / script)], cwd=ROOT, check=True)
        actual = read(ROOT / 'notes' / output)
        reference = read(ROOT.parent / 'reference_results' / output)
        # These two fields describe the original manuscript edition and helper.
        for value in [actual, reference]:
            value.pop('manuscript_sha256', None)
            value.pop('note', None)
        if actual != reference:
            raise SystemExit(f'Result differs from reference: {output}')
        total += actual[count_key]
    print(json.dumps({'status': 'passed', 'recorded_checks': total, 'reference_results_match': True}))


if __name__ == '__main__':
    main()
