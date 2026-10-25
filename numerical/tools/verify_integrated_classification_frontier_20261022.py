"""Exact rational checks for the classification frontier.

The suite uses shared GE helper functions and Fraction arithmetic.
"""
from pathlib import Path
from fractions import Fraction as F
import ast
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
helper = ROOT / 'tools/verify_ces_precision_frontier_20261021.py'
names = {'dot', 'mv', 'ge', 'null_direction', 'extreme_same_reports'}
nodes = [node for node in ast.parse(helper.read_text(encoding='utf-8')).body
         if isinstance(node, ast.FunctionDef) and node.name in names]
exec(compile(ast.Module(body=nodes, type_ignores=[]), str(helper), 'exec'))
checks = []

def check(value, name):
    assert value, name
    checks.append(name)

def parameters(eta, alpha, beta):
    A = eta + alpha
    nu = eta + A*beta*beta
    P = A*beta*beta/nu
    return A, nu, P, P*A

def demand(w, v, eta, alpha):
    return [[eta*w[i]*(i == j)+alpha*w[i]*v[i]*w[j]*v[j]
             for j in range(len(w))] for i in range(len(w))]

def moments(w, v, c):
    return dot(w, [v[i]*c[i] for i in range(len(w))]), dot(w, [x*x for x in c])

def report(w, c, labels):
    return [sum(w[i]*c[i] for i in range(len(w)) if labels[i] == g)
            for g in sorted(set(labels))]

def K(s, Q, x, eta, alpha):
    return s+(eta-s)*Q+alpha*x

eta = alpha = F(9, 4)
beta = F(1, 2)
sigma = F(1)
eps = F(1, 20)
A, nu0, P, B = parameters(eta, alpha, beta)
xstar = F(1, 4)
G = F(1, 15)
Lambda = F(15, 112)
check((A, nu0, P, B) == (F(9,2),F(27,8),F(1,3),F(3,2)), 'main parameters')
L4 = B*xstar*(1/K(sigma,xstar,xstar,eta,alpha)-1/K(sigma,F(27,32),xstar,eta,alpha))
check(L4 == F(19,335) and L4 > eps, 'all four-group lower bound')
check(B*xstar*(1/K(sigma,xstar,xstar,eta,alpha)-1/K(sigma,F(3,4),xstar,eta,alpha)) == eps,
      'known-sigma threshold Q = 3/4')
check(Lambda/F(5) == F(3,112) < eps, 'concentrated-sales four-group certificate')

# Conditional variance thresholds on both sides of eta=sigma.
conditional = []
for s in (F(1), F(9,4), F(4)):
    for x,q0 in ((F(0),F(1,8)),(F(1,16),F(1,8)),(F(1,4),F(1,4))):
        k0 = K(s,q0,x,eta,alpha)
        h = abs(eta-s)
        for V in (F(0),F(1,8),F(1,4),F(1,2)):
            q1 = q0+V
            if q1 > 1:
                continue
            width = abs(B*x*(1/k0-1/K(s,q1,x,eta,alpha)))
            if h == 0 or x == 0:
                check(width == 0, 'zero conditional width')
            else:
                sign = 1 if eta > s else -1
                formula = B*x*h*V/(k0*(k0+sign*h*V))
                check(width == formula, 'conditional linked-moment formula')
                if eta > s and B*x <= eps*k0:
                    check(width <= eps, 'automatic positive-branch guarantee')
                else:
                    den = h*(B*x-eps*k0) if eta > s else h*(B*x+eps*k0)
                    threshold = eps*k0*k0/den
                    check((width <= eps) == (V <= threshold), 'variance threshold iff')
            conditional.append({'sigma':s,'x':x,'q0':q0,'V':V,'width':width})

# Sample both pure and mixed partitions. General all-partition proof is analytic.
n = 32
w = [F(1,n)]*n
v = [F(1)]*(n//2)+[F(-1)]*(n//2)
p = [F(1)]*n
D0 = demand(w,v,eta,alpha)
b0 = [1+beta*vi for vi in v]
c0 = [vi/2 for vi in v]
g0 = ge(c0,p,w,D0,b0,sigma)
partition_examples = []
label_sets = [
    [i//8 for i in range(n)],
    [i%4 for i in range(n)],
    [(7*i+i//4)%4 for i in range(n)],
    [min(i,3) for i in range(n)],
    [(i//3)%4 for i in range(n)],
]
for labels in label_sets:
    check(len(set(labels)) == 4, 'four groups in sample')
    cv = extreme_same_reports(c0,labels,v)
    check(moments(w,v,cv)[0] == F(1,2), 'vertex preserves theta')
    check(report(w,cv,labels) == report(w,c0,labels), 'vertex preserves report')
    check(moments(w,v,cv)[1] >= F(27,32), 'vertex capacity lower bound')
    c1 = [(15*u+z)/16 for u,z in zip(cv,c0)]
    g1 = ge(c1,p,w,D0,b0,sigma)
    check(report(w,c1,labels) == report(w,c0,labels), 'positive witness report')
    check(g1['Q'] >= F(6323,8192), 'positive universal witness Q')
    check(g1['minimum_input'] >= F(1,64), 'positive universal share bound')
    check(g0['totals'] == g1['totals'] == [F(1,2),F(1,2)], 'same parent endowment')
    width = abs(g1['normalized']-g0['normalized'])
    check(width > eps, 'positive same-report width exceeds epsilon')
    partition_examples.append({'labels':labels,'c0':c0,'c1':c1,'width':width,
                               'minimum_input':g1['minimum_input']})

# Explicit within-type witness for the displayed 49/885.
labels = [i//8 for i in range(n)]
cv = [v[i]*(1 if i%8 < 6 else -1) for i in range(n)]
c1 = [(7*u+z)/8 for u,z in zip(cv,c0)]
g1 = ge(c1,p,w,D0,b0,sigma)
check(report(w,c1,labels) == report(w,c0,labels), 'explicit four-group report')
check(g1['Q'] == F(211,256), 'explicit four-group Q')
check(g1['minimum_input'] == F(1,32), 'explicit four-group minimum input')
check(abs(g1['normalized']-g0['normalized']) == F(49,885), 'explicit four-group width')

# The same R preserves every conditional target set over the same sigma interval.
# A within-type permutation changes product inputs but not the two moments.
c2 = c1[8:16]+c1[0:8]+c1[24:32]+c1[16:24]
# Use a nontrivial rearrangement within the group.
c2 = [c1[(i//8)*8+(i+3)%8] for i in range(n)]
check(c2 != c1 and moments(w,v,c2) == moments(w,v,c1), 'same moments distinct inputs')
for s in (F(1),F(25,16),F(9,4),F(4)):
    u1 = ge(c1,p,w,D0,b0,s)
    u2 = ge(c2,p,w,D0,b0,s)
    check(u1['normalized'] == u2['normalized'], 'R recovers target for each sigma')
    theta,Q = moments(w,v,c1)
    check(u1['normalized'] == 1-B*theta*theta/K(s,Q,theta*theta,eta,alpha), 'R formula matches physical GE')

# Uncertain sigma floor at its attained positive allocation.
l,u = F(1),F(25,16)
sqrtlu = F(5,4)
xf = sqrtlu/(A+sqrtlu)
floor = P*F(1,9)
check(B*xf*(1/K(l,xf,xf,eta,alpha)-1/K(u,xf,xf,eta,alpha)) == floor == F(1,27),
      'full-input and moment interval floor')

delta = tau = F(1,1000)
e = delta+(1+delta)*(2*tau+tau*tau)
amin = (1-delta)*(1-tau)**2
amax = (1+delta)*(1+tau)**2
upper_R = 2*e/amin
lower_groups = (L4-2*e)/amax
upper_concentrated = (F(3,112)+2*e)/amin
check(e == F(3003001,10**9), 'perturbation e')
check(amin == F(997002999,10**9) and amax == F(1003003001,10**9), 'perturbation normalization')
check(upper_R < eps < lower_groups, 'strict robust separation')
check(upper_concentrated < eps, 'concentrated four groups remain sufficient')

# Nonvanishing demand, policy and input heterogeneity with approximate R recovery.
heterogeneous = []
for n in (4,8,32):
    w = [F(1,n)]*n
    v = [F(1)]*(n//2)+[F(-1)]*(n//2)
    h = [F(1) if i%2 == 0 else F(-1) for i in range(n)]
    check(dot(w,h) == dot(w,[vi*hi for vi,hi in zip(v,h)]) == 0, 'balanced four cells')
    D0 = demand(w,v,eta,alpha)
    b0 = [1+beta*vi for vi in v]
    kap,zeta = F(9,8000),F(1,1000)
    D = [[D0[i][j]+(kap*w[i]*h[i] if i == j else 0) for j in range(n)] for i in range(n)]
    b = [bi+zeta*hi for bi,hi in zip(b0,h)]
    a = r = F(1,4)
    cp = [a*vi+r*hi for vi,hi in zip(v,h)]
    cm = [a*vi-r*hi for vi,hi in zip(v,h)]
    check(moments(w,v,cp) == moments(w,v,cm), 'perturbed economies same R')
    check(kap/eta <= delta and F(2,3)*zeta*zeta <= tau*tau, 'analytic norm bounds')
    gp = ge(cp,[F(1)]*n,w,D,b,sigma)
    gm = ge(cm,[F(1)]*n,w,D,b,sigma)
    check(gp['totals'] == gm['totals'] == [F(1,2)]*2, 'perturbed common benchmark')
    check(gp['m'] == A*beta*a+(eta*zeta+kap)*r, 'perturbed m plus')
    check(gm['m'] == A*beta*a-(eta*zeta+kap)*r, 'perturbed m minus')
    check(gp['K'] == gm['K'] == 1+(eta-1)*(a*a+r*r)+alpha*a*a, 'perturbed common K')
    check(gp['nu'] == nu0+eta*zeta*zeta+2*kap*zeta, 'perturbed nu')
    check(gp['minimum_input'] == gm['minimum_input'] == F(1,4), 'perturbed positive shares')
    check(dot(w,[(a-b)**2 for a,b in zip(cp,cm)]) == F(1,4), 'nonvanishing input uncertainty')
    width = abs(gp['normalized']-gm['normalized'])
    check(0 < width < upper_R < eps, 'approximate not exact recovery')
    heterogeneous.append({'n':n,'same_R':moments(w,v,cp),'width':width,'K':gp['K'],'nu':gp['nu']})

output = {
    'status':'passed', 'recorded_assertions':len(checks),
    'note':'Includes additional exact equilibrium checks from the shared helper.',
    'helper_sha256':hashlib.sha256(helper.read_bytes()).hexdigest(),
    'conditional_cases':conditional, 'partition_examples':partition_examples,
    'perturbed_examples':heterogeneous,
    'certificates':{'L4':L4,'upper_R':upper_R,'lower_four_groups':lower_groups,
                    'upper_concentrated':upper_concentrated,'epsilon':eps},
    'checks':checks,
}
target = ROOT/'notes/integrated_classification_frontier_audit_20261022.json'
target.write_text(json.dumps(output,ensure_ascii=False,indent=2,default=str)+'\n',encoding='utf-8')
print(json.dumps({'status':'passed','recorded_assertions':len(checks),'artifact':str(target)},ensure_ascii=False))
