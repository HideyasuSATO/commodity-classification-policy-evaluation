"""Symbolic checks of nested-demand formulas and equilibrium examples."""
from pathlib import Path
import sys
import json

ROOT = Path(__file__).resolve().parents[1]
import sympy as s

R = s.Rational
M = s.Matrix
checks = {}
examples = {}

def eq(label, a, b=0):
    diff = a-b
    ok = all(s.simplify(v) == 0 for v in diff) if isinstance(diff, s.MatrixBase) else s.simplify(diff) == 0
    if not ok:
        raise AssertionError((label, diff))
    checks[label] = True

def require(label, ok):
    if not ok:
        raise AssertionError(label)
    checks[label] = True

def spd(a):
    return all(s.simplify(a[:j, :j].det()) > 0 for j in range(1, a.rows+1))

def demand(p, q, groups, eta, DG, beta):
    E = s.zeros(len(p), len(groups))
    eta_i = [0]*len(p)
    for g, ids in enumerate(groups):
        for i in ids:
            E[i, g] = 1
            eta_i[i] = eta[g]
    Q = s.diag(*q)*E
    S = s.diag(*list(E.T*s.diag(*p)*q))
    Xi = s.diag(*[q[i]/p[i] for i in range(len(p))])
    B = S.inv()*(DG-s.diag(*eta)*S)*S.inv()
    D = s.diag(*eta_i)*Xi+Q*B*Q.T
    b = s.diag(*p)*E*beta
    return D, b, Q, S, Xi

def state(label, p, q, shares, D, b, sigma):
    n, f = shares.shape
    V = M([1, -1]) if f == 2 else M([[1,1],[-1,1],[0,-2]])
    a0 = s.ones(f,1)/f
    A = s.diag(*p)*shares
    C = A*V
    RR = V.T*s.diag(*list(A.T*q))*V
    Xi = s.diag(*[q[i]/p[i] for i in range(n)])
    Hess = s.zeros(f)
    for i in range(n):
        ai = A.row(i).T
        Hess += q[i]*sigma*(ai*ai.T/p[i]-s.diag(*list(ai)))
    T = -V.T*Hess*V
    K = C.T*D*C+T
    m = C.T*D*b
    z = -K.inv()*m
    dq = -D*(b+C*z)
    nu = (b.T*D*b)[0]
    ell = s.factor(nu-(m.T*K.inv()*m)[0])
    residual = A.T*dq+Hess*V*z
    dq0 = -sum(residual)
    require(label+'_positive_shares', all(v > 0 for v in shares))
    eq(label+'_costs', A*s.ones(f,1), p)
    require(label+'_D_SPD', spd(D))
    require(label+'_K_SPD', spd(K))
    eq(label+'_physical_clearing', residual+a0*dq0, s.zeros(f,1))
    eq(label+'_envelope', ell, -(b.T*dq)[0])
    eq(label+'_K_decomposition', K, sigma*RR+C.T*(D-sigma*Xi)*C)
    return dict(A=A,C=C,R=RR,K=K,m=m,ell=ell,nu=nu,V=V,z=z,T=T)

# The four-good untaxed-nest example, checked from physical factor clearing.
p = s.ones(4,1)
q = s.ones(4,1)/4
groups = [[0,1],[2,3]]
DG = s.eye(2)/2
D,b,Q,S,Xi = demand(p,q,groups,[1,2],DG,M([1,0]))
eq('explicit_demand_matrix', D, M([[R(1,4),0,0,0],[0,R(1,4),0,0],[0,0,R(3,8),-R(1,8)],[0,0,-R(1,8),R(3,8)]]))
c0 = M([R(1,4),R(1,4),-R(1,4),-R(1,4)])
c1 = M([R(1,4),R(1,4),0,-R(1,2)])
def sh(c):
    return M([[(1+v)/2,(1-v)/2] for v in c])
e0 = state('baseline',p,q,sh(c0),D,b,1)
e1 = state('untaxed_dispersion',p,q,sh(c1),D,b,1)
eq('same_physical_reports', Q.T*e0['A'], Q.T*e1['A'])
eq('same_parent_endowment', e0['A'].T*q, e1['A'].T*q)
eq('m_value',e0['m'],M([R(1,8)]))
eq('m_preserved',e1['m'],e0['m'])
eq('K0',e0['K'],M([1]))
eq('K1',e1['K'],M([R(33,32)]))
eq('ell0',e0['ell'],R(31,64))
eq('ell1',e1['ell'],R(16,33))
eq('width_witness',e1['ell']-e0['ell'],R(1,2112))
examples['untaxed_nest'] = dict(ell0=str(e0['ell']),ell1=str(e1['ell']),difference='1/2112',minimum_share=str(min(sh(c1))))

# Actual nested utility Hessian: F1 Cobb-Douglas, F2 CES elasticity 2.
xs = s.symbols('x1:5',positive=True)
F = M([2*s.sqrt(xs[0]*xs[1]),(s.sqrt(xs[2])+s.sqrt(xs[3]))**2/2])
ds = F-M([R(1,2),R(1,2)])
utility = sum(ds)-(ds.T*DG.inv()*ds)[0]/2
atq = dict(zip(xs,list(q)))
eq('nested_utility_gradient',M([s.diff(utility,x).subs(atq) for x in xs]),p)
eq('nested_utility_Hessian',s.hessian(utility,xs).subs(atq),-D.inv())

# Differentiate the harmonic composite cost.
w1,w2=s.symbols('w1 w2',positive=True)
for label,st,c in [('mean',e0,c0),('spread',e1,c1)]:
    costs=[w1**((1+c[i])/2)*w2**((1-c[i])/2) for i in [2,3]]
    G=1/(1/(2*costs[0])+1/(2*costs[1]))
    GH=s.hessian(G,(w1,w2)).subs({w1:1,w2:1})
    Jg=(Q.T*st['C']).row(1)
    Hg=s.zeros(1)
    for i in [2,3]:
        Hg += (q[i]/p[i])*(st['C'].row(i).T*st['C'].row(i))
    Vg=Hg-Jg.T*Jg/S[1,1]
    Ig=sum((q[i]*st['A'].row(i).T for i in [2,3]),s.zeros(2,1))
    Rg=st['V'].T*s.diag(*list(Ig))*st['V']
    eq(label+'_composite_curvature',-S[1,1]*st['V'].T*GH*st['V'],Rg-Jg.T*Jg/S[1,1]+Vg)

# Matching nest may stay pooled, even with input dispersion.
c2=M([0,R(1,2),0,-R(1,2)])
e2=state('matching_hidden',p,q,sh(c2),D,b,1)
Qref=M([[R(1,4),0,0],[R(1,4),0,0],[0,R(1,4),0],[0,0,R(1,4)]])
eq('successful_refinement_same_report',Qref.T*e2['A'],Qref.T*e1['A'])
eq('successful_refinement_same_welfare',e2['ell'],e1['ell'])

# Fixed-answer zero load and parent identification under a different fixed policy.
ez=state('zero_report',p,q,sh(M([R(1,4),-R(1,4),R(1,4),-R(1,4)])),D,b,1)
eq('zero_report_welfare',ez['ell'],R(1,2))
require('parent_not_identified',ez['ell'] != e0['ell'])
ep=state('uniform_policy',p,q,sh(c1),D,s.ones(4,1),1)
eq('parent_policy_exception',ep['m'],s.zeros(1,1))

# Six asymmetric goods, three factors, heterogeneous nest elasticities and cross demand.
p=M([1,2,3,R(3,2),R(4,3),R(5,4)])
q=M([R(1,3),R(1,5),R(1,7),R(1,4),R(2,9),R(3,10)])
groups=[[0,1],[2,3],[4,5]]
E=M([[1,0,0],[1,0,0],[0,1,0],[0,1,0],[0,0,1],[0,0,1]])
S=s.diag(*list(E.T*s.diag(*p)*q))
v=M([1,-1,2])
DG=S+S*v*v.T*S/10
beta=M([1,0,R(1,2)])
D,b,Q,S,Xi=demand(p,q,groups,[1,2,R(1,2)],DG,beta)
shares=M([[R(1,2),R(1,3),R(1,6)],[R(1,3),R(1,2),R(1,6)],
          [R(1,4),R(1,4),R(1,2)],[R(1,3),R(1,3),R(1,3)],
          [R(1,5),R(2,5),R(2,5)],[R(2,5),R(1,5),R(2,5)]])
st=state('asymmetric_three_factor',p,q,shares,D,b,1)
J=Q.T*st['C']
eq('general_policy_load',D*b,Q*S.inv()*DG*beta)
eq('general_outer_demand',E.T*s.diag(*p)*D*s.diag(*p)*E,DG)
eq('general_nu',st['nu'],(beta.T*DG*beta)[0])
eq('general_m',st['m'],J.T*S.inv()*DG*beta)
Kbar=st['R']+J.T*S.inv()*(DG-S)*S.inv()*J
covs=[]
for g,ids in enumerate(groups):
    Hg=s.zeros(2)
    for i in ids:
        Hg+=(q[i]/p[i])*st['C'].row(i).T*st['C'].row(i)
    covs.append(Hg-J.row(g).T*J.row(g)/S[g,g])
eq('general_covariance_decomposition',st['K'],Kbar+covs[1]-covs[2]/2)
for g,ids in enumerate(groups):
    i,j=ids
    n=s.zeros(6,1);n[i]=1/q[i];n[j]=-1/q[j]
    eta=[1,2,R(1,2)][g]
    rhs=s.zeros(6,1);rhs[i]=(eta-1)/p[i];rhs[j]=-(eta-1)/p[j]
    eq('pair_column_'+str(g),(D-Xi)*n,rhs)
    eq('pair_load_'+str(g),(n.T*D*b)[0])
    if g:
        require('pair_not_parent_span_'+str(g),M.hstack(q,rhs).rank()==2)

# Covariance change at a group-mean representative and the rank-one identity.
Amean=s.zeros(6,3)
for g,ids in enumerate(groups):
    I=Q[:,g].T*st['A']
    for i in ids:
        Amean[i,:]=p[i]*I/S[g,g]
sm=state('group_mean',p,q,s.diag(*[1/z for z in p])*Amean,D,b,1)
require('nonzero_load_at_mean',sm['m'] != s.zeros(2,1))
u=M([1,0]); t=R(1,10000); i,j=2,3
require('chosen_direction_loaded',(u.T*sm['K'].inv()*sm['m'])[0] != 0)
# Lift a relative input perturbation while preserving cost: rows solve [ones,V].
lift=M.hstack(s.ones(3,1),sm['V']).inv()
Apert=Amean.copy()
da=(M([[0,t,0]])*lift)
Apert[i,:]+=da/q[i];Apert[j,:]-=da/q[j]
sp=state('rank_one_witness',p,q,s.diag(*[1/z for z in p])*Apert,D,b,1)
delta=t*t*(1/(p[i]*q[i])+1/(p[j]*q[j]))
eq('rank_one_same_reports',Q.T*Apert,Q.T*Amean)
eq('rank_one_K',sp['K'],sm['K']+delta*u*u.T)
eq('rank_one_m',sp['m'],sm['m'])
pred=delta*(u.T*sm['K'].inv()*sm['m'])[0]**2/(1+delta*(u.T*sm['K'].inv()*u)[0])
eq('Sherman_Morrison_welfare',sp['ell']-sm['ell'],pred)
require('rank_one_welfare_differs',pred>0)

out=dict(status='passed',assertions=len(checks),checks=checks,examples=examples,
         scope='Exact formulas, equilibrium examples, and physical factor clearing.',
         sympy_version=s.__version__)
(ROOT/'notes'/'demand_aggregation_policy_classification_audit_20261022.json').write_text(json.dumps(out,ensure_ascii=False,indent=2),encoding='utf-8')
print(json.dumps({k:out[k] for k in ['status','assertions','examples','sympy_version']},ensure_ascii=False))
