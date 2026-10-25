"""Targeted algebra and equilibrium checks for the integrated manuscript.

The suite checks derivatives, equilibrium examples, and precision bounds.
"""
from pathlib import Path
import sys, json, hashlib, re
ROOT = Path(__file__).resolve().parents[1]
import sympy as s

R = s.Rational
checks = []
def eq(name, lhs, rhs):
    diff = lhs-rhs
    ok = all(s.simplify(z)==0 for z in diff) if isinstance(diff, s.MatrixBase) else s.simplify(diff)==0
    checks.append({"name": name, "passed": bool(ok)})
    if not ok:
        raise AssertionError((name, diff))
def yes(name, condition):
    checks.append({"name": name, "passed": bool(condition)})
    if not condition:
        raise AssertionError(name)

# Exact differentiation of the high-risk all-answer lemma.
t = s.symbols("t", real=True)
K0 = s.Matrix([[3,1],[1,2]])
AB = s.Matrix([[1,2],[-1,1]])
AN = s.Matrix([[2,-1],[1,3]])
X = s.Matrix([[1,2],[3,-1]])
MNB = s.Matrix([[1,2],[0,-1]])
MBB = s.Matrix([[2,1],[1,-1]])
SNB = MNB + AN*K0.inv()*AB.T
SBB = MBB + AB*K0.inv()*AB.T
SNN = AN*K0.inv()*AN.T
Kt = K0 + t*(X.T*AB+AB.T*X) + t*t*X.T*SBB*X
ANt = AN + t*SNB*X
MNNt = SNN-ANt*Kt.inv()*ANt.T
E0 = K0.inv()*AN.T
eq("all_answer_first_cross_derivative",
   MNNt.diff(t).subs(t,0), -MNB*X*E0-E0.T*X.T*MNB.T)

SNB0 = AN*K0.inv()*AB.T
ANt0 = AN+t*SNB0*X
MNNt0 = SNN-ANt0*Kt.inv()*ANt0.T
eq("all_answer_second_derivative_after_cross_block_zero",
   MNNt0.diff(t,2).subs(t,0), 2*E0.T*X.T*MBB*X*E0)
m0 = s.Matrix([1,2])
y0 = K0.inv()*m0
gB = s.Matrix([2,-1])
rB = AB*y0+gB
rN = AN*y0
gNt = rN-ANt0*Kt.inv()*(m0+t*X.T*rB)
eq("all_answer_load_derivative", gNt.diff(t).subs(t,0), -E0.T*X.T*gB)

z11,z12,z21,z22=s.symbols("z11 z12 z21 z22")
Z=s.Matrix([[z11,z12],[z21,z22]])
H=s.eye(2)+K0.inv()*AN.T*Z
eq("fixed_answer_congruence_polynomial",
   K0+Z.T*AN+AN.T*Z+Z.T*SNN*Z, H.T*K0*H)
eq("fixed_answer_load_congruence", m0+Z.T*rN,H.T*m0)

# Nonzero scalar cancellation conditional on a fixed answer.
e=s.ones(3,1); n=s.Matrix([1,-1,0]); v=s.Matrix([1,1,-2])
a=tc=rho=R(1,10)
Lc=tc*(n*v.T+v*n.T)+12*a*a*tc*tc*n*n.T
Dc=s.eye(3)+Lc
dc=e+rho*v+12*a*a*tc*rho*n
z=s.symbols("z",real=True)
c=a*v+z*n
eq("fixed_answer_cancellation_K",(s.Matrix([[3]])+c.T*Lc*c)[0],3*(1+4*a*tc*z)**2)
eq("fixed_answer_cancellation_m",(c.T*dc)[0],6*a*rho*(1+4*a*tc*z))
eq("fixed_answer_cancellation_nonzero_ratio",
   (c.T*dc)[0]**2/(3+(c.T*Lc*c)[0]),12*a*a*rho*rho)
yes("cancellation_demand_positive_definite",all(Dc[:j,:j].det()>0 for j in range(1,4)))
eq("other_answer_not_constant_first_derivative_load",(n.T*dc)[0],24*a*a*tc*rho)

# Resource cancellation preserves welfare but changes group output.
D=s.eye(3)+(e*n.T+n*e.T)/20+v*v.T/10
b=s.Matrix([R(19,20),R(5,4),R(4,5)])
c0=v/10; c1=c0+n/10
def twofactor(C,D,b,weights):
    Xi=s.diag(*weights)
    RR=sum(weights)
    m=(C.T*D*b)[0]
    K=RR+(C.T*(D-Xi)*C)[0]
    zz=-m/K
    qdot=-D*(b+C*zz)
    ell=(b.T*D*b)[0]-m*m/K
    A=s.Matrix([[(1+ci)/2,(1-ci)/2] for ci in C])
    V=s.Matrix([1,-1])
    # Physical Hessian sum, numeraire adjustment, and rebate envelope.
    costH=s.zeros(2)
    for i in range(len(C)):
        ai=A[i,:].T
        costH += weights[i]*(ai*ai.T-s.diag(*ai))
    residual=A.T*qdot+costH*V*zz
    q0dot=-sum(residual)
    eq("physical_factor_clearing_"+str(len(checks)),
       residual+s.ones(2,1)*q0dot/2,s.zeros(2,1))
    eq("envelope_"+str(len(checks)),ell,-(b.T*qdot)[0])
    yes("positive_input_"+str(len(checks)),min(A)>0)
    return m,K,ell,qdot,A.T*s.Matrix(weights)
r0=twofactor(c0,D,b,[s.S.One]*3)
r1=twofactor(c1,D,b,[s.S.One]*3)
eq("resource_same_parent",r0[4],r1[4])
eq("resource_same_welfare",r0[2],r1[2])
Hout=s.Matrix([[1,1,0],[0,0,1]])
yes("resource_different_group_output",Hout*r0[3]!=Hout*r1[3])
eq("resource_column_difference",(D-s.eye(3))*n,e/10)

# Untaxed-nest nonidentification using the same physical reports.
D4=s.diag(R(1,4),R(1,4),1,1)
D4[2:4,2:4]=s.Matrix([[R(3,8),R(-1,8)],[R(-1,8),R(3,8)]])
b4=s.Matrix([1,1,0,0])
ca=s.Matrix([R(1,4),R(1,4),R(-1,4),R(-1,4)])
cb=s.Matrix([R(1,4),R(1,4),0,R(-1,2)])
u0=twofactor(ca,D4,b4,[R(1,4)]*4)
u1=twofactor(cb,D4,b4,[R(1,4)]*4)
groups=s.Matrix([[R(1,4),R(1,4),0,0],[0,0,R(1,4),R(1,4)]])
eq("untaxed_same_group_report",groups*ca,groups*cb)
eq("untaxed_same_endowment",u0[4],u1[4])
eq("untaxed_welfare_difference",u1[2]-u0[2],R(1,2112))

# Re-derive the rational maximization identity and its coefficient.
x,aa,dd,AA=s.symbols("x aa dd AA",positive=True)
den=(aa+(AA-aa)*x)*(dd+(AA-dd)*x)
eq("precision_maximization_identity",
   den-AA*(s.sqrt(aa)+s.sqrt(dd))**2*x*(1-x),
   (s.sqrt(aa*dd)-(AA+s.sqrt(aa*dd))*x)**2)
PP=s.symbols("PP",positive=True)
xx=s.sqrt(aa*dd)/(AA+s.sqrt(aa*dd))
eq("precision_G_coefficient",
   (PP*AA*(dd-aa)*x*(1-x)/den).subs(x,xx),
   PP*(s.sqrt(dd)-s.sqrt(aa))/(s.sqrt(dd)+s.sqrt(aa)))
eta=alpha=R(9,4); sigma=1; beta=R(1,2)
As=eta+alpha; nu=eta+As*beta**2
Ps=As*beta**2/nu; Bs=Ps*As; xs=R(1,4)
def KK(q): return 1+(eta-1)*q+alpha*xs
Lm=Bs*xs*(1/KK(xs)-1/KK(R(27,32)))
eq("finite_32_all_four_groups_lower",Lm,R(19,335))
yes("finite_lower_exceeds_tolerance",Lm>R(1,20))
qpositive=xs+R(15,16)**2*(R(27,32)-xs)
eq("positive_witness_Q_bound",qpositive,R(6323,8192))
yes("positive_witness_exceeds_tolerance",
    Bs*xs*(1/KK(xs)-1/KK(qpositive))>R(1,20))
eq("positive_witness_share_floor",(1-R(15,16))*(1-s.sqrt(xs))/2,R(1,64))
Lambda=Bs*(eta-sigma)/(4*(As-1))
eq("concentrated_sales_upper",Lambda/5,R(3,112))
yes("concentrated_upper_below_tolerance",Lambda/5<R(1,20))

# Record the symbolic checks.
result={
 "date":"2026-10-22",
 "status":"passed",
 "purpose":"Targeted symbolic derivatives, equilibrium witnesses, precision coefficient and finite-weight checks",
 "count":len(checks),
 "checks":checks,
 "coverage":"Symbolic derivatives, equilibrium witnesses, precision coefficients, and finite-weight checks."
}
out=ROOT/"notes"/"presubmission_mathematical_audit_20261022.json"
out.write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
print(json.dumps({"status":"passed","checks":len(checks),"output":str(out)}))
