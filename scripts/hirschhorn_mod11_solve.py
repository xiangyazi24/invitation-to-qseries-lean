from itertools import product
from math import factorial
from functools import reduce

subs=[0,1,3,6,10]; names=['J0','J1','J3','J6','J10']; P11=11
def mult(exps):
    return factorial(sum(exps))//reduce(lambda a,b:a*b,[factorial(e) for e in exps],1)
def part(power,res):
    out={}
    def gen(i,rem,cur):
        if i==4:
            c=cur+[rem]; w=sum(e*s for e,s in zip(c,subs))%P11
            if w==res:
                co=mult(c)%P11
                if co: out[tuple(c)]=co
            return
        for e in range(rem+1): gen(i+1,rem-e,cur+[e])
    gen(0,power,[]); return out

P=part(7,6)
R={r:part(4,r) for r in [3,6,8,9,10]}

# unknown multipliers M_r: degree-3 monomials with residue (6-r)%11
def deg_monos(deg,res):
    ms=[]
    def gen(i,rem,cur):
        if i==4:
            c=cur+[rem]; w=sum(e*s for e,s in zip(c,subs))%P11
            if w==res: ms.append(tuple(c))
            return
        for e in range(rem+1): gen(i+1,rem-e,cur+[e])
    gen(0,deg,[]); return ms

# columns: for each r, each degree-3 monomial m of residue (6-r), the product m*R_r is a degree-7 residue-6 poly
# unknown coeff for each (r,m). Build linear system over GF(11): sum = P.
unknowns=[]   # list of (r,m)
cols=[]       # each col: dict exps7->coeff (the poly m*R_r)
for r in [3,6,8,9,10]:
    res=(6-r)%P11
    for m in deg_monos(3,res):
        poly={}
        for er,cr in R[r].items():
            e7=tuple(m[i]+er[i] for i in range(5))
            poly[e7]=(poly.get(e7,0)+cr)%P11
        unknowns.append((r,m)); cols.append(poly)

# all degree-7 residue-6 monomials (rows)
rows=sorted(set().union(*[set(c) for c in cols], set(P)))
rowidx={e:i for i,e in enumerate(rows)}
A=[[0]*len(cols) for _ in rows]
for j,c in enumerate(cols):
    for e,co in c.items(): A[rowidx[e]][j]=co%P11
b=[P.get(e,0)%P11 for e in rows]

# Gaussian elimination over GF(11)
def inv(a): 
    for x in range(1,P11):
        if a*x%P11==1: return x
    return None
M=[row[:]+[b[i]] for i,row in enumerate(A)]
nr=len(M); nc=len(cols)
piv=[]; r0=0
for col in range(nc):
    pr=None
    for rr in range(r0,nr):
        if M[rr][col]%P11!=0: pr=rr;break
    if pr is None: continue
    M[r0],M[pr]=M[pr],M[r0]
    iv=inv(M[r0][col]%P11)
    M[r0]=[(x*iv)%P11 for x in M[r0]]
    for rr in range(nr):
        if rr!=r0 and M[rr][col]%P11!=0:
            f=M[rr][col]%P11
            M[rr]=[(M[rr][k]-f*M[r0][k])%P11 for k in range(nc+1)]
    piv.append((r0,col)); r0+=1

# check consistency
consistent=True
for rr in range(nr):
    if all(M[rr][k]%P11==0 for k in range(nc)) and M[rr][nc]%P11!=0:
        consistent=False
print("System consistent (P in ideal of R_r):",consistent)
# extract a particular solution: set free vars=0
sol=[0]*nc
for (pr,col) in piv:
    sol[col]=M[pr][nc]%P11
# verify
chk={}
for j,c in enumerate(cols):
    if sol[j]:
        for e,co in c.items(): chk[e]=(chk.get(e,0)+sol[j]*co)%P11
chk={e:v for e,v in chk.items() if v%P11}
Pn={e:v%P11 for e,v in P.items() if v%P11}
print("Solution reproduces P exactly:", chk==Pn)
print("\nMultiplier polynomials M_r (P = sum_r M_r * R_r):")
for r in [3,6,8,9,10]:
    terms=[]
    for j,(rr,m) in enumerate(unknowns):
        if rr==r and sol[j]:
            mon='*'.join(f'{names[i]}^{m[i]}' if m[i]>1 else names[i] for i in range(5) if m[i]) or '1'
            terms.append(f'{sol[j]}*{mon}')
    print(f"  M_{r} =", ' + '.join(terms) if terms else '0')
