# ChatGPT Pro (chan1): HM2.3 final transport — exact reindexing blueprint
(Full content pasted by Xiang 2026-06-04; key structure below. C(t):=t(t-1)/2.
Gamma(D,k)=1 if D>0,k>=0; -1 if D<0,k<0; 0 else. geomInv(D)=sum_k Gamma(D,k)Q^{kD}.)

## Term 1: S(a,z1)·j(z0)·j(a+z0)·j(a+z1), indices (r,k,i,j,l), D1(r)=90(r-1)+a+z1
Substitution: m=r-j, p=j+l+k, z'=r+i-j-l-k-1, N'=C(r)+C(i)+C(j)+C(l)+k(r-1)-C(m)-C(p).
PF branch index = k, u-power = z', PF window = N'.
Exponent identity: E1 = 90(C(m)+C(p)+N') + z0(1-m+p+z') + z1(m+p) + a·p.
Sign: (-1)^{r+i+j+l} = (-1)^{m+p}·(-1)^{i+j-k}.
Inverse: i=z'+p-r+1, j=r-m, l=p-r+m-k.  N' = N_{m,p,z}(r,k):=C(r)+C(z+p-r+1)+C(r-m)+C(p-r+m-k)+k(r-1)-C(m)-C(p).

## Term 2: S(a,z0)·j(z1)·j(a+z0)·j(a+z1), indices (s,k,h,j,l), D0(s)=90(s-1)+a+z0
Substitution: m=h-j-k, p=j+l+k, z'=s+h-j-l-k-1, N'=C(s)+C(h)+C(j)+C(l)+k(s-1)-C(m)-C(p).
Same exponent identity E0 = 90(C(m)+C(p)+N') + z0(1-m+p+z') + z1(m+p) + a·p.
Sign: (-1)^{s+h+j+l} = (-1)^{m+p}·(-1)^{s+j}. With r:=h-k, inverse: h=r+k, s=z'+p-r+1-k, j=r-m, l=p-r+m-k.

## Difference-cancellation involution
Phi(r,k,i,j,l) = (i-k, k, r+k, j, l);  Phi^{-1}(s,k,h,j,l) = (h-k, k, s+k, j, l).
Exponent preservation: C(r)+C(i)+k(r-1) = C(i-k)+C(r+k)+k(i-k-1)  ==>  E1(r,k,i,j,l) = E0(i-k,k,r+k,j,l).
Parity: r+i+j+l = (i-k)+(r+k)+j+l. Since term 2 subtracted, contribution is
(-1)^{r+i+j+l}(Gamma(D1(r),k) - Gamma(D0(i-k),k)), which in (m,p,z,r,k) coords is
(-1)^{m+p}(-1)^{z+p-m+1-k}(Gamma(90(r-1)+a+z1,k) - Gamma(90(z+p-r-k)+a+z0,k)).
Cancellation: Gamma(D1,k)-Gamma(D0,k)=0 when same sign; +1 if D0<0<D1; -1 if D1<0<D0. [discrete residue cancellation]

## RHS emergence (after hPF projection kills z'!=0; set z'=0)
Linear part: z0(1-m+p)+z1(m+p)+a·p = z0 + (z1-z0)m + (a+z0+z1)p.
Q^{90C(m)+(z1-z0)m} = m-th theta monomial of j(z1-z0); Q^{90C(p)+(a+z0+z1)p} = p-th of j(a+z0+z1).
Sign after projection: (-1)^{m+p}=(-1)^m(-1)^p. Outer monomial: Q^{z0}·(-1)^m Q^{90C(m)+(z1-z0)m}·(-1)^p Q^{90C(p)+(a+z0+z1)p}.

## Finite-set bijections
E_out(m,p,z,N) := 90(C(m)+C(p)+N) + z0(1-m+p+z) + z1(m+p) + a·p.
W_e := {(m,p,z,N,r,k): E_out=e, N=N_{m,p,z}(r,k)}.
Psi1(r,k,i,j,l)=(m,p,z,N,r,k) with the Term-1 substitution; inverse (r,k, z+p-r+1, r-m, p-r+m-k).
Psi0(s,k,h,j,l)=(m,p,z,N,r,k) with the Term-2 substitution (r=h-k); inverse (z+p-r+1-k, k, r+k, r-m, p-r+m-k).
Pullback of Psi0 through Phi^{-1} = Psi1 coordinates.

## Final chain
L_e = sum_{E_out=e} (-1)^{m+p}·hPFraw(N,z), where
hPFraw(N,z) = sum_{N=N_{m,p,z}(r,k)} (-1)^{z+p-m+1-k}(Gamma(90(r-1)+a+z1,k)-Gamma(90(z+p-r-k)+a+z0,k))
  = thetaMulPFRawCoeffPF(N,z)   [hPF projection]
  = thetaMulPFCoeffPF(N,z)      [raw=compressed]
  = J3Coeff(N)·1_{z=0}          [compressed PF]
==> L_e = sum_{z0+90N+90C(m)+(z1-z0)m+90C(p)+(a+z0+z1)p=e} J3Coeff(N)(-1)^m(-1)^p
       = lcoeff[ Q^{z0}·J^3·j(z1-z0)·j(a+z0+z1) ] e.
Rewrite sequence: fourFactorWindow -> Psi1/Psi0 finite-Icc reindex -> Phi difference cancellation
-> sign_bookkeeping -> hPF_projection -> raw_eq_compressed -> thetaMulPFCoeffPF -> rhsCoeff.
