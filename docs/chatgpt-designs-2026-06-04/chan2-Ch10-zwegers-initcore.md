# ChatGPT Pro (chan2): Zwegers init cores — complete 23-lemma design
(Pasted by Xiang 2026-06-05. Key structure; q=Q^3, J(z;R)=sum (-1)^r R^{T(r)} z^r, T(r)=r(r-1)/2.)

## Theta-product slices C_m = [x^m] Theta(x;q^2)Theta(x;q) = sum_n (-1)^m q^{n(n-1)+T(m-n)}
C_1 = -J(-1;q^3)        [n(n-1)+T(1-n) = 3T(n)]
C_2 =  J(-q^2;q^3)      [r=n-1: n(n-1)+T(2-n) = 3T(r)+2r]
C_3 = -q J(-q^2;q^3)    [r=1-n: n(n-1)+T(3-n) = 1+3T(r)+2r]
In Q-form: -qJ(-q^2;q^3) = single 3 (-1) * J(-Q^6;Q^9).

## Circle-sum slices L_j = sum_k (-1)^{k+j}(delta3(k)-delta3(j)) Q^{k^2+j^2}
L_0 = 2Q J(q^5;q^6) = single 1 2 * J(Q^15;Q^18)   [bijection ZZ+ZZ ~ {3 nmid k}: inl r -> 3r+1, inr r -> -(3r+1);
   (3r+1)^2 = 1+3(3r^2+2r); -(-1)^{3r+1} = (-1)^r both branches]
L_1 = -Q J(q^3;q^6) = single 1 (-1) * J(Q^9;Q^18)  [k=3r; (3r)^2+1 = 1+3(3r^2); (-1)^{3r+1} = -(-1)^r]
L_2 = Q^4 J(q^3;q^6) = single 4 1 * J(Q^9;Q^18)    [k=3r; (3r)^2+4 = 4+3(3r^2); (-1)^{3r+2} = (-1)^r]

## The two product identities (JTP + AP splitting; both sides reduce to the SAME mod-18 AP product)
(P0)  2 poch_q2 J(q^5;q^6) = poch_q J(-1;q^3)
   JTP: J(q^5;q^6)=(q;q^6)(q^5;q^6)(q^6;q^6); J(-1;q^3)=2(-q^3;q^3)^2(q^3;q^3).
   Use (q^3;q^3)(-q^3;q^3)=(q^6;q^6); (q^2;q^2)=(q^2;q^6)(q^4;q^6)(q^6;q^6); (q;q)=prod of 6 mod-6 APs.
   Both sides -> 2(Q^3;Q^18)(Q^6;Q^18)(Q^12;Q^18)(Q^15;Q^18)(Q^18;Q^18)^2.
(P12) poch_q2 J(q^3;q^6) = poch_q J(-q^2;q^3)
   JTP: J(q^3;q^6)=(q^3;q^6)^2(q^6;q^6); J(-q^2;q^3)=(-q;q^3)(-q^2;q^3)(q^3;q^3).
   Pair (q;q^3)(-q;q^3)=(q^2;q^6); (q^2;q^3)(-q^2;q^3)=(q^4;q^6); split (q^3;q^3)=(q^3;q^6)(q^6;q^6).
   Both sides -> (Q^6;Q^18)(Q^9;Q^18)^2(Q^12;Q^18)(Q^18;Q^18)^2.

## Dispatch (j=0,1,2 by interval_cases): e.g. j=0:
poch_q2 * L_0 = 2Q poch_q2 J(q^5;q^6) = Q poch_q J(-1;q^3) = single 1 (-1) * poch_q * (-J(-1;q^3)) = RHS. 
j=2 uses single 1 (-1) * single 3 (-1) = single 4 1.
y-mirror identical.

## Ordered lemma list (23): A. arithmetic (Tn_one_sub, Tn_two_sub_shift, Tn_three_sub_reflect,
sq_mod3_nonzero_bij + inverse, multiples_three_bij, exponent/sign lemmas 6-11). B. theta-product slices (12-14).
C. circle slices (15-17). D. product identities init_product_j0/init_product_j12 (18-19).
E. dispatch zwegers_init_x_core_j0/j1/j2 + interval_cases wrapper (20-23). y-mirror same.
