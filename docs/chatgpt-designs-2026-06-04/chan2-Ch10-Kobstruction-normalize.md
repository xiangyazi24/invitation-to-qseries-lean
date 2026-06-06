The obstruction is presentation-real but mathematically artificial.
Let


$$A_a:=\frac{J_a}{K}=(Q^a;Q^{90})_\infty(Q^{90-a};Q^{90})_\infty .$$


Then every $J_a$ contributes exactly one hidden $K$.
For your LHS, the total exponent sum is


$$6+3+4+5+6+3+6+4+5+5+6+1+6+5+2=67.$$


So


$$Q^4\prod J_a^{e_a}
=
K^{67}\,Q^4\prod A_a^{e_a}.$$


For every one of the 30 $P30$ terms, the exponent-vector sum is exactly


$$19.$$


Thus


$$K^{48}\cdot P30
=
K^{48}\sum_t c_tQ^{d_t}\prod J_a^{v_{t,a}}
=
K^{48}\sum_t c_tQ^{d_t}K^{19}\prod A_a^{v_{t,a}}
=
K^{67}\sum_t c_tQ^{d_t}\prod A_a^{v_{t,a}}.$$


So the exact total $K$-degree is:


$$\boxed{\text{LHS total }K\text{-degree}=67,\qquad \text{RHS total }K\text{-degree}=48+19=67.}$$


Therefore your Riemann-span obstruction is not an obstruction in $\mathbb Q((Q))$. It is an obstruction only in the unnormalized polynomial presentation where $K$ is treated as independent from the $J_a$’s.
The correct normalized identity is:


$$\boxed{
Q^4\prod_a A_a^{e_a}
=
\sum_{t=1}^{30} c_tQ^{d_t}\prod_a A_a^{v_{t,a}}.
}$$


Equivalently, after full $P_r$-expansion:


$$A_a=P_aP_{90-a},$$


so this becomes a pure AP-product identity in the $P_r=(Q^r;Q^{90})_\infty$ basis.
I would not try to close this with ordinary Riemann theta addition. Riemann-90 is homogeneous in unnormalized theta factors and cannot create the explicit $K^{48}$-block. The needed move is exactly the normalization


$$J_a \mapsto A_a=J_a/K.$$


Then the identity lives in the normalized theta/eta-product algebra. In Lean, the clean route is:


define redJ a := jLaurent a 90 / K;


prove redJ a = qPochAP a 90 * qPochAP (90-a) 90;


rewrite the whole residual by J_a = K * redJ a;


collect powers of $K$, using the two degree lemmas:


$$\sum e_a=67,\qquad \forall t,\ \sum_a v_{t,a}=19;$$




cancel $K^{67}$, using nonzero/unit facts for $K=(Q^{90};Q^{90})_\infty$;


prove the remaining normalized AP-product identity.


So the better bridge is: avoid bare $K$-graded Riemann algebra entirely; bridge through normalized level-90 atoms $A_a=J_a/K$. The final crux is then not a new Riemann relation, but a normalized eta-product/AP-product identity.