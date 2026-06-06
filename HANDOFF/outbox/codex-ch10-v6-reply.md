Added a low-degree theta-log recurrence check for the Ch10 Eq. (10.15) LHS
coefficient data in `QseriesFormalization/Pending/Chapter10_TenthOrder.lean`.

What changed:
- Added integer AP-sigma coefficient helpers:
  - `apDivisorSigmaCoeffZ`
  - `chan1015RHSThetaLogAPCoeffZ`
- Added a finite-vector residual for the equation
  `Theta(f) = chan1015RHSThetaLogAP * f`:
  - `thetaLogResidualCoeffVecZ`
  - `chan1015LHSThetaLogResidualVec`
- Proved the cached degree-15 LHS coefficient vector satisfies the RHS
  AP theta-log recurrence through degree 15:
  - `chan1015LHSThetaLogResidualVec_fifteen :
      chan1015LHSThetaLogResidualVec 15 = Vector.replicate 16 0`
- Added the coefficient bridge for the explicit AP theta-log series:
  - `coeff_chan1015RHSThetaLogAP :
      chan1015RHSThetaLogAP.coeff n =
        (chan1015RHSThetaLogAPCoeffZ n : ℚ)`

Status:
- This confirms that the same AP theta-log recurrence is numerically
  compatible with the verified Ch10 LHS coefficient vector through degree 15.
- I did not close the full remaining target
  `SatisfiesThetaLogRecurrence chan1015RHSThetaLogAP (chan1015LHSPS ℚ)`.
  That still needs an all-`n` argument for the four-variable indefinite theta
  coefficient formula.
- I also tried upgrading the cached degree-15 result to a raw theorem
  `chan1015LHSCoeffVecRaw 15 = chan1015CoeffVecFifteen`; direct `decide`
  over the raw four-variable sums ran too long, so I did not leave that in the
  file.

Validation:
- `lake env lean QseriesFormalization/Pending/Chapter10_TenthOrder.lean`
  passed.
- `rg -n "sorry|axiom|native_decide|#guard" QseriesFormalization/Pending/Chapter10_TenthOrder.lean`
  returned no matches.
