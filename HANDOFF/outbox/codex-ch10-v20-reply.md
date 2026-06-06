E6 Ramanujan theta is closed.

Work done:

- In `QseriesFormalization/Pending/Chapter20_LiouvilleConvolution.lean`:
  - generalized the sigma-convolution-to-Liouville bridge to arbitrary exponents:
    `sigmaSigmaConvZ_eq_liouvilleBpowDpowSum`.
  - added the E6 convolution instances:
    `sigma1Sigma5ConvZ_eq_liouvilleBD5Sum`,
    `sigma3Sigma3ConvZ_eq_liouvilleB3D3Sum`.
  - added the degree-6 Liouville weights and P-step identities:
    `liouvilleP15_step_int` for `(b^2+bd+d^2)^3`,
    `liouvilleP33_step_int` for `b^2*d^2*(b+d)^2`.
  - abstracted the Liouville telescope to `scaled_sum_liouvilleQ_eq_boundary_general`.
  - proved the symmetric convolution identity:
    `one_twenty_mul_liouvilleB3D3Sum_eq_sigma7_sub_sigma3`.
  - proved the combined E6 Liouville convolution identity:
    `e6_liouville_convolution_identity`.
  - lifted it back to sigma convolutions:
    `e6_sigma_convolution_identity`.

- In `QseriesFormalization/Pending/Chapter20_Eisenstein.lean`:
  - `ramanujanThetaE6ArithmeticIdentityAt_all` now closes from
    `Ch20LiouvilleConvolution.e6_sigma_convolution_identity`.
  - `RamanujanThetaE6_all` is proved.
  - The file checks with the downstream Eisenstein identity scaffolding.

Verification:

```bash
lake env lean QseriesFormalization/Pending/Chapter20_LiouvilleConvolution.lean
lake env lean QseriesFormalization/Pending/Chapter20_Eisenstein.lean
```

Both commands completed successfully.
