import QseriesFormalization.Chapter02
import QseriesFormalization.Chapter03

/-!
# Chapter 5 — the Jacobi Triple Product (Chan §5's main result)

Chan §5 ("Borcherds' proof of the Jacobi Triple Product" / Boson–Fermion
correspondence) has as its **main result the Jacobi Triple Product identity
(JTP)** itself; §5 gives a particular proof of it via the Boson–Fermion
correspondence (eqs 5.2 + 5.4).

The repository's `Chapter05*.lean` files instead contain **Franklin's
involution** (a combinatorial proof of Euler's pentagonal number theorem,
Chan §4 material), so the audit marks `Chapter05.lean` MISLABELED.

This file records that **Chan §5's main theorem — the JTP — IS proved in this
repository**, namely as `QseriesFormalization.PartI.Ch02.jacobiTripleProduct`:

  for `‖q‖ < 1` and `z ≠ 0`,
  `∏_{n≥1} (1 - q^{2n})(1 + z q^{2n-1})(1 + z⁻¹ q^{2n-1})  =  ∑_{n ∈ ℤ} zⁿ q^{n²}`.

The proof used here is the **finite-JTP limit** (Chan §3 route), **not** the
Boson–Fermion correspondence of Chan §5.  So the *theorem* of §5 is available;
the specific §5 *proof method* (vertex-operator / fermionic Fock space) is not
formalized.
-/

namespace QseriesFormalization
namespace Pending
namespace Ch05JTP

open QseriesFormalization.PartI.Ch02

/-- **Jacobi Triple Product (Chan §5 main theorem)** — re-export of the proved
`Ch02.jacobiTripleProduct`.  For `‖q‖ < 1`, `z ≠ 0`:

  `jacobiInfiniteProduct q z = jacobiInfiniteSeries q z`,

i.e. `∏_{n≥1}(1-q^{2n})(1+z q^{2n-1})(1+z⁻¹ q^{2n-1}) = ∑_{n∈ℤ} zⁿ q^{n²}`. -/
theorem jacobi_triple_product (q z : ℂ) (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    jacobiInfiniteProduct q z = jacobiInfiniteSeries q z :=
  jacobiTripleProduct q z hq hz

/-- **Unfolded form** of the JTP, showing the explicit product and bilateral
sum that Chan §5 states. -/
theorem jacobi_triple_product_unfolded (q z : ℂ) (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    (∏' n : ℕ+, (1 - q ^ (2 * n.val)) *
        (1 + z * q ^ (2 * n.val - 1)) *
        (1 + z⁻¹ * q ^ (2 * n.val - 1)))
      = ∑' n : ℤ, z ^ n * q ^ (n ^ 2) :=
  jacobiTripleProduct q z hq hz

end Ch05JTP
end Pending
end QseriesFormalization
