# TASK (codex / gpt-5.5): full ASD mod-5 congruences (Hirschhorn §3.6.6–3.6.7)

## NEW file (do not touch others)
Create `QseriesFormalization/Pending/Chapter17_ASD_Mod5_Full.lean`, importing the
committed `QseriesFormalization.Pending.Chapter17_ASD_Mod5` (reuse its `section5`/`A`/
`qPochInfPS_cube_decompose_mod_5`). Do NOT edit `Chapter17_ASD_Mod5.lean`,
`Chapter16_MBI_Proof.lean`, `Chapter08_FiniteRR.lean` (other agents own those), or
`QseriesFormalization.lean`/`Audit.lean`.
Verify single-file `lake env lean ...`; no `lake build`; 0 sorry/axiom/admit; no `sorryAx`.
Reply to `HANDOFF/outbox/codex-asd-mod5-full-reply.md`.

## Goal (Hirschhorn §3.6)
Building on `(q;q)³ ≡ F(q⁵) − 3q·G(q⁵) (mod 5)` (the residue-0 and residue-3-shift parts,
already given by the `A`-decomposition in `Chapter17_ASD_Mod5`), derive the mod-5
generating-function congruences (3.6.6–3.6.7):
```
1/(q;q) = ((q;q)³)³/((q;q)⁵)² ≡ (F − 3qG)³ / (q⁵;q⁵)²   (mod 5)
```
and by extracting residues mod 5, the five congruences
`∑ p(5n+j) qⁿ ≡ (explicit ratio of F,G over (q;q)²)` for j=0..4, including
`∑ p(5n+4) qⁿ ≡ 0` (already proven — reuse it as the j=4 case / sanity check).

## Reachable core (deliverable; choose largest with 0 sorry)
1. Over `ZMod 5`: `(qPochInfPS (ZMod 5))^9 = (expand 5 (qPochInfPS (ZMod 5)))^2 * (the
   residue-decomposition cubed)`, i.e. set up `1/(q;q) ≡ (F−3qG)³/(q⁵;q⁵)²` rigorously at
   the level of `partitionGenFun (ZMod 5)` and the section components `A 0, A 1`.
2. Expand `(A 0 + A 1)³` (here `A 0 = F`, `A 1 = −3q·G`-shaped — match Hirschhorn's signs)
   and extract each residue class mod 5 to express `mk (fun n => (partitionGenFun (ZMod 5)).coeff (5n+j))`
   in terms of the section components and `expand 5 qPoch`. This is the same residue-
   convolution + Frobenius bookkeeping as the mod-11 proof in
   `Pending/Chapter17_Hirschhorn_Mod11.lean`.

NOTE: identifying `F`,`G` as the η-products `(q¹⁰,q¹⁵,q²⁵;q²⁵)`, `(q⁵,q²⁰,q²⁵;q²⁵)`
(eq 3.6.5) needs a Jacobi-triple-product formal-PS coefficient lemma which may not exist
in the repo — that part is a STRETCH; skip if not readily available, and deliver the
section-component form of the congruences instead.

## Infrastructure
- `Chapter17_ASD_Mod5` (`section5`, `A`, `qPochInfPS_cube_decompose_mod_5`, residue lemmas).
- B2, Frobenius `expand_eq_pow_zmod`, `coeff_qPochInfPS_pow_p_in_ZMod_p`,
  `coeff_partitionGenFun_pow`, `partitionGenFun`, `ramanujan_from_pochInf_vanishes` (Ch19).
- The mod-11 residue-convolution pattern (`Pending/Chapter17_Hirschhorn_Mod11.lean`).
