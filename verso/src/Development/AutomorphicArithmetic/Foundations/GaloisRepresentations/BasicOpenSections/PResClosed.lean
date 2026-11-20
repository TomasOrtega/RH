import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.ResClosed

open Polynomial

namespace UpperTheory.Gal.Mod

/- English proof (translation)
Introduce `V _ _ _ _`. Use `IsAlgClosed.of_exists_root _ ?_` and prove the remaining obligations. Introduce `P hmon hirr`. Establish `hl : P ∈ Polynomial.lifts (IsLocalRing.residue V)`. Rewrite using `[Polynomial.mem_lifts]`.

Conclude with `Polynomial.map_surjective _ IsLocalRing.residue_surjective P`. Take `⟨Q, hQ, hdeg, hQm⟩` from `Polynomial.lifts_and_degree_eq_and_monic hl hmon`. Establish `hpos : 0 < P.degree` using `Polynomial.degree_pos_of_irreducible hirr`. Establish `hdeg' : (Q.map (algebraMap V (FractionRing V))).degree ≠ 0`. Rewrite using `[hQm.degree_map, hdeg]`.

Conclude with `hpos.ne'`. Take `⟨x, hx⟩` from `IsAlgClosed.exists_root (Q.map (algebraMap V (FractionRing V))) hdeg'`. Establish `hint : IsIntegral V x` using `⟨Q, hQm, by`. Rewrite `hx` using `[Polynomial.IsRoot.def, Polynomial.eval_map]`. Conclude with `hx⟩`.

Take `⟨y, rfl⟩` from `(IsIntegrallyClosed.isIntegral_iff (K := FractionRing V)).1 hint`. Establish `hy : Q.eval y = 0`. Apply `IsFractionRing.injective V (FractionRing V)` to reduce the goal to its premises. Rewrite using `[map_zero, ← hx.eq_zero, Polynomial.eval_map, Polynomial.eval₂_hom]`. Use `⟨IsLocalRing.residue V y, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hQ, Polynomial.eval_map, Polynomial.eval₂_hom, hy, map_zero]`.
-/
theorem resClosed : ResClosed := by
  intro V _ _ _ _
  refine IsAlgClosed.of_exists_root _ ?_
  intro P hmon hirr
  have hl : P ∈ Polynomial.lifts (IsLocalRing.residue V) := by
    rw [Polynomial.mem_lifts]
    exact Polynomial.map_surjective _ IsLocalRing.residue_surjective P
  obtain ⟨Q, hQ, hdeg, hQm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hmon
  have hpos : 0 < P.degree := Polynomial.degree_pos_of_irreducible hirr
  have hdeg' : (Q.map (algebraMap V (FractionRing V))).degree ≠ 0 := by
    rw [hQm.degree_map, hdeg]
    exact hpos.ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (Q.map (algebraMap V (FractionRing V))) hdeg'
  have hint : IsIntegral V x := ⟨Q, hQm, by
    rw [Polynomial.IsRoot.def, Polynomial.eval_map] at hx
    exact hx⟩
  obtain ⟨y, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (K := FractionRing V)).1 hint
  have hy : Q.eval y = 0 := by
    apply IsFractionRing.injective V (FractionRing V)
    rw [map_zero, ← hx.eq_zero, Polynomial.eval_map, Polynomial.eval₂_hom]
  refine ⟨IsLocalRing.residue V y, ?_⟩
  rw [← hQ, Polynomial.eval_map, Polynomial.eval₂_hom, hy, map_zero]

end UpperTheory.Gal.Mod
