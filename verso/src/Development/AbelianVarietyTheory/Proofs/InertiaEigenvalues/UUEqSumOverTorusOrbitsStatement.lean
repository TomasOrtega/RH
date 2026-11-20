import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UUEqSumOverTorusOrbits
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FUUEqSumOverTorusOrbits.lean&line=130#L130)
-/
theorem _root_.GlobalTheory.T.UU_eq_sum_over_torus_orbits : ∀ (K : UQ) (B : InvAlg K) (x w : B.A), Finite (Orb K.O B.T (B.X x)) → (∀ o : Orb K.O B.T (B.X x), Finite {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M}) → B.UU x w = ∑ᶠ o : Orb K.O B.T (B.X x), Nat.card {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M} := by
  first | exact @GlobalTheory.UnitLemma.UU_eq_sum_orbits | exact GlobalTheory.UnitLemma.UU_eq_sum_orbits | (intros; apply GlobalTheory.UnitLemma.UU_eq_sum_orbits <;> assumption)
