import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFinPartOneMulInvMemHeckeSplitCongruence
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLoc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeckeSplitAll.Fin.exists_finPart_eq_one_mul_inv_mem` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FExistsFinPartOneMulInvMemHeckeSplitCongruence.lean&line=308#L308)
-/
theorem _root_.GlobalTheory.T.exists_finPartOne_mul_inv_mem_heckeSplitCongruence : ∀ (D : D7) (N : ℕ), 0 < N → ∀ x : (AE D)ˣ, ∃ z : (AE D)ˣ, finPart D (z : AE D) = 1 ∧ x * z⁻¹ ∈ GlobalTheory.HeckeSplitAll.grpH D N := by
  first | exact @GlobalTheory.HeckeSplitAll.Fin.exists_finPart_eq_one_mul_inv_mem | exact GlobalTheory.HeckeSplitAll.Fin.exists_finPart_eq_one_mul_inv_mem | (intros; apply GlobalTheory.HeckeSplitAll.Fin.exists_finPart_eq_one_mul_inv_mem <;> assumption)
