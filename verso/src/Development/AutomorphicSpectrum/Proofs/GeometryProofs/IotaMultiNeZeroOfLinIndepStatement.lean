import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IotaMultiNeZeroOfLinIndep
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FIotaMultiNeZeroOfLinIndep.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.iota_multi_ne_zero_of_lin_indep : ∀ (Ω V : Type) [Field Ω] [AddCommGroup V] [Module Ω V] (n : ℕ) (e : Fin n → V), LinearIndependent Ω e → exteriorPower.ιMulti Ω n e ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Exterior.ιMulti_ne_zero_of_linearIndependent | exact GlobalTheory.CompanionTheory.Exterior.ιMulti_ne_zero_of_linearIndependent | (intros; apply GlobalTheory.CompanionTheory.Exterior.ιMulti_ne_zero_of_linearIndependent <;> assumption)
