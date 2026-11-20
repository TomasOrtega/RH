import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MultipliableOfRealReOfComplex
import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FMultipliableOfRealReOfComplex.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.multipliable_ofReal_re_of_nonneg_real : ∀ (ι : Type) (c : ι → ℂ), Multipliable c → (∀ i, (c i).im = 0 ∧ 0 ≤ (c i).re) → Multipliable (fun i => ENNReal.ofReal (c i).re) ∧ ∏' i, ENNReal.ofReal (c i).re = ENNReal.ofReal (∏' i, c i).re := by
  first | exact @GlobalTheory.multipliable_ofReal_re_of_complex' | exact GlobalTheory.multipliable_ofReal_re_of_complex' | (intros; apply GlobalTheory.multipliable_ofReal_re_of_complex' <;> assumption)
