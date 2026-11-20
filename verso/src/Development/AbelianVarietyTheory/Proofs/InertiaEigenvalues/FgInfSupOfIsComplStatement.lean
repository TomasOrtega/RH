import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FgInfSupOfIsCompl
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.fg_inf_sup_of_isCompl` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFgInfSupOfIsCompl.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.fg_inf_sup_of_isCompl' : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (A : Submodule (𝓞 K) V) (U U' : Submodule K V), A.FG → IsCompl U U' → (U.restrictScalars (𝓞 K) ⊓ (A ⊔ U'.restrictScalars (𝓞 K))).FG := by
  first | exact @GlobalTheory.fg_inf_sup_of_isCompl | exact GlobalTheory.fg_inf_sup_of_isCompl | (intros; apply GlobalTheory.fg_inf_sup_of_isCompl <;> assumption)
