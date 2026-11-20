import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonUnramifiedExtension
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.compositum_finite_formallyUnramified` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsCommonUnramifiedExtension.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_common_unramified_extension : ∀ {k K L : Type} [Field k] [Field K] [Field L] (i : k →+* K) (j : k →+* L), i.Finite → i.FormallyUnramified → ∃ (M : Type) (_ : Field M) (u : K →+* M) (v : L →+* M), u.comp i = v.comp j ∧ v.Finite ∧ v.FormallyUnramified := by
  first | exact @GlobalTheory.compositum_finite_formallyUnramified | exact GlobalTheory.compositum_finite_formallyUnramified | (intros; apply GlobalTheory.compositum_finite_formallyUnramified <;> assumption)
