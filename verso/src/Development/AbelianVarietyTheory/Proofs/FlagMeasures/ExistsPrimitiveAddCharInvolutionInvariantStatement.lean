import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPrimitiveAddCharInvolutionInvariant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
open GlobalTheory.GramCount
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsPrimitiveAddCharInvolutionInvariant.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_primitive_addChar_involution_invariant : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∃ χ : AddChar B ℂ, χ.IsPrimitive ∧ ∀ u, χ (c u) = χ u := by
  first | exact @GlobalTheory.GramCount.exists_isPrimitive_invol_invariant | exact GlobalTheory.GramCount.exists_isPrimitive_invol_invariant | (intros; apply GlobalTheory.GramCount.exists_isPrimitive_invol_invariant <;> assumption)
