import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisIndexTwoCmConjugation
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FGaloisIndexTwoCmConjugation.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.galois_index_two_cm_conjugation : ∀ (X : Formalism.L2.Col.Fields), X.Core → IsGalois ℚ X.E → ∃ (τ₀ : X.Tau) (H : Subgroup (X.E ≃ₐ[ℚ] X.E)) (γ : H ≃ X.Tau) (c : X.E ≃ₐ[ℚ] X.E), H.index = 2 ∧ (∀ g ∈ H, ∀ x ∈ X.Kq, g x = x) ∧ (∀ (h : H) (x : X.E), X.emb (γ h) x = X.emb τ₀ (h.1 x)) ∧ (∀ x, c x = star x) ∧ c ∉ H := by
  first | exact @GlobalTheory.cmType_equiv_fixingSubgroup | exact GlobalTheory.cmType_equiv_fixingSubgroup | (intros; apply GlobalTheory.cmType_equiv_fixingSubgroup <;> assumption)
