import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismProperties
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FIsotropicLeviEmbeddingHomomorphismProperties.lean&line=358#L358)
-/
theorem _root_.GlobalTheory.T.isotropicLeviEmbedding_homomorphism_properties : ∀ k r : ℕ, (∀ u u' : Matrix (Fin r) (Fin r) ℂ, IsUnit u.det → IsUnit u'.det → uEmb k r (u * u') = uEmb k r u * uEmb k r u') ∧ uEmb k r 1 = 1 ∧ (∀ u : Matrix (Fin r) (Fin r) ℂ, IsUnit u.det → uEmb k r u ∈ GG k r ∧ (uEmb k r u)⁻¹ = uEmb k r u⁻¹ ∧ (∀ b : Fin r, uEmb k r u *ᵥ bvec (eI k r b) = ∑ a, u a b • bvec (eI k r a)) ∧ (∀ b : Fin r, uEmb k r u *ᵥ bvec (esI k r b) = ∑ a, star (u⁻¹ b a) • bvec (esI k r a)) ∧ ∀ w, inWb k r w → uEmb k r u *ᵥ w = w) ∧ (∀ x : UT r → ℂ, (upper x).det = 1 ∧ uEmb k r (upper x) ∈ Nset k r) := by
  first | exact @GlobalTheory.Amp.UEmb.uEmb_hom | exact GlobalTheory.Amp.UEmb.uEmb_hom | (intros; apply GlobalTheory.Amp.UEmb.uEmb_hom <;> assumption)
