import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformiserIdeleMultiplicativeOnIdeals
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableZterm
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.LatEnt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CMVal.IdealIdele.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsUniformiserIdeleMultiplicativeOnIdeals.lean&line=104#L104)
-/
theorem _root_.GlobalTheory.T.exists_uniformiserIdele_multiplicative_on_ideals : ∀ (E : Type) [Field E] [NumberField E], ∃ t : Ideal (𝓞 E) → (Af E)ˣ, t ⊤ = 1 ∧ (∀ I J, I ≠ ⊥ → J ≠ ⊥ → t (I * J) = t I * t J) ∧ (∀ v : HeightOneSpectrum (𝓞 E), t v.asIdeal = unifAt v) ∧ (∀ I, I ≠ ⊥ → modF (t I) = ((Ideal.absNorm I : ℕ) : ℝ)⁻¹) ∧ (∀ I, I ≠ ⊥ → ∀ w : HeightOneSpectrum (𝓞 E), Valued.v ((t I : Af E) w) ≤ 1 ∧ (w.asIdeal ∣ I → Valued.v ((t I : Af E) w) < 1) ∧ (¬ w.asIdeal ∣ I → (t I : Af E) w = 1)) ∧ (∀ I J, I ≠ ⊥ → J ≠ ⊥ → (∀ w, Valued.v ((t I : Af E) w) = Valued.v ((t J : Af E) w)) → I = J) ∧ ∀ z : (Af E)ˣ, (∀ w, Valued.v ((z : Af E) w) ≤ 1) → ∃ I, I ≠ ⊥ ∧ ∀ w, Valued.v ((t I : Af E) w) = Valued.v ((z : Af E) w) := by
  first | exact @GlobalTheory.CMVal.IdealIdele.main | exact GlobalTheory.CMVal.IdealIdele.main | (intros; apply GlobalTheory.CMVal.IdealIdele.main <;> assumption)
