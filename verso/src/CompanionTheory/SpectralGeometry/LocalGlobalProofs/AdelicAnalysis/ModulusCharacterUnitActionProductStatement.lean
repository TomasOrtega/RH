import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ModulusCharacterUnitActionProduct
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FModulusCharacterUnitActionProduct.lean&line=75#L75)
-/
theorem _root_.GlobalTheory.T.modulus_character_unit_action_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (M : ℕ) (μW : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (μA : Measure (AF F)), μW.IsAddHaarMeasure → μA.IsAddHaarMeasure → ∃ χ : (AF F ⊗[F] E)ˣ →* ℝ≥0, Continuous χ ∧ (∀ a : (AF F ⊗[F] E)ˣ, (μW.prod μA).map (fun p => (sigR (AF F) σ (a : AF F ⊗[F] E) • p.1, Algebra.norm (AF F) (a : AF F ⊗[F] E) * p.2)) = χ a • μW.prod μA) ∧ ∀ x : ℝ, (χ (τ (Multiplicative.ofAdd x)) : ℝ) = Real.exp (-(2 * Module.finrank ℚ F * (M + 1) * x)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.FChi.exists_modulus_chi | exact GlobalTheory.CompanionTheory.SW.FChi.exists_modulus_chi | (intros; apply GlobalTheory.CompanionTheory.SW.FChi.exists_modulus_chi <;> assumption)
