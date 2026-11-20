import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuadricFibreMeasureEqSmulNormalisedProduct
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GaugeEx.isXbetaMeasure_iff_smul_std` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FQuadricFibreMeasureEqSmulNormalisedProduct.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.quadricFibreMeasure_eq_smul_normalisedProduct : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b), ∃ κ : ℕ → ℝ≥0, (∀ M, κ M ≠ 0) ∧ ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (β : F) (ψ : AddChar (AF F) ℂ) (ν : Measure (Fin 1 → Fin M → AF F ⊗[F] E)), 1 ≤ M → IsHermND σ J → β ≠ 0 → IsCharAF F ψ → IsStdX s σ J β ν → ∀ νX, IsXbetaMeasure F E σ M J ψ β νX ↔ νX = κ M • ν := by
  first | exact @GlobalTheory.GaugeEx.isXbetaMeasure_iff_smul_std | exact GlobalTheory.GaugeEx.isXbetaMeasure_iff_smul_std | (intros; apply GlobalTheory.GaugeEx.isXbetaMeasure_iff_smul_std <;> assumption)
