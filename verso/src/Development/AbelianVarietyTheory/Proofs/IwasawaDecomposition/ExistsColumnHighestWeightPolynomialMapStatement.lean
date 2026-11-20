import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnHighestWeightPolynomialMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DefLift.exists_colHighest` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsColumnHighestWeightPolynomialMap.lean&line=108#L108)
-/
theorem _root_.GlobalTheory.T.exists_column_highest_weight_polynomial_map : ∀ (ι : Type) [Fintype ι] (m n : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] (U : Submodule ℂ (X →ₗ[ℂ] Pol ι m n)), U ≠ ⊥ → (∀ Φ ∈ U, ∀ τ g, colSub m τ g ∘ₗ Φ ∈ U) → ∃ Φ ∈ U, Φ ≠ 0 ∧ (∀ τ k l, k < l → colLie m τ k l ∘ₗ Φ = 0) ∧ ∃ μ : ι → Fin n → ℤ, ∀ τ k, colLie m τ k k ∘ₗ Φ = (μ τ k : ℂ) • Φ := by
  first | exact @GlobalTheory.DefLift.exists_colHighest | exact GlobalTheory.DefLift.exists_colHighest | (intros; apply GlobalTheory.DefLift.exists_colHighest <;> assumption)
