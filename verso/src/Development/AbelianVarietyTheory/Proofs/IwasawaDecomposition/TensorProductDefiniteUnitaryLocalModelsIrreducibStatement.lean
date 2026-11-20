import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorProductDefiniteUnitaryLocalModelsIrreducib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FTensorProductDefiniteUnitaryLocalModelsIrreducib.lean&line=122#L122)
-/
theorem _root_.GlobalTheory.T.tensorProduct_definiteUnitary_localModels_irreducible : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), (∀ τ, FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤ ∧ ∀ U : Submodule ℂ (M.H τ), (∀ u : Matrix.unitaryGroup (Fin V.rank) ℂ, ∀ x ∈ U, M.σ τ u x ∈ U) → U = ⊥ ∨ U = ⊤) → AllPlus M → FiniteDimensional ℂ (SmT M) ∧ Function.Injective (inclT M) ∧ ∃ π, IsTensAct M π ∧ IrrFam π := by
  first | exact @GlobalTheory.DefLift.tensor_irreducible | exact GlobalTheory.DefLift.tensor_irreducible | (intros; apply GlobalTheory.DefLift.tensor_irreducible <;> assumption)
