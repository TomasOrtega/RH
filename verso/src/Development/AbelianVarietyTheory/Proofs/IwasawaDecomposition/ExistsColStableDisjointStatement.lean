import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColStableDisjoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DefLift.exists_colStable_disjoint` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsColStableDisjoint.lean&line=87#L87)
-/
theorem _root_.GlobalTheory.T.exists_colStable_complement_of_lt : ∀ (ι : Type) [Fintype ι] (m n : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] (U W : Submodule ℂ (X →ₗ[ℂ] Pol ι m n)), (∀ Φ ∈ U, ∀ τ g, colSub m τ g ∘ₗ Φ ∈ U) → (∀ Φ ∈ W, ∀ τ g, colSub m τ g ∘ₗ Φ ∈ W) → U < W → ∃ U' : Submodule ℂ (X →ₗ[ℂ] Pol ι m n), U' ≠ ⊥ ∧ U' ≤ W ∧ U ⊓ U' = ⊥ ∧ ∀ Φ ∈ U', ∀ τ g, colSub m τ g ∘ₗ Φ ∈ U' := by
  first | exact @GlobalTheory.DefLift.exists_colStable_disjoint | exact GlobalTheory.DefLift.exists_colStable_disjoint | (intros; apply GlobalTheory.DefLift.exists_colStable_disjoint <;> assumption)
