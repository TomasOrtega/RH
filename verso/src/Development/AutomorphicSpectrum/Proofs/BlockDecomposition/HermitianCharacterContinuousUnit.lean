import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatSectionParabolicChange
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CoefWeight

/- English proof (translation)
Introduce `D n ψ hψ β`. Use `⟨?_, fun b => hψ.2.1 _⟩` and prove the remaining obligations. Take `⟨i1, i2, i3, i4, -, -⟩` from `lattice_Mx D n n`. Use `haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)`. Use `haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩`.

Establish `ht : Continuous (Algebra.trace (AF D.host.F) (AE D))` using `IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))`. Unfold `GlobalTheory.StdUnn.halfTr`. Conclude with `hψ.1.comp ((continuous_const.mul (ht.comp ((continuous_const.matrix_mul continuous_subtype_val).matrix_trace))).neg)`.
-/
theorem continuous_norm_coefChar : ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ β : PositivityTheory.GramSchwartzFunctions.HermE D n, Continuous (fun b : PositivityTheory.GramSchwartzFunctions.BC.hermA D n => ψ (-GlobalTheory.StdUnn.halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))) ∧ ∀ b : PositivityTheory.GramSchwartzFunctions.BC.hermA D n, ‖ψ (-GlobalTheory.StdUnn.halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))‖ = 1 := by
  intro D n ψ hψ β
  refine ⟨?_, fun b => hψ.2.1 _⟩
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D n n
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  unfold GlobalTheory.StdUnn.halfTr
  exact hψ.1.comp ((continuous_const.mul (ht.comp
    ((continuous_const.matrix_mul continuous_subtype_val).matrix_trace))).neg)

end GlobalTheory.CompanionTheory.CoefWeight
