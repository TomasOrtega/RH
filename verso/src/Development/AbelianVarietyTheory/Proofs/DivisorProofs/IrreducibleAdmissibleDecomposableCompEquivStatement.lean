import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleAdmissibleDecomposableCompEquiv
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CuspMult.isDecomp_comp_equiv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIrreducibleAdmissibleDecomposableCompEquiv.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.irreducibleAdmissibleDecomposable_comp_equiv : ∀ (H H' : Type) [Group H] [TopologicalSpace H] [Group H'] [TopologicalSpace H'] (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H' X) (C : Submodule ℂ X) (Φ : H ≃ₜ* H'), IsDecomp ρ C → IsDecomp (ρ.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ H X) C := by
  first | exact @GlobalTheory.CuspMult.isDecomp_comp_equiv | exact GlobalTheory.CuspMult.isDecomp_comp_equiv | (intros; apply GlobalTheory.CuspMult.isDecomp_comp_equiv <;> assumption)
