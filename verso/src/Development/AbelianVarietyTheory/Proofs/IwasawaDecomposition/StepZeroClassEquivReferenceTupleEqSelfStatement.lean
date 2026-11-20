import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassEquivReferenceTupleEqSelf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.Col2.TC.MuZeroCls.stepZeroClassEquiv_referenceTuple_eq_self` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FStepZeroClassEquivReferenceTupleEqSelf.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.eCls0_mu0_eq_self : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (c : (I.stp u I.mu0 0).Cl), I.eCls0 l u I.mu0 c = c := by
  first | exact @GlobalTheory.Mem.Col2.TC.MuZeroCls.stepZeroClassEquiv_referenceTuple_eq_self | exact GlobalTheory.Mem.Col2.TC.MuZeroCls.stepZeroClassEquiv_referenceTuple_eq_self | (intros; apply GlobalTheory.Mem.Col2.TC.MuZeroCls.stepZeroClassEquiv_referenceTuple_eq_self <;> assumption)
