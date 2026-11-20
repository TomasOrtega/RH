import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryLocalComponentMemIntegralGLCofini
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernSum
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDefiniteUnitaryLocalComponentMemIntegralGLCofini.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.definiteUnitaryLocalComponent_mem_integralGL_cofinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (y : UA E n), ∀ᶠ w in cofinite, cLoc w y ∈ GlobalTheory.LFun.KGL w n := by
  first | exact @GlobalTheory.BCT.SuppFin.cLoc_mem_KGL_cofinite | exact GlobalTheory.BCT.SuppFin.cLoc_mem_KGL_cofinite | (intros; apply GlobalTheory.BCT.SuppFin.cLoc_mem_KGL_cofinite <;> assumption)
