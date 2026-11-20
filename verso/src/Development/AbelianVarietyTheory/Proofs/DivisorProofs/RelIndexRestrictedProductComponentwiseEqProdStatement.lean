import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexRestrictedProductComponentwiseEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwOrbEqFinsumTwTerm
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRelIndexRestrictedProductComponentwiseEqProd.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.relIndex_restrictedProduct_componentwise_eq_prod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (C H : ∀ v, Subgroup (Y v)), (∀ v, (H v).relIndex (C v) ≠ 0) → (∀ᶠ v in cofinite, C v ≤ H v) → (⨅ v, (H v).comap (pf v)).relIndex (⨅ v, (C v).comap (pf v)) = ∏ᶠ v, (H v).relIndex (C v) := by
  first | exact @GlobalTheory.RelIdxRestr.relIndex_iInf_comap | exact GlobalTheory.RelIdxRestr.relIndex_iInf_comap | (intros; apply GlobalTheory.RelIdxRestr.relIndex_iInf_comap <;> assumption)
