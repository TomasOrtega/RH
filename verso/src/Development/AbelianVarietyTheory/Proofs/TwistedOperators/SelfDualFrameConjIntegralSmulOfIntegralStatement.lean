import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualFrameConjIntegralSmulOfIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FSelfDualFrameConjIntegralSmulOfIntegral.lean&line=71#L71)
-/
theorem _root_.GlobalTheory.T.selfDualFrame_conj_integral_smul_of_integral : ∀ {D : D7} (T : HSp D) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC T ΛT → IsFrame βT ΛT → ∀ (h : GL (Fin T.rank) (EAf D)), h ∈ UA D.sp.cm T.gram → ∀ (γ : GL (Fin T.rank) (EAf D)), γ = βT⁻¹ * h * βT → ∀ (a : AE D), IsIntM (toEAf D a • γ.1) → IsIntM (toEAf D a • (γ⁻¹ : GL (Fin T.rank) (EAf D)).1) → IsIntM (toEAf D (cA D a) • γ.1) ∧ IsIntM (toEAf D (cA D a) • (γ⁻¹ : GL (Fin T.rank) (EAf D)).1) := by
  first | exact @GlobalTheory.ConjIntegral.conj_smul_isIntM | exact GlobalTheory.ConjIntegral.conj_smul_isIntM | (intros; apply GlobalTheory.ConjIntegral.conj_smul_isIntM <;> assumption)
