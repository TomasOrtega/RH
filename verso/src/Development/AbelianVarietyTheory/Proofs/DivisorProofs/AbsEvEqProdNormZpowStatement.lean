import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsEvEqProdNormZpow
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValAtOfUnder

noncomputable section

open scoped TensorProduct NNReal nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnrTate.absEv_eq_prod_absNorm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAbsEvEqProdNormZpow.lean&line=107#L107)
-/
theorem _root_.GlobalTheory.T.absEv_eq_prod_norm_zpow : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) (x : (Fv F v ⊗[F] E)ˣ), ((absEv F E v x : ℝ≥0) : ℝ) = ∏ w ∈ Formalism.L2.Host.aboveF (L := E) F v, (Ideal.absNorm w.asIdeal : ℝ) ^ (-GlobalTheory.UnrTate.ordAt v w x) := by
  first | exact @GlobalTheory.UnrTate.absEv_eq_prod_absNorm | exact GlobalTheory.UnrTate.absEv_eq_prod_absNorm | (intros; apply GlobalTheory.UnrTate.absEv_eq_prod_absNorm <;> assumption)
