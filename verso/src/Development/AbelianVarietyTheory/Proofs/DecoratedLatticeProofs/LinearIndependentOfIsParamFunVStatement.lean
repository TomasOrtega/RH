import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearIndependentOfIsParamFunV
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FLinearIndependentOfIsParamFunV.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.linearIndependent_of_ne_zero_of_isParamFunV_of_separated : ∀ (D : D7) (V : HSp D) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (ι : Type) (f : ι → (GA D V → ℂ)) (B : ι → GlobalTheory.LFun.Fam D.host.E), (∀ i, f i ≠ 0) → (∀ i, GlobalTheory.LFun.IsParamFunV V Sb (f i) (B i)) → (∀ i i', i ≠ i' → ∃ w ∉ GlobalTheory.LFun.above D.host.E (Sb : Set (HeightOneSpectrum (𝓞 D.host.F))), B i w ≠ B i' w) → LinearIndependent ℂ f := by
  first | exact @GlobalTheory.ChainOnto.linearIndependent_of_isParamFunV | exact GlobalTheory.ChainOnto.linearIndependent_of_isParamFunV | (intros; apply GlobalTheory.ChainOnto.linearIndependent_of_isParamFunV <;> assumption)
