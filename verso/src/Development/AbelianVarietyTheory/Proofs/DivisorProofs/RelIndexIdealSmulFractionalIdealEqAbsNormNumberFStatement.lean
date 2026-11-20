import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexIdealSmulFractionalIdealEqAbsNormNumberF
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRelIndexIdealSmulFractionalIdealEqAbsNormNumberF.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.relIndex_ideal_smul_fractionalIdeal_eq_absNorm_numberField : ∀ (F : Type) [Field F] [NumberField F] (I : Submodule (𝓞 F) F) (p : Ideal (𝓞 F)), p ≠ ⊥ → I ≠ ⊥ → (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ y ∈ I, c • y ∈ (1 : Submodule (𝓞 F) F)) → (p • I).toAddSubgroup.relIndex I.toAddSubgroup = Ideal.absNorm p := by
  first | exact @GlobalTheory.FracIdealIndex.relIndex_smul_eq_absNorm | exact GlobalTheory.FracIdealIndex.relIndex_smul_eq_absNorm | (intros; apply GlobalTheory.FracIdealIndex.relIndex_smul_eq_absNorm <;> assumption)
