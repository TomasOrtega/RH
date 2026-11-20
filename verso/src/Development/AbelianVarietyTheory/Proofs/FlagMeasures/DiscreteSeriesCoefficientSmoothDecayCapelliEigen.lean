import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqUnitNormalizationLe
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliKFiniteCoefficient
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselPeriodAdjointPairStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliDiscreteSeriesInfChar
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliEigenvalueKFiniteDiscreteSeriesCoeff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CentredCapelliOperatorFormsAgree
open BranchingSupport BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory

/- English proof (translation)
Introduce `hH k r ε mu h R Wp Wq _ _ _ _ _ _ f hDS hgap hok hf`. Use `FiniteDimensional.complete ℂ Wp` as an intermediate fact. Use `FiniteDimensional.complete ℂ Wq` as an intermediate fact. Establish `hsm : PI.KFinSmooth` using `hH.1.1.2.2.1`. Establish `hDG : R.IsDG ε mu` using `⟨hDS.1, hDS.2, h, hgap, hok⟩`.

Take `⟨s, hs⟩` from `(GlobalTheory.isCoef_of_translate_smul_exists hsm k r ε mu R Wp Wq (fun _ => 0) (fun _ => 0) hDS).1 f hf`. Take `⟨h1, h2⟩` from `Gp91.GlobalTheory.T.smooth_and_inCC_of_isCoef_of_gap hH.1 k r ε mu h R Wp Wq (fun _ => 0) (fun _ => 0) f s hDG hgap hok hs`. Use `⟨h1, h2, fun y g hg => ?_⟩` and prove the remaining obligations. Establish `hE` using `GlobalTheory.CapelliEigenvalue.capEig hsm GlobalTheory.capelliDiscreteSeriesInfChar k r ε mu R.H R.σ Wp Wq hDS.1 hDS.2 f hf (y : ℂ) g hg`. Rewrite using `[(GlobalTheory.ThA.centredCapelli_forms_agree k r _ (y : ℂ) f).1, hE]`.

Simplify using `only [Formalism.QuantumDeterminants.capP, Complex.ofReal_prod, Complex.ofReal_add]`.
-/
theorem eigDec_of_isKFinCoefT_gap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (f : B.Mat k r → (Wq →L[ℂ] Wp)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → (haveI := FiniteDimensional.complete ℂ Wp; PI.CapelliEig.IsKFinCoefT (k := k) (r := r) R.σ f) → EigDec f (aOf r h - 1) mu := by
  intro hH k r ε mu h R Wp Wq _ _ _ _ _ _ f hDS hgap hok hf
  have := FiniteDimensional.complete ℂ Wp
  have := FiniteDimensional.complete ℂ Wq
  have hsm : PI.KFinSmooth := hH.1.1.2.2.1
  have hDG : R.IsDG ε mu := ⟨hDS.1, hDS.2, h, hgap, hok⟩
  obtain ⟨s, hs⟩ := (GlobalTheory.isCoef_of_translate_smul_exists hsm k r ε mu R Wp Wq (fun _ => 0) (fun _ => 0) hDS).1 f hf
  obtain ⟨h1, h2⟩ := Gp91.GlobalTheory.T.smooth_and_inCC_of_isCoef_of_gap hH.1 k r ε mu h R Wp Wq (fun _ => 0) (fun _ => 0) f s hDG hgap hok hs
  refine ⟨h1, h2, fun y g hg => ?_⟩
  have hE := GlobalTheory.CapelliEigenvalue.capEig hsm GlobalTheory.capelliDiscreteSeriesInfChar k r ε mu R.H R.σ Wp Wq hDS.1 hDS.2 f hf (y : ℂ) g hg
  rw [(GlobalTheory.ThA.centredCapelli_forms_agree k r _ (y : ℂ) f).1, hE]
  simp only [Formalism.QuantumDeterminants.capP, Complex.ofReal_prod, Complex.ofReal_add]

end GlobalTheory

end
