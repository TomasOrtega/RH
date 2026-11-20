import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
import GroundTheory.AutomorphicForms.FourierWhittaker.PartialCoeffDiagonalBlockGLEqVecCoeff

noncomputable section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc

/- English proof (translation)
Establish `hF : Continuous (Function.uncurry fun (x : AdelicGLn.AdelicGL K n) (y : archGroup K n) => (β y : ℂ) * f (x * infEmb K n y))`. Use `(Complex.continuous_ofReal.comp (hβ.cont.comp continuous_snd)).mul (hf.comp ?_)` and prove the remaining obligations. Conclude with `continuous_fst.mul (continuous_infEmb.comp continuous_snd)`. Establish `h` using `continuous_parametric_integral_of_continuous (μ := ν) hF hβ.cpt.isCompact`. Use `h.congr fun x => ?_` and prove the remaining obligations.

Use `setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_` and prove the remaining obligations. Establish `: β y = 0` using `image_eq_zero_of_notMem_tsupport hy`. Simplify using `[this]`.
-/
theorem continuous_sm_uFam {K : Type} [Field K] [NumberField K] {n : ℕ}
    [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n))
    [ν.IsHaarMeasure] {β : archGroup K n → ℝ} (hβ : Ker ν β) {f : AdelicGLn.AdelicGL K n → ℂ}
    (hf : Continuous f) : Continuous (sm ν β f) := by
  have hF : Continuous (Function.uncurry fun (x : AdelicGLn.AdelicGL K n) (y : archGroup K n) =>
      (β y : ℂ) * f (x * infEmb K n y)) := by
    refine (Complex.continuous_ofReal.comp (hβ.cont.comp continuous_snd)).mul (hf.comp ?_)
    exact continuous_fst.mul (continuous_infEmb.comp continuous_snd)
  have h := continuous_parametric_integral_of_continuous (μ := ν) hF hβ.cpt.isCompact
  refine h.congr fun x => ?_
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
  have : β y = 0 := image_eq_zero_of_notMem_tsupport hy
  simp [this]

/- English proof (translation)
Introduce `K _ _ n _ _ ν _ β ι f hβ hf`. Use `⟨fun i => continuous_sm_uFam ν hβ (hf.cont i), fun i γ x => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [sm, mul_assoc]`. Use `integral_congr_ae (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[hf.left i γ (x * infEmb K n y)]`. Take `⟨U, hU, hlev⟩` from `hf.level`. Use `⟨U, hU, fun i g u => ?_⟩` and prove the remaining obligations. Simplify using `only [sm]`. Use `integral_congr_ae (Eventually.of_forall fun y => ?_)` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[mul_assoc g, ← infEmb_mul_finEmb_comm, ← mul_assoc, hlev i (g * infEmb K n y) u]`.
-/
theorem uFam_sm : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (archGroup K n)]
    [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ)
    (ι : Type) (f : ι → AdelicGLn.AdelicGL K n → ℂ), Ker ν β → UFam f → UFam (fun i => sm ν β (f i)) := by
  intro K _ _ n _ _ ν _ β ι f hβ hf
  refine ⟨fun i => continuous_sm_uFam ν hβ (hf.cont i), fun i γ x => ?_, ?_⟩
  · simp only [sm, mul_assoc]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [hf.left i γ (x * infEmb K n y)]
  · obtain ⟨U, hU, hlev⟩ := hf.level
    refine ⟨U, hU, fun i g u => ?_⟩
    simp only [sm]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [mul_assoc g, ← infEmb_mul_finEmb_comm, ← mul_assoc, hlev i (g * infEmb K n y) u]

end GlobalTheory.CompanionTheory.Conc

end
