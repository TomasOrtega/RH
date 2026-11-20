import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTheRecOfIsRec
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolarizedGaloisRepNarrow2
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GenericUnlinkedGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenericUnlinkedGLOutright
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProductSpehSatake
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedRepTemperedParameter
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GalOfCusp GlobalTheory.TheRec
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
open scoped TensorProduct

namespace GlobalTheory.SegLen

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ Y, φ y ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 hc)`. Introduce `h0`.

Use `congrArg ((TensorProduct.rid ℂ X).toLinearMap ∘ₗ LinearMap.lTensor X φ) h0` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul, map_zero] at this`. Conclude with `hx ((smul_eq_zero.1 this).resolve_left hφ)`.
-/
theorem tmul_ne_zero_of_ne {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] {x : X} {y : Y}
    (hx : x ≠ 0) (hy : y ≠ 0) : x ⊗ₜ[ℂ] y ≠ 0 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ Y, φ y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 hc)
  intro h0
  have := congrArg ((TensorProduct.rid ℂ X).toLinearMap ∘ₗ LinearMap.lTensor X φ) h0
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul,
    map_zero] at this
  exact hx ((smul_eq_zero.1 this).resolve_left hφ)

/- English proof (translation)
Establish `h1 : WD.lpSp h 1 = WD.lpOfChar h (WeilDeligne.unrChar h (qPow w 0)) (isSmooth_unrChar h _)`. Use `WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `[WDRep.spEig]`. Use function extensionality and compare the values at `i`.

Simplify using `[shiftEnd_apply]`. Rewrite using `[h1, lpChar_lpOfChar]`. Conclude with `WD.lpTw_zero x`.
-/
theorem lpChar_lpSp_one' (x : WD h) : x.lpChar (WD.lpSp h 1) = x := by
  have h1 : WD.lpSp h 1 = WD.lpOfChar h (WeilDeligne.unrChar h (qPow w 0)) (isSmooth_unrChar h _) := by
    refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => ?_⟩
    · funext i
      simp [WDRep.spEig]
    · funext i
      simp [shiftEnd_apply]
  rw [h1, lpChar_lpOfChar]
  exact WD.lpTw_zero x

/- English proof (translation)
Establish `h0` using `TemperedRec.monodromy_zero_of_irreducible_weilDeligne E Ω A w h x hx`. Take `⟨m, b, rfl, hirr⟩` from `hx`. Establish `: Nontrivial (Fin m → ℂ)` using `Model.nontrivial_of_isIrreducible hirr`. Take `⟨v, hv⟩` from `exists_ne (0 : Fin m → ℂ)`. Rewrite `h0` using `[WD.monodromyZero_ofWeilDeligneRepClass_iff]`.

Rewrite using `[WD.lpSp, WD.lpChar_mk, WD.monodromyZero_ofWeilDeligneRepClass_iff, WDRep.tensor_N, h0, WDRep.sp_N, LinearMap.rTensor_zero, zero_add]`. Introduce `hN`. Choose the witnesses or unpack the hypotheses as in `⟨u, hu⟩ : ∃ u, shiftEnd n u ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Conclude with `shiftEnd_ne_zero hn (LinearMap.ext hc)`. Use `LinearMap.congr_fun hN (v ⊗ₜ u)` as an intermediate fact. Rewrite `this` using `[LinearMap.lTensor_tmul, LinearMap.zero_apply]`. Conclude with `tmul_ne_zero_of_ne hv hu this`.
-/
theorem not_mono0_lpChar_lpSp {x : WD h} (hx : IsIrrWD x) {n : ℕ} (hn : 2 ≤ n) :
    ¬ (x.lpChar (WD.lpSp h n)).mono0 := by
  have h0 := TemperedRec.monodromy_zero_of_irreducible_weilDeligne E Ω A w h x hx
  obtain ⟨m, b, rfl, hirr⟩ := hx
  have : Nontrivial (Fin m → ℂ) := Model.nontrivial_of_isIrreducible hirr
  obtain ⟨v, hv⟩ := exists_ne (0 : Fin m → ℂ)
  rw [WD.monodromyZero_ofWeilDeligneRepClass_iff] at h0
  rw [WD.lpSp, WD.lpChar_mk, WD.monodromyZero_ofWeilDeligneRepClass_iff, WDRep.tensor_N, h0, WDRep.sp_N, LinearMap.rTensor_zero, zero_add]
  intro hN
  obtain ⟨u, hu⟩ : ∃ u, shiftEnd n u ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact shiftEnd_ne_zero hn (LinearMap.ext hc)
  have := LinearMap.congr_fun hN (v ⊗ₜ u)
  rw [LinearMap.lTensor_tmul, LinearMap.zero_apply] at this
  exact tmul_ne_zero_of_ne hv hu this

end GlobalTheory.SegLen
