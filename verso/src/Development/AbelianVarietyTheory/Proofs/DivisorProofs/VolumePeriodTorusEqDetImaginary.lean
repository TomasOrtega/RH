import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe

noncomputable section
namespace GlobalTheory.PerVol

def reIm {g : ℕ} (z : Fin g → ℂ) : Fl g := Sum.elim (fun i => (z i).im) (fun i => (z i).re)

/- English proof (translation)
Establish `h1 : MeasurePreserving (fun (z : Fin g → ℂ) (i : Fin g) => Complex.measurableEquivRealProd (z i)) volume volume` using `volume_preserving_pi (fun _ : Fin g => Complex.volume_preserving_equiv_real_prod)`. Establish `h2` using `volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin g)`. Establish `h3 : MeasurePreserving (Prod.swap : (Fin g → ℝ) × (Fin g → ℝ) → _) volume volume` using `Measure.measurePreserving_swap`. Establish `h4` using `volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin g ⊕ Fin g => ℝ)`. Use `h4.comp (h3.comp (h2.comp h1))` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `z i`. Apply the tactic sequence `cases i <;> rfl`.
-/
theorem reIm_mp {g : ℕ} : MeasurePreserving (reIm (g := g)) volume volume := by
  have h1 : MeasurePreserving (fun (z : Fin g → ℂ) (i : Fin g) => Complex.measurableEquivRealProd (z i))
      volume volume :=
    volume_preserving_pi (fun _ : Fin g => Complex.volume_preserving_equiv_real_prod)
  have h2 := volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin g)
  have h3 : MeasurePreserving (Prod.swap : (Fin g → ℝ) × (Fin g → ℝ) → _) volume volume :=
    Measure.measurePreserving_swap
  have h4 := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin g ⊕ Fin g => ℝ)
  have := h4.comp (h3.comp (h2.comp h1))
  convert this using 1
  funext z i
  cases i <;> rfl

/- English proof (translation)
Introduce `z w h`. Use function extensionality and compare the values at `i`. Apply `Complex.ext` to reduce the goal to its premises. Conclude with `congrFun h (Sum.inr i)`. Conclude with `congrFun h (Sum.inl i)`.
-/
theorem reIm_injective {g : ℕ} : Function.Injective (reIm (g := g)) := by
  intro z w h
  funext i
  apply Complex.ext
  · exact congrFun h (Sum.inr i)
  · exact congrFun h (Sum.inl i)

def perMat {g : ℕ} (τ0 : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ :=
  Matrix.fromBlocks (τ0.map Complex.im)ᵀ 0 (τ0.map Complex.re)ᵀ 1

/- English proof (translation)
Use function extensionality and compare the values at `i`. Consider the cases of `i with`. Consider the case `inl i`. Simplify using `[reIm, per, perMat, Matrix.vecMul, dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Matrix.fromBlocks, Complex.im_sum, Complex.re_sum, mul_comm]`. Consider the case `inr i`.

Simplify using `[reIm, per, perMat, Matrix.vecMul, dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Matrix.fromBlocks, Complex.im_sum, Complex.re_sum, mul_comm, Matrix.one_apply]`.
-/
theorem reIm_per {g : ℕ} (τ0 : Matrix (Fin g) (Fin g) ℂ) (x : Fl g) :
    reIm (per τ0 x) = Matrix.toLin' (perMat τ0) x := by
  funext i
  cases i with
  | inl i =>
    simp [reIm, per, perMat, Matrix.vecMul, dotProduct, Matrix.mulVec, Fintype.sum_sum_type,
      Matrix.fromBlocks, Complex.im_sum, Complex.re_sum, mul_comm]
  | inr i =>
    simp [reIm, per, perMat, Matrix.vecMul, dotProduct, Matrix.mulVec, Fintype.sum_sum_type,
      Matrix.fromBlocks, Complex.im_sum, Complex.re_sum, mul_comm, Matrix.one_apply]

/- English proof (translation)
Simplify using `[perMat, Matrix.det_fromBlocks_zero₁₂]`.
-/
theorem det_perMat {g : ℕ} (τ0 : Matrix (Fin g) (Fin g) ℂ) :
    (perMat τ0).det = (τ0.map Complex.im).det := by
  simp [perMat, Matrix.det_fromBlocks_zero₁₂]

end GlobalTheory.PerVol

namespace GlobalTheory.PerVol

/- English proof (translation)
Use `set L : Fl g →ₗ[ℝ] Fl g := Matrix.toLin' (perMat τ0)`. Establish `hset : per τ0 '' Set.Icc (0 : Fl g) 1 = reIm ⁻¹' (L '' Set.Icc (0 : Fl g) 1)`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`.

Conclude with `⟨x, hx, (reIm_per τ0 x).symm⟩`. Introduce and unpack `⟨x, hx, hxz⟩`. Use `⟨x, hx, reIm_injective ?_⟩` and prove the remaining obligations. Rewrite using `[reIm_per]`. Conclude with `hxz`.

Establish `hmeas : MeasurableSet (L '' Set.Icc (0 : Fl g) 1)` using `(isCompact_Icc.image (LinearMap.continuous_of_finiteDimensional L)).measurableSet`. Rewrite using `[hset, reIm_mp.measure_preimage hmeas.nullMeasurableSet, MeasureTheory.Measure.addHaar_image_linearMap, Real.volume_Icc_pi]`. Simplify using `[L, LinearMap.det_toLin', det_perMat]`.
-/
theorem volume_per_image_Icc {g : ℕ} (τ0 : Matrix (Fin g) (Fin g) ℂ) :
    volume (per τ0 '' Set.Icc (0 : Fl g) 1) = ENNReal.ofReal |(τ0.map Complex.im).det| := by
  set L : Fl g →ₗ[ℝ] Fl g := Matrix.toLin' (perMat τ0)
  have hset : per τ0 '' Set.Icc (0 : Fl g) 1 = reIm ⁻¹' (L '' Set.Icc (0 : Fl g) 1) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (reIm_per τ0 x).symm⟩
    · rintro ⟨x, hx, hxz⟩
      refine ⟨x, hx, reIm_injective ?_⟩
      rw [reIm_per]
      exact hxz
  have hmeas : MeasurableSet (L '' Set.Icc (0 : Fl g) 1) :=
    (isCompact_Icc.image (LinearMap.continuous_of_finiteDimensional L)).measurableSet
  rw [hset, reIm_mp.measure_preimage hmeas.nullMeasurableSet,
    MeasureTheory.Measure.addHaar_image_linearMap, Real.volume_Icc_pi]
  simp [L, LinearMap.det_toLin', det_perMat]

end GlobalTheory.PerVol
