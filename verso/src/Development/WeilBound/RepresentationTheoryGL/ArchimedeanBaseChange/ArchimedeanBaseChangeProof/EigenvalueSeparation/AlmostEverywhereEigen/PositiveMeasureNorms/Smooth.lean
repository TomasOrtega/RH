import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OneStepOf

open MeasureTheory
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P

/- English proof (translation)
Introduce `hconv X ι κ _ u Φ lam c₀ hu hinv hΦ hlam heq`. Use `set f : ι → X.G → ℂ := fun i x => (lam c₀)⁻¹ * ∑ j, ∫ y, Φ c₀ i j y * u j (x * y) ∂X.μ with hf`. Establish `hcont : ∀ i, Continuous (f i)` using `fun i => continuous_const.mul (continuous_finsetSum _ fun j _ => hconv X _ _ (hΦ c₀ i j) (hu j))`. Establish `hae : ∀ i, f i =ᵐ[X.μ] u i` using `fun i => (heq c₀ i).mono fun x hx => by`. Simplify using `only [hf]`.

Rewrite using `[hx, ← mul_assoc, inv_mul_cancel₀ hlam, one_mul]`. Use `⟨f, fun i => ⟨hcont i, hae i, fun γ hγ x => ?_⟩, fun c i x => ?_⟩` and prove the remaining obligations. Simplify using `only [hf]`. Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Use `congr 1`. Use function extensionality and compare the values at `y`. Rewrite using `[mul_assoc, hinv j γ hγ]`. Establish `hconv' : ∀ x, ∑ j, ∫ y, Φ c i j y * f j (x * y) ∂X.μ = ∑ j, ∫ y, Φ c i j y * u j (x * y) ∂X.μ`. Introduce `x`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `integral_congr_ae ?_` and prove the remaining obligations. Establish `h1` using `(measurePreserving_mul_left X.μ x).quasiMeasurePreserving.ae_eq_comp (hae j)`. Use `filter_upwards [h1] with y hy`. Simplify using `only [Function.comp] at hy`.

Rewrite using `[hy]`. Establish `hc1 : Continuous fun x => ∑ j, ∫ y, Φ c i j y * u j (x * y) ∂X.μ` using `continuous_finsetSum _ fun j _ => hconv X _ _ (hΦ c i j) (hu j)`. Establish `hc2 : Continuous fun x => lam c * f i x` using `continuous_const.mul (hcont i)`. Establish `hae2 : (fun x => ∑ j, ∫ y, Φ c i j y * u j (x * y) ∂X.μ) =ᵐ[X.μ] fun x => lam c * f i x` using `by filter_upwards [heq c i, hae i] with x h1 h2`. Rewrite using `[h1, h2]`.

Use `(Continuous.ae_eq_iff_eq X.μ hc1 hc2).1 hae2` as an intermediate fact. Rewrite using `[hconv' x]`. Conclude with `congrFun this x`.
-/
theorem smooth : ConvCont → Smooth := by
  classical
  intro hconv X ι κ _ u Φ lam c₀ hu hinv hΦ hlam heq
  set f : ι → X.G → ℂ := fun i x => (lam c₀)⁻¹ * ∑ j, ∫ y, Φ c₀ i j y * u j (x * y) ∂X.μ with hf
  have hcont : ∀ i, Continuous (f i) := fun i =>
    continuous_const.mul (continuous_finsetSum _ fun j _ => hconv X _ _ (hΦ c₀ i j) (hu j))
  have hae : ∀ i, f i =ᵐ[X.μ] u i := fun i => (heq c₀ i).mono fun x hx => by
    simp only [hf]
    rw [hx, ← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
  refine ⟨f, fun i => ⟨hcont i, hae i, fun γ hγ x => ?_⟩, fun c i x => ?_⟩
  · simp only [hf]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    funext y
    rw [mul_assoc, hinv j γ hγ]
  · have hconv' : ∀ x, ∑ j, ∫ y, Φ c i j y * f j (x * y) ∂X.μ = ∑ j, ∫ y, Φ c i j y * u j (x * y) ∂X.μ := by
      intro x
      refine Finset.sum_congr rfl fun j _ => ?_
      refine integral_congr_ae ?_
      have h1 := (measurePreserving_mul_left X.μ x).quasiMeasurePreserving.ae_eq_comp (hae j)
      filter_upwards [h1] with y hy
      simp only [Function.comp] at hy
      rw [hy]
    have hc1 : Continuous fun x => ∑ j, ∫ y, Φ c i j y * u j (x * y) ∂X.μ :=
      continuous_finsetSum _ fun j _ => hconv X _ _ (hΦ c i j) (hu j)
    have hc2 : Continuous fun x => lam c * f i x := continuous_const.mul (hcont i)
    have hae2 : (fun x => ∑ j, ∫ y, Φ c i j y * u j (x * y) ∂X.μ) =ᵐ[X.μ] fun x => lam c * f i x := by
      filter_upwards [heq c i, hae i] with x h1 h2
      rw [h1, h2]
    have := (Continuous.ae_eq_iff_eq X.μ hc1 hc2).1 hae2
    rw [hconv' x]
    exact congrFun this x

end PositivityTheory.Rg.BcB.E2.P
