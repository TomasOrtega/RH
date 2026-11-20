import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramIsHermitianL2EqDoubleSumStatement
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.HSAmp

/- English proof (translation)
Introduce `S Y _ ι _ _ μ v hF hinj`. Take `⟨hH, hl⟩` from `GlobalTheory.T.gram_isHermitian_l2_eq_double_sum S Y ι μ v hF`. Use `Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hH, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨-, h0, heq⟩` from `hl (fun i => (starRingEnd ℂ) (x i))`. Establish `hform : star x ⬝ᵥ (gram μ v *ᵥ x) = ((l2 μ v (fun i => (starRingEnd ℂ) (x i)) : ℝ) : ℂ)`.

Rewrite using `[heq]`. Simplify using `only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, Complex.star_def, Complex.conj_conj]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hform]`.

Establish `hne : l2 μ v (fun i => (starRingEnd ℂ) (x i)) ≠ 0`. Introduce `h`. Apply `hx` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Use `congrFun (hinj _ h) i` as an intermediate fact.

Simplify using `using this`. Conclude with `lt_of_le_of_ne h0 (Ne.symm hne)` after adjusting the coercions.
-/
theorem gram_posDef : ∀ (S : Type) (Y : S → Type) [∀ σ, MeasurableSpace (Y σ)] (ι : Type) [Fintype ι] [DecidableEq ι]
    (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ), IsFam μ v → (∀ c : ι → ℂ, l2 μ v c = 0 → c = 0) →
    (gram μ v).PosDef := by
  intro S Y _ ι _ _ μ v hF hinj
  obtain ⟨hH, hl⟩ := GlobalTheory.T.gram_isHermitian_l2_eq_double_sum S Y ι μ v hF
  refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hH, fun x hx => ?_⟩
  obtain ⟨-, h0, heq⟩ := hl (fun i => (starRingEnd ℂ) (x i))
  have hform : star x ⬝ᵥ (gram μ v *ᵥ x) = ((l2 μ v (fun i => (starRingEnd ℂ) (x i)) : ℝ) : ℂ) := by
    rw [heq]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, Complex.star_def, Complex.conj_conj]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hform]
  have hne : l2 μ v (fun i => (starRingEnd ℂ) (x i)) ≠ 0 := by
    intro h
    apply hx
    funext i
    have := congrFun (hinj _ h) i
    simpa using this
  exact_mod_cast lt_of_le_of_ne h0 (Ne.symm hne)

end GlobalTheory.HSAmp
