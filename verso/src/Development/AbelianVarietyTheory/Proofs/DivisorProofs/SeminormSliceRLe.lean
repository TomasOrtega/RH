import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTemperateGrowthElim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClmSupBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTranslationSeminormBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowNormMulSeminormSliceRLe

open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff

noncomputable section
namespace GlobalTheory.SliceOpCont

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/- English proof (translation)
Use `(pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_` and prove the remaining obligations. Consider the cases of `i with`. Consider the case `inl i => simpa [padL] using norm_le_pi_norm h i`. Consider the case `inr j => simp [padL]`.
-/
theorem norm_padL_le {κ κ' : Type} [Fintype κ] [Fintype κ'] (h : κ → V) :
    ‖(padL (κ' := κ') h : κ ⊕ κ' → V)‖ ≤ ‖h‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  cases i with
  | inl i => simpa [padL] using norm_le_pi_norm h i
  | inr j => simp [padL]

/- English proof (translation)
Use extensionality with `y`. Establish `he : (Sum.elim x₀ y : κ ⊕ κ' → V) + padL (x - x₀) = Sum.elim x y`. Use function extensionality and compare the values at `i`. Consider the cases of `i with`. Consider the case `inl i => simp [padL]`.

Consider the case `inr j => simp [padL]`. Simplify using `[SchwartzMap.compSubConstCLM_apply, he]`.
-/
theorem sliceR_sub_eq {κ κ' : Type} [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ)
    (x x₀ : κ → V) :
    sliceR f x - sliceR f x₀
      = sliceR (SchwartzMap.compSubConstCLM ℂ (-(padL (κ' := κ') (x - x₀))) f - f) x₀ := by
  ext y
  have he : (Sum.elim x₀ y : κ ⊕ κ' → V) + padL (x - x₀) = Sum.elim x y := by
    funext i
    cases i with
    | inl i => simp [padL]
    | inr j => simp [padL]
  simp [SchwartzMap.compSubConstCLM_apply, he]

/- English proof (translation)
Use `GlobalTheory.SliceWeight.pow_norm_mul_seminorm_sliceR_le V κ κ' g 0 k n x` as an intermediate fact. Simplify using `using this`.
-/
theorem seminorm_sliceR_le (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {κ κ' : Type} [Fintype κ] [Fintype κ'] (g : SchwartzMap (κ ⊕ κ' → V) ℂ) (x : κ → V) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (sliceR g x) ≤ SchwartzMap.seminorm ℂ k n g := by
  have := GlobalTheory.SliceWeight.pow_norm_mul_seminorm_sliceR_le V κ κ' g 0 k n x
  simpa using this

/- English proof (translation)
Use `continuous_iff_continuousAt.2 fun x₀ => ?_` and prove the remaining obligations. Use `((schwartz_withSeminorms ℂ (κ' → V) ℂ).tendsto_nhds _ _).2 fun i ε hε => ?_` and prove the remaining obligations. Take `⟨k, n⟩` from `i`. Use `set C : ℝ := 2 ^ k * ((Finset.Iic (k, n + 1)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) f`. Establish `hcont : Continuous (fun x : κ → V => ‖x - x₀‖ * (1 + ‖x - x₀‖) ^ k * C)` using `by fun_prop`.

Establish `h0 : ‖x₀ - x₀‖ * (1 + ‖x₀ - x₀‖) ^ k * C = 0` using `by simp`. Establish `hev : ∀ᶠ x in nhds x₀, ‖x - x₀‖ * (1 + ‖x - x₀‖) ^ k * C < ε`. Use `hcont.continuousAt (x := x₀)` as an intermediate fact. Rewrite `this` using `[ContinuousAt, h0]`. Conclude with `this (Iio_mem_nhds hε)`.

Use `filter_upwards [hev] with x hx`. Use `lt_of_le_of_lt ?_ hx` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `SchwartzMap.seminorm ℂ k n (sliceR f x - sliceR f x₀) ≤ _`. Rewrite using `[sliceR_sub_eq]`. Use `(seminorm_sliceR_le V _ x₀ k n).trans ?_` and prove the remaining obligations.

Use `(GlobalTheory.SchwartzTranslateLip.seminorm_translate_sub_le k n k n le_rfl le_rfl _ f).trans ?_` and prove the remaining obligations. Establish `hC : 0 ≤ C` using `by positivity`. Establish `hp` using `norm_padL_le (κ' := κ') (x - x₀)`. Use `gcongr`.
-/
theorem continuous_sliceR (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {κ κ' : Type} [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ) :
    Continuous (fun x : κ → V => sliceR f x) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  refine ((schwartz_withSeminorms ℂ (κ' → V) ℂ).tendsto_nhds _ _).2 fun i ε hε => ?_
  obtain ⟨k, n⟩ := i
  set C : ℝ := 2 ^ k * ((Finset.Iic (k, n + 1)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) f
  have hcont : Continuous (fun x : κ → V => ‖x - x₀‖ * (1 + ‖x - x₀‖) ^ k * C) := by fun_prop
  have h0 : ‖x₀ - x₀‖ * (1 + ‖x₀ - x₀‖) ^ k * C = 0 := by simp
  have hev : ∀ᶠ x in nhds x₀, ‖x - x₀‖ * (1 + ‖x - x₀‖) ^ k * C < ε := by
    have := hcont.continuousAt (x := x₀)
    rw [ContinuousAt, h0] at this
    exact this (Iio_mem_nhds hε)
  filter_upwards [hev] with x hx
  refine lt_of_le_of_lt ?_ hx
  change SchwartzMap.seminorm ℂ k n (sliceR f x - sliceR f x₀) ≤ _
  rw [sliceR_sub_eq]
  refine (seminorm_sliceR_le V _ x₀ k n).trans ?_
  refine (GlobalTheory.SchwartzTranslateLip.seminorm_translate_sub_le k n k n le_rfl le_rfl _ f).trans ?_
  have hC : 0 ≤ C := by positivity
  have hp := norm_padL_le (κ' := κ') (x - x₀)
  gcongr

end GlobalTheory.SliceOpCont

open GlobalTheory.SliceOpCont in
/- English proof (translation)
Establish `hinl : Continuous (fun s : κ ⊕ κ₁' → V => s ∘ Sum.inl)` using `by fun_prop`. Establish `hinr : Continuous (fun s : κ ⊕ κ₁' → V => s ∘ Sum.inr)` using `by fun_prop`. Establish `hG : Continuous (fun s : κ ⊕ κ₁' → V => SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ₁' → V) ℂ (P (sliceR f (s ∘ Sum.inl))))` using `(SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ₁' → V) ℂ).continuous.comp (P.continuous.comp ((continuous_sliceR V f).comp hinl))`. Establish `hq : qOp P f = fun s => (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ₁' → V) ℂ (P (sliceR f (s ∘ Sum.inl)))) (s ∘ Sum.inr)`. Use function extensionality and compare the values at `s`.

Both sides reduce to the same expression. Rewrite using `[hq]`. Conclude with `continuous_eval.comp (hG.prodMk hinr)`.
-/
theorem GlobalTheory.SliceOp.continuous_qOp (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (κ κ' κ₁' : Type) [Fintype κ] [Fintype κ'] [Fintype κ₁']
    (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ) :
    Continuous (qOp P f) := by
  have hinl : Continuous (fun s : κ ⊕ κ₁' → V => s ∘ Sum.inl) := by fun_prop
  have hinr : Continuous (fun s : κ ⊕ κ₁' → V => s ∘ Sum.inr) := by fun_prop
  have hG : Continuous (fun s : κ ⊕ κ₁' → V =>
      SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ₁' → V) ℂ (P (sliceR f (s ∘ Sum.inl)))) :=
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ₁' → V) ℂ).continuous.comp
      (P.continuous.comp ((continuous_sliceR V f).comp hinl))
  have hq : qOp P f = fun s => (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ₁' → V) ℂ
      (P (sliceR f (s ∘ Sum.inl)))) (s ∘ Sum.inr) := by
    funext s; rfl
  rw [hq]
  exact continuous_eval.comp (hG.prodMk hinr)
