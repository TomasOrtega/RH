import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Filter GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

variable {K : Type*} [DecidableEq K] {ι : K → Type*}

/- English proof (translation)
Rewrite using `[MvPolynomial.eval_eq]`. Use `Finset.sum_eq_zero fun d hd => ?_` and prove the remaining obligations. Establish `hw` using `hf (MvPolynomial.mem_support_iff.mp hd)`. Choose the witnesses or unpack the hypotheses as in `⟨v, hv, hvk⟩ : ∃ v ∈ d.support, v.1 = k := by`. Assume the negation of the conclusion as `hno`.

Use `push Not at hno`. Establish `h0 : (Finsupp.weight (blockWeight ι) d) k = 0`. Rewrite using `[Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]`. Use `Finset.sum_eq_zero fun v hv => ?_` and prove the remaining obligations. Simplify using `[blockWeight, hno v hv]`.

Use `hm k` as an intermediate fact. Rewrite `h0` using `[hw]`. Use linear arithmetic over natural numbers and integers. Use `mul_eq_zero_of_right _ (Finset.prod_eq_zero hv ?_)` and prove the remaining obligations. Take `⟨k', i⟩` from `v`.

Substitute `hvk` using the available equality. Rewrite using `[hx i]`. Conclude with `zero_pow (Finsupp.mem_support_iff.mp hv)`.
-/
theorem eval_eq_zero_of_block_zero {m : K → ℕ} (hm : ∀ k, 1 ≤ m k) {f : MvPolynomial (Σ k, ι k) ℂ}
    (hf : IsWeightedHomogeneous (blockWeight ι) f m) {x : (Σ k, ι k) → ℂ} {k : K}
    (hx : ∀ i, x ⟨k, i⟩ = 0) : eval x f = 0 := by
  classical
  rw [MvPolynomial.eval_eq]
  refine Finset.sum_eq_zero fun d hd => ?_
  have hw := hf (MvPolynomial.mem_support_iff.mp hd)
  obtain ⟨v, hv, hvk⟩ : ∃ v ∈ d.support, v.1 = k := by
    by_contra hno
    push Not at hno
    have h0 : (Finsupp.weight (blockWeight ι) d) k = 0 := by
      rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
      refine Finset.sum_eq_zero fun v hv => ?_
      simp [blockWeight, hno v hv]
    have := hm k
    rw [hw] at h0
    omega
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero hv ?_)
  obtain ⟨k', i⟩ := v
  subst hvk
  rw [hx i]
  exact zero_pow (Finsupp.mem_support_iff.mp hv)

variable [Fintype K] [∀ k, Fintype (ι k)]

/- English proof (translation)
Rewrite using `[← vanishingIdeal_zeroLocus_eq_radical (K := ℂ) I]`. Prove the components needed by the constructor for the conclusion. Conclude with `fun h => vanishingIdeal_anti_mono Set.inter_subset_left h`. Introduce `h x hx`. Distinguish the cases in `hU : ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0`.

Conclude with `h x ⟨hx, hU⟩`. Use `push Not at hU`. Take `⟨k, hk⟩` from `hU`. Conclude with `eval_eq_zero_of_block_zero hm hf hk`.
-/
theorem mem_radical_iff_offBlocks (I : Ideal (MvPolynomial (Σ k, ι k) ℂ)) {m : K → ℕ} (hm : ∀ k, 1 ≤ m k)
    {f : MvPolynomial (Σ k, ι k) ℂ} (hf : IsWeightedHomogeneous (blockWeight ι) f m) :
    f ∈ I.radical ↔ f ∈ vanishingIdeal ℂ (zeroLocus ℂ I ∩ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) := by
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := ℂ) I]
  constructor
  · exact fun h => vanishingIdeal_anti_mono Set.inter_subset_left h
  · intro h x hx
    by_cases hU : ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0
    · exact h x ⟨hx, hU⟩
    · push Not at hU
      obtain ⟨k, hk⟩ := hU
      exact eval_eq_zero_of_block_zero hm hf hk

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Use `set W := weightedHomogeneousSubmodule ℂ (blockWeight ι) m`. Set `f₁` to `(Ideal.Quotient.mkₐ ℂ P₁).toLinearMap ∘ₗ W.subtype`. Set `f₂` to `(Ideal.Quotient.mkₐ ℂ P₂).toLinearMap ∘ₗ W.subtype`. Establish `hr₁ : LinearMap.range f₁ = gradedPiece P₁ m`. Simplify using `only [f₁, LinearMap.range_comp, Submodule.range_subtype]`.

Both sides reduce to the same expression. Establish `hr₂ : LinearMap.range f₂ = gradedPiece P₂ m`. Simplify using `only [f₂, LinearMap.range_comp, Submodule.range_subtype]`. Both sides reduce to the same expression. Establish `hk : LinearMap.ker f₁ = LinearMap.ker f₂`.

Use extensionality with `⟨x, hx⟩`. Simplify using `only [LinearMap.mem_ker, f₁, f₂, LinearMap.comp_apply, Submodule.subtype_apply, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `h x hx`. Rewrite using `[← hr₁, ← hr₂]`. Conclude with `((f₁.quotKerEquivRange.symm.trans (Submodule.quotEquivOfEq _ _ hk)).trans f₂.quotKerEquivRange).finrank_eq`.
-/
theorem finrank_gradedPiece_eq {P₁ P₂ : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (m : K → ℕ)
    (h : ∀ f ∈ weightedHomogeneousSubmodule ℂ (blockWeight ι) m, f ∈ P₁ ↔ f ∈ P₂) :
    Module.finrank ℂ (gradedPiece P₁ m) = Module.finrank ℂ (gradedPiece P₂ m) := by
  set W := weightedHomogeneousSubmodule ℂ (blockWeight ι) m
  let f₁ := (Ideal.Quotient.mkₐ ℂ P₁).toLinearMap ∘ₗ W.subtype
  let f₂ := (Ideal.Quotient.mkₐ ℂ P₂).toLinearMap ∘ₗ W.subtype
  have hr₁ : LinearMap.range f₁ = gradedPiece P₁ m := by
    simp only [f₁, LinearMap.range_comp, Submodule.range_subtype]
    rfl
  have hr₂ : LinearMap.range f₂ = gradedPiece P₂ m := by
    simp only [f₂, LinearMap.range_comp, Submodule.range_subtype]
    rfl
  have hk : LinearMap.ker f₁ = LinearMap.ker f₂ := by
    ext ⟨x, hx⟩
    simp only [LinearMap.mem_ker, f₁, f₂, LinearMap.comp_apply, Submodule.subtype_apply,
      AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact h x hx
  rw [← hr₁, ← hr₂]
  exact ((f₁.quotKerEquivRange.symm.trans (Submodule.quotEquivOfEq _ _ hk)).trans
    f₂.quotKerEquivRange).finrank_eq

/- English proof (translation)
Unfold `hilbFn`. Establish `h0 : ∀ k, 0 ≤ m k` using `fun k => le_trans zero_le_one (hm k)`. Rewrite using `[if_pos h0, if_pos h0]`. Use `congr 1`. Use `finrank_gradedPiece_eq _ fun f hf => mem_radical_iff_offBlocks I (m := fun k => (m k).toNat) (fun k => ?_) ?_` and prove the remaining obligations.

Use `hm k` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite `hf` using `[mem_weightedHomogeneousSubmodule]`. Then use the resulting hypothesis.
-/
theorem hilbFn_radical_eq_offBlocks (I : Ideal (MvPolynomial (Σ k, ι k) ℂ)) {m : K → ℤ} (hm : ∀ k, 1 ≤ m k) :
    hilbFn I.radical m = hilbFn (vanishingIdeal ℂ (zeroLocus ℂ I ∩ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0})) m := by
  unfold hilbFn
  have h0 : ∀ k, 0 ≤ m k := fun k => le_trans zero_le_one (hm k)
  rw [if_pos h0, if_pos h0]
  congr 1
  refine finrank_gradedPiece_eq _ fun f hf => mem_radical_iff_offBlocks I (m := fun k => (m k).toNat) (fun k => ?_) ?_
  · have := hm k
    omega
  · rwa [mem_weightedHomogeneousSubmodule] at hf

omit [DecidableEq K] [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact h`. Consider the case `cons b l ih`. Establish `ht : Tendsto (fun m : K → ℤ => m - b) atTop atTop`. Conclude with `(tendsto_atTop_add_const_right atTop (-b) tendsto_id).congr fun m => by simp [sub_eq_add_neg]`.

Use `filter_upwards [ih, ht.eventually ih] with m hm hmb`. Simplify using `only [List.foldr_cons, diffStep, hm, hmb]`.
-/
theorem foldr_diffStep_eventuallyEq {h₁ h₂ : (K → ℤ) → ℤ} (h : h₁ =ᶠ[atTop] h₂) (l : List (K → ℤ)) :
    l.foldr diffStep h₁ =ᶠ[atTop] l.foldr diffStep h₂ := by
  induction l with
  | nil => exact h
  | cons b l ih =>
    have ht : Tendsto (fun m : K → ℤ => m - b) atTop atTop := by
      exact (tendsto_atTop_add_const_right atTop (-b) tendsto_id).congr fun m => by simp [sub_eq_add_neg]
    filter_upwards [ih, ht.eventually ih] with m hm hmb
    simp only [List.foldr_cons, diffStep, hm, hmb]

omit [DecidableEq K] [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Unfold `eventualValue`. Establish `hiff : (∃ c, ∀ᶠ m in atTop, f m = c) ↔ ∃ c, ∀ᶠ m in atTop, g m = c` using `⟨fun ⟨c, hc⟩ => ⟨c, (h.and hc).mono fun _ hm => hm.1.symm.trans hm.2⟩, fun ⟨c, hc⟩ => ⟨c, (h.and hc).mono fun _ hm => hm.1.trans hm.2⟩⟩`. Distinguish the cases in `hf : ∃ c, ∀ᶠ m in atTop, f m = c`. Rewrite using `[dif_pos hf, dif_pos (hiff.mp hf)]`. Take `⟨m, hm⟩` from `(hf.choose_spec.and ((hiff.mp hf).choose_spec.and h)).exists`.

Conclude with `hm.1.symm.trans (hm.2.2.trans hm.2.1)`. Rewrite using `[dif_neg hf, dif_neg (mt hiff.mpr hf)]`.
-/
theorem eventualValue_congr {f g : (K → ℤ) → ℤ} (h : f =ᶠ[atTop] g) : eventualValue f = eventualValue g := by
  unfold eventualValue
  have hiff : (∃ c, ∀ᶠ m in atTop, f m = c) ↔ ∃ c, ∀ᶠ m in atTop, g m = c :=
    ⟨fun ⟨c, hc⟩ => ⟨c, (h.and hc).mono fun _ hm => hm.1.symm.trans hm.2⟩,
      fun ⟨c, hc⟩ => ⟨c, (h.and hc).mono fun _ hm => hm.1.trans hm.2⟩⟩
  by_cases hf : ∃ c, ∀ᶠ m in atTop, f m = c
  · rw [dif_pos hf, dif_pos (hiff.mp hf)]
    obtain ⟨m, hm⟩ := (hf.choose_spec.and ((hiff.mp hf).choose_spec.and h)).exists
    exact hm.1.symm.trans (hm.2.2.trans hm.2.1)
  · rw [dif_neg hf, dif_neg (mt hiff.mpr hf)]

/- English proof (translation)
Unfold `intNum mixedDiff`. Use `eventualValue_congr (foldr_diffStep_eventuallyEq ?_ _)` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop (1 : K → ℤ)] with m hm`. Conclude with `hilbFn_radical_eq_offBlocks I fun k => hm k`.
-/
theorem intNum_radical_eq_offBlocks (I : Ideal (MvPolynomial (Σ k, ι k) ℂ)) {n : ℕ} (bs : Fin n → K → ℤ) :
    intNum ℂ I.radical bs =
      intNum ℂ (vanishingIdeal ℂ (zeroLocus ℂ I ∩ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0})) bs := by
  unfold intNum mixedDiff
  refine eventualValue_congr (foldr_diffStep_eventuallyEq ?_ _)
  filter_upwards [eventually_ge_atTop (1 : K → ℤ)] with m hm
  exact hilbFn_radical_eq_offBlocks I fun k => hm k

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
