import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LeTwoMulOfForallScale

open Matrix ComplexConjugate
open scoped ComplexOrder

namespace GlobalTheory.SpanCompare

/- English proof (translation)
Simplify using `only [HermFrame.form, star_sum, mulVec_sum, sum_dotProduct, dotProduct_sum, star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `only [Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_sum_sum {n ι : Type*} [Fintype n] (H : Matrix n n ℂ) (s : Finset ι) (c : ι → ℂ)
    (v : ι → n → ℂ) :
    HermFrame.form H (∑ i ∈ s, c i • v i) (∑ j ∈ s, c j • v j) =
      ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * HermFrame.form H (v i) (v j) := by
  simp only [HermFrame.form, star_sum, mulVec_sum, sum_dotProduct, dotProduct_sum, star_smul,
    mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.star_def]
  ring

/- English proof (translation)
Simplify using `only [form_sum_sum, h, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm (s := Finset.univ)]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.
-/
theorem form_comb {n ι Tau : Type*} [Fintype n] [Fintype Tau] {d : Tau → ℕ} (v : ι → n → ℂ)
    (G : Matrix n n ℂ) (A : ∀ τ, Matrix (Fin (d τ)) (Fin (d τ)) ℂ)
    (x : ∀ τ, ι → Fin (d τ) → ℂ)
    (h : ∀ i i', HermFrame.form G (v i) (v i') = ∑ τ, HermFrame.form (A τ) (x τ i) (x τ i'))
    (s : Finset ι) (c : ι → ℂ) :
    HermFrame.form G (∑ i ∈ s, c i • v i) (∑ j ∈ s, c j • v j) =
      ∑ τ, HermFrame.form (A τ) (∑ i ∈ s, c i • x τ i) (∑ j ∈ s, c j • x τ j) := by
  simp only [form_sum_sum, h, Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.univ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

/- English proof (translation)
Introduce `g ι Tau _ d v hv Gm Gm' hG hG' A A' x h h' K hK`. Use `PosSemidef.of_dotProduct_mulVec_nonneg ((hG'.smul (show star (K : ℂ) = K from Complex.conj_ofReal K)).sub hG) fun w => ?_` and prove the remaining obligations. Establish `hw : star w ∈ Submodule.span ℂ (Set.range v)` using `by rw [hv]; trivial`. Take `⟨c, hc⟩` from `Finsupp.mem_span_range_iff_exists_finsupp.1 hw`. Rewrite `hc` using `[Finsupp.sum]`.

Establish `e : ∀ {m : Type} [Fintype m] (M M' : Matrix m m ℂ) (z : m → ℂ), HermFrame.form ((K : ℂ) • M' - M) z z = K * HermFrame.form M' z z - HermFrame.form M z z` using `fun M M' z => by`. Simplify using `[HermFrame.form, sub_mulVec, smul_mulVec]`. Establish `h0 : star w ⬝ᵥ ((K : ℂ) • Gm' - Gm) *ᵥ w = HermFrame.form ((K : ℂ) • Gm' - Gm) (star w) (star w)` using `by simp [HermFrame.form]`. Rewrite using `[h0, e, ← hc, form_comb v Gm A x h, form_comb v Gm' A' x h', Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_nonneg fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[← e]`. Simplify `(hK τ).dotProduct_mulVec_nonneg (star (∑ i ∈ c.support, c i • x τ i))` using `only [HermFrame.form, star_star]`.
-/
theorem posSemidef_of_span : ∀ {g : ℕ} {ι Tau : Type} [Fintype Tau] {d : Tau → ℕ} (v : ι → Fin g → ℂ), Submodule.span ℂ (Set.range v) = ⊤ → ∀ (Gm Gm' : Matrix (Fin g) (Fin g) ℂ), Gm.IsHermitian → Gm'.IsHermitian → ∀ (A A' : ∀ τ, Matrix (Fin (d τ)) (Fin (d τ)) ℂ) (x : ∀ τ, ι → Fin (d τ) → ℂ), (∀ i i', HermFrame.form Gm (v i) (v i') = ∑ τ, HermFrame.form (A τ) (x τ i) (x τ i')) → (∀ i i', HermFrame.form Gm' (v i) (v i') = ∑ τ, HermFrame.form (A' τ) (x τ i) (x τ i')) → ∀ (K : ℝ), (∀ τ, (((K : ℂ) • A' τ) - A τ).PosSemidef) → (((K : ℂ) • Gm') - Gm).PosSemidef := by
  intro g ι Tau _ d v hv Gm Gm' hG hG' A A' x h h' K hK
  refine PosSemidef.of_dotProduct_mulVec_nonneg
    ((hG'.smul (show star (K : ℂ) = K from Complex.conj_ofReal K)).sub hG) fun w => ?_
  have hw : star w ∈ Submodule.span ℂ (Set.range v) := by rw [hv]; trivial
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hw
  rw [Finsupp.sum] at hc
  have e : ∀ {m : Type} [Fintype m] (M M' : Matrix m m ℂ) (z : m → ℂ),
      HermFrame.form ((K : ℂ) • M' - M) z z =
        K * HermFrame.form M' z z - HermFrame.form M z z := fun M M' z => by
    simp [HermFrame.form, sub_mulVec, smul_mulVec]
  have h0 : star w ⬝ᵥ ((K : ℂ) • Gm' - Gm) *ᵥ w =
      HermFrame.form ((K : ℂ) • Gm' - Gm) (star w) (star w) := by simp [HermFrame.form]
  rw [h0, e, ← hc, form_comb v Gm A x h, form_comb v Gm' A' x h', Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_nonneg fun τ _ => ?_
  rw [← e]
  simpa only [HermFrame.form, star_star] using
    (hK τ).dotProduct_mulVec_nonneg (star (∑ i ∈ c.support, c i • x τ i))

end GlobalTheory.SpanCompare
