import Mathlib
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `l _ d ι w γ hw hn c hc`. Assume the negation of the conclusion as `hne`. Take `⟨a1, ha1⟩` from `Function.ne_iff.mp hne`. Take `⟨a₀, -, ha₀⟩` from `Finset.exists_max_image Finset.univ (fun a => ‖c a‖) ⟨a1, Finset.mem_univ _⟩`. Establish `hc0 : c a₀ ≠ 0`.

Introduce `h`. Use `ha₀ a1 (Finset.mem_univ _)` as an intermediate fact. Simplify using `only [h, norm_zero] at this`. Conclude with `ha1 (norm_le_zero_iff.mp this)`. Use `set c' : Fin d → ℚ_[l] := fun a => c a / c a₀ with hc'`.

Establish `hc'le : ∀ a, ‖c' a‖ ≤ 1`. Introduce `a`. Simplify using `only [hc', norm_div]`. Conclude with `div_le_one_of_le₀ (ha₀ a (Finset.mem_univ _)) (norm_nonneg _)`. Establish `hc'a₀ : c' a₀ = 1` using `div_self hc0`.

Establish `hsum' : ∀ i, ∑ a, algebraMap ℚ_[l] ℂ_[l] (c' a) * w a i = 0`. Introduce `i`. Establish `: ∑ a, algebraMap ℚ_[l] ℂ_[l] (c' a) * w a i = algebraMap ℚ_[l] ℂ_[l] (c a₀)⁻¹ * ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * w a i`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Simplify using `only [hc', div_eq_mul_inv, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, hc i, mul_zero]`. Set `e : Fin d → ℤ_[l]` to `fun a => ⟨c' a, hc'le a⟩`. Set `n : Fin d → ℕ` to `fun a => (e a).appr 1`.

Establish `hen : ∀ a, ‖e a - (n a : ℤ_[l])‖ ≤ (l : ℝ)⁻¹`. Introduce `a`. Establish `h` using `(PadicInt.norm_le_pow_iff_mem_span_pow _ 1).mpr (by simpa using PadicInt.appr_spec 1 (e a))`. Simplify using `using h`. Establish `hlC : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹`.

Rewrite using `[← map_natCast (algebraMap ℚ_[l] ℂ_[l]) l, norm_algebraMap', Padic.norm_p]`. Establish `hsmall : ∀ i, ‖∑ a, (n a : ℂ_[l]) * w a i‖ ≤ ‖(l : ℂ_[l])‖ * γ i`. Introduce `i`. Establish `heq : ∑ a, (n a : ℂ_[l]) * w a i = ∑ a, ((n a : ℂ_[l]) - algebraMap ℚ_[l] ℂ_[l] (c' a)) * w a i`. Simplify using `only [sub_mul, Finset.sum_sub_distrib, hsum' i, sub_zero]`.

Rewrite using `[heq, hlC]`. Apply `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg` to reduce the goal to its premises. Conclude with `mul_nonneg (by positivity) ((norm_nonneg _).trans (hw a₀ i))`. Introduce `a _`. Rewrite using `[norm_mul]`.

Use `mul_le_mul ?_ (hw a i) (norm_nonneg _) (by positivity)` and prove the remaining obligations. Establish `: (n a : ℂ_[l]) - algebraMap ℚ_[l] ℂ_[l] (c' a) = algebraMap ℚ_[l] ℂ_[l] (-(((e a - (n a : ℤ_[l]) : ℤ_[l]) : ℚ_[l])))`. Establish `hea : ((e a : ℤ_[l]) : ℚ_[l]) = c' a` using `rfl`. Rewrite using `[map_neg, PadicInt.coe_sub, PadicInt.coe_natCast, hea, map_sub, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, norm_algebraMap', norm_neg, PadicInt.padic_norm_e_of_padicInt]`. Conclude with `hen a`. Establish `hdiv` using `hn n hsmall a₀`. Establish `hlt : ‖(n a₀ : ℤ_[l])‖ < 1`. Rewrite using `[PadicInt.norm_lt_one_iff_dvd]`.

Take `⟨k, hk⟩` from `hdiv`. Conclude with `⟨k, by rw [hk]; push_cast; ring⟩`. Establish `he1 : ‖e a₀‖ = 1` using `by show ‖c' a₀‖ = 1`. Rewrite using `[hc'a₀, norm_one]`. Establish `hlinv : (l : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)`.

Establish `: ‖e a₀‖ ≤ max ‖e a₀ - (n a₀ : ℤ_[l])‖ ‖(n a₀ : ℤ_[l])‖`. Simplify using `using IsUltrametricDist.norm_add_le_max (e a₀ - (n a₀ : ℤ_[l])) (n a₀ : ℤ_[l])`. Rewrite `this` using `[he1]`. Use `this.trans_lt (max_lt ((hen a₀).trans_lt hlinv) hlt)` as an intermediate fact. Conclude with `lt_irrefl _ this`.
-/
theorem indep_over_Ql_of_indep_mod_l : ∀ (l : ℕ) [Fact l.Prime] (d : ℕ) (ι : Type) (w : Fin d → ι → ℂ_[l]) (γ : ι → ℝ), (∀ a i, ‖w a i‖ ≤ γ i) → (∀ n : Fin d → ℕ, (∀ i, ‖∑ a, (n a : ℂ_[l]) * w a i‖ ≤ ‖(l : ℂ_[l])‖ * γ i) → ∀ a, l ∣ n a) → ∀ c : Fin d → ℚ_[l], (∀ i, ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * w a i = 0) → c = 0 := by
  intro l _ d ι w γ hw hn c hc
  by_contra hne
  obtain ⟨a1, ha1⟩ := Function.ne_iff.mp hne
  obtain ⟨a₀, -, ha₀⟩ := Finset.exists_max_image Finset.univ (fun a => ‖c a‖) ⟨a1, Finset.mem_univ _⟩
  have hc0 : c a₀ ≠ 0 := by
    intro h
    have := ha₀ a1 (Finset.mem_univ _)
    simp only [h, norm_zero] at this
    exact ha1 (norm_le_zero_iff.mp this)
  set c' : Fin d → ℚ_[l] := fun a => c a / c a₀ with hc'
  have hc'le : ∀ a, ‖c' a‖ ≤ 1 := by
    intro a
    simp only [hc', norm_div]
    exact div_le_one_of_le₀ (ha₀ a (Finset.mem_univ _)) (norm_nonneg _)
  have hc'a₀ : c' a₀ = 1 := div_self hc0
  have hsum' : ∀ i, ∑ a, algebraMap ℚ_[l] ℂ_[l] (c' a) * w a i = 0 := by
    intro i
    have : ∑ a, algebraMap ℚ_[l] ℂ_[l] (c' a) * w a i
        = algebraMap ℚ_[l] ℂ_[l] (c a₀)⁻¹ * ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * w a i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [hc', div_eq_mul_inv, map_mul]
      ring
    rw [this, hc i, mul_zero]
  let e : Fin d → ℤ_[l] := fun a => ⟨c' a, hc'le a⟩
  let n : Fin d → ℕ := fun a => (e a).appr 1
  have hen : ∀ a, ‖e a - (n a : ℤ_[l])‖ ≤ (l : ℝ)⁻¹ := by
    intro a
    have h := (PadicInt.norm_le_pow_iff_mem_span_pow _ 1).mpr (by simpa using PadicInt.appr_spec 1 (e a))
    simpa using h
  have hlC : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[l] ℂ_[l]) l, norm_algebraMap', Padic.norm_p]
  have hsmall : ∀ i, ‖∑ a, (n a : ℂ_[l]) * w a i‖ ≤ ‖(l : ℂ_[l])‖ * γ i := by
    intro i
    have heq : ∑ a, (n a : ℂ_[l]) * w a i
        = ∑ a, ((n a : ℂ_[l]) - algebraMap ℚ_[l] ℂ_[l] (c' a)) * w a i := by
      simp only [sub_mul, Finset.sum_sub_distrib, hsum' i, sub_zero]
    rw [heq, hlC]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    · exact mul_nonneg (by positivity) ((norm_nonneg _).trans (hw a₀ i))
    · intro a _
      rw [norm_mul]
      refine mul_le_mul ?_ (hw a i) (norm_nonneg _) (by positivity)
      have : (n a : ℂ_[l]) - algebraMap ℚ_[l] ℂ_[l] (c' a)
          = algebraMap ℚ_[l] ℂ_[l] (-(((e a - (n a : ℤ_[l]) : ℤ_[l]) : ℚ_[l]))) := by
        have hea : ((e a : ℤ_[l]) : ℚ_[l]) = c' a := rfl
        rw [map_neg, PadicInt.coe_sub, PadicInt.coe_natCast, hea, map_sub, map_natCast]
        ring
      rw [this, norm_algebraMap', norm_neg, PadicInt.padic_norm_e_of_padicInt]
      exact hen a
  have hdiv := hn n hsmall a₀
  have hlt : ‖(n a₀ : ℤ_[l])‖ < 1 := by
    rw [PadicInt.norm_lt_one_iff_dvd]
    obtain ⟨k, hk⟩ := hdiv
    exact ⟨k, by rw [hk]; push_cast; ring⟩
  have he1 : ‖e a₀‖ = 1 := by
    show ‖c' a₀‖ = 1
    rw [hc'a₀, norm_one]
  have hlinv : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have : ‖e a₀‖ ≤ max ‖e a₀ - (n a₀ : ℤ_[l])‖ ‖(n a₀ : ℤ_[l])‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (e a₀ - (n a₀ : ℤ_[l])) (n a₀ : ℤ_[l])
  rw [he1] at this
  have := this.trans_lt (max_lt ((hen a₀).trans_lt hlinv) hlt)
  exact lt_irrefl _ this

end GlobalTheory
