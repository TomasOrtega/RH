import Mathlib

open Real

namespace GlobalTheory

open Filter Asymptotics in

/- English proof (translation)
Introduce `a b c C κ p ha hab hκ`. Establish `hb : 0 < b` using `lt_of_le_of_lt ha hab`. Establish `h1 : (fun x : ℝ => c * Real.log x) =o[atTop] fun x => x ^ b` using `(isLittleO_log_rpow_atTop hb).const_mul_left c`. Establish `h2 : (fun x : ℝ => C * x ^ a * Real.log x ^ p) =o[atTop] fun x => x ^ b`. Establish `hl : (fun x : ℝ => Real.log x ^ p) =o[atTop] fun x => x ^ (b - a)`.

Use `isLittleO_log_rpow_rpow_atTop (p : ℝ) (sub_pos.2 hab)` as an intermediate fact. Simplify `this` using `[Real.rpow_natCast]`. Establish `hm : (fun x : ℝ => x ^ a * Real.log x ^ p) =o[atTop] fun x => x ^ a * x ^ (b - a)` using `(isBigO_refl (fun x : ℝ => x ^ a) atTop).mul_isLittleO hl`. Establish `hm' : (fun x : ℝ => x ^ a * Real.log x ^ p) =o[atTop] fun x => x ^ b`. Use `hm.congr' (Eventually.of_forall fun _ => rfl) ?_` and prove the remaining obligations.

Use `filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx`. Rewrite using `[← Real.rpow_add hx]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Simplify `hm'.const_mul_left C` using `[mul_assoc]`.

Establish `h3 : (fun _ : ℝ => C) =o[atTop] fun x => x ^ b`. Rewrite using `[isLittleO_const_left]`. Use `right`. Conclude with `tendsto_norm_atTop_atTop.comp (tendsto_rpow_atTop hb)`. Establish `h` using `(h1.add h2).add h3`.

Take `⟨x0, hx0⟩` from `eventually_atTop.1 ((h.bound hκ).and (eventually_gt_atTop (0 : ℝ)))`. Use `⟨x0, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨hbd, hxpos⟩` from `hx0 x hx`. Establish `hpos : 0 < x ^ b` using `Real.rpow_pos_of_pos hxpos b`. Rewrite `hbd` using `[Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos]`.

Conclude with `(le_abs_self _).trans hbd`.
-/
theorem log_add_rpow_mul_log_pow_le_rpow :
    ∀ a b c C κ : ℝ, ∀ p : ℕ, 0 ≤ a → a < b → 0 < κ → ∃ x0 : ℝ, ∀ x ≥ x0,
      c * Real.log x + C * x ^ a * Real.log x ^ p + C ≤ κ * x ^ b := by
  intro a b c C κ p ha hab hκ
  have hb : 0 < b := lt_of_le_of_lt ha hab
  have h1 : (fun x : ℝ => c * Real.log x) =o[atTop] fun x => x ^ b :=
    (isLittleO_log_rpow_atTop hb).const_mul_left c
  have h2 : (fun x : ℝ => C * x ^ a * Real.log x ^ p) =o[atTop] fun x => x ^ b := by
    have hl : (fun x : ℝ => Real.log x ^ p) =o[atTop] fun x => x ^ (b - a) := by
      have := isLittleO_log_rpow_rpow_atTop (p : ℝ) (sub_pos.2 hab)
      simpa [Real.rpow_natCast] using this
    have hm : (fun x : ℝ => x ^ a * Real.log x ^ p) =o[atTop]
        fun x => x ^ a * x ^ (b - a) :=
      (isBigO_refl (fun x : ℝ => x ^ a) atTop).mul_isLittleO hl
    have hm' : (fun x : ℝ => x ^ a * Real.log x ^ p) =o[atTop] fun x => x ^ b := by
      refine hm.congr' (Eventually.of_forall fun _ => rfl) ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [← Real.rpow_add hx]
      congr 1
      ring
    simpa [mul_assoc] using hm'.const_mul_left C
  have h3 : (fun _ : ℝ => C) =o[atTop] fun x => x ^ b := by
    rw [isLittleO_const_left]
    right
    exact tendsto_norm_atTop_atTop.comp (tendsto_rpow_atTop hb)
  have h := (h1.add h2).add h3
  obtain ⟨x0, hx0⟩ := eventually_atTop.1 ((h.bound hκ).and (eventually_gt_atTop (0 : ℝ)))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨hbd, hxpos⟩ := hx0 x hx
  have hpos : 0 < x ^ b := Real.rpow_pos_of_pos hxpos b
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos] at hbd
  exact (le_abs_self _).trans hbd

end GlobalTheory
