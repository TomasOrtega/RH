import Formalism.EllipticTorsion.EllipticTorsionProofs.LegendreInvariant

namespace Formalism.ELL

namespace DeuringModel

open Polynomial

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/- English proof (translation)
Rewrite using `[IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]`.
-/
lemma norm_add_eq_left {x y : K} (h : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

/- English proof (translation)
The claim follows from `IsUltrametricDist.norm_natCast_le_one K n`.
-/
lemma norm_nat_le_one (n : ℕ) : ‖(n : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K n

/- English proof (translation)
Set `P : K[X]` to `X ^ 3 * (X ^ 3 - C 24) ^ 3 - C j * (X ^ 3 - C 27)`. Establish `hdeg : P.degree = 12`. Simplify using `only [P]`. Use `compute_degree!`. Take `⟨a, ha⟩` from `IsAlgClosed.exists_root P (by rw [hdeg]; norm_num)`.

Use `⟨a, ?_⟩` and prove the remaining obligations. Simplify using `only [P, IsRoot, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at ha`. Conclude with `sub_eq_zero.mp ha`.
-/
lemma exists_root_deuring [IsAlgClosed K] (j : K) :
    ∃ a : K, a ^ 3 * (a ^ 3 - 24) ^ 3 = j * (a ^ 3 - 27) := by
  let P : K[X] := X ^ 3 * (X ^ 3 - C 24) ^ 3 - C j * (X ^ 3 - C 27)
  have hdeg : P.degree = 12 := by
    simp only [P]
    compute_degree!
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root P (by rw [hdeg]; norm_num)
  refine ⟨a, ?_⟩
  simp only [P, IsRoot, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at ha
  exact sub_eq_zero.mp ha

end DeuringModel

open DeuringModel in
/- English proof (translation)
Introduce `K _ _ _ h3 j hj`. Take `⟨a, ha⟩` from `exists_root_deuring j`. Establish `hc4 : (deuring a).c₄ = a * (a ^ 3 - 24)`. Simplify using `[deuring, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hΔ : (deuring a).Δ = a ^ 3 - 27`. Simplify using `[deuring, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]`. Expand and normalize the polynomial expressions, which then agree. Establish `h27 : ‖(27 : K)‖ = 1`. Establish `e : (27 : K) = 3 ^ 3` using `by norm_num`.

Rewrite using `[e, norm_pow, h3, one_pow]`. Establish `ha1 : ‖a‖ ≤ 1`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `hA3 : ‖a ^ 3‖ = ‖a‖ ^ 3` using `norm_pow a 3`.

Establish `hbig : 1 < ‖a‖ ^ 3` using `one_lt_pow₀ hlt (by norm_num)`. Establish `h24 : ‖(24 : K)‖ ≤ 1` using `by exact_mod_cast norm_nat_le_one (K := K) 24`. Establish `hn1 : ‖a ^ 3 - 24‖ = ‖a‖ ^ 3`. Rewrite using `[sub_eq_add_neg, norm_add_eq_left (by rw [norm_neg, hA3]; linarith), hA3]`. Establish `hn2 : ‖a ^ 3 - 27‖ = ‖a‖ ^ 3`.

Rewrite using `[sub_eq_add_neg, norm_add_eq_left (by rw [norm_neg, hA3]; linarith), hA3]`. Establish `hL : ‖a ^ 3 * (a ^ 3 - 24) ^ 3‖ = ‖a‖ ^ 12`. Rewrite using `[norm_mul, hA3, norm_pow, hn1]`. Expand and normalize the polynomial expressions, which then agree. Establish `hR : ‖j * (a ^ 3 - 27)‖ ≤ ‖a‖ ^ 3`.

Rewrite using `[norm_mul, hn2]`. Combine the equalities or inequalities in the displayed calculation. Rewrite `hL` using `[ha]`. Establish `hlt2 : ‖a‖ ^ 3 < ‖a‖ ^ 12` using `pow_lt_pow_right₀ hlt (by norm_num)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hA3le : ‖a ^ 3‖ ≤ 1`. Rewrite using `[norm_pow]`. Conclude with `pow_le_one₀ (norm_nonneg _) ha1`. Establish `hΔle : ‖a ^ 3 - 27‖ ≤ 1`. Rewrite using `[sub_eq_add_neg]`.

Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hA3le (by rw [norm_neg, h27]))`. Establish `hΔ1 : ‖a ^ 3 - 27‖ = 1`. Assume the negation of the conclusion as `hne`. Establish `hlt : ‖a ^ 3 - 27‖ < 1` using `lt_of_le_of_ne hΔle hne`. Establish `e1 : a ^ 3 = 27 + (a ^ 3 - 27)` using `by ring`.

Establish `hA : ‖a ^ 3‖ = 1`. Rewrite using `[e1, norm_add_eq_left (by rw [h27]; exact hlt), h27]`. Establish `e2 : a ^ 3 - 24 = 3 + (a ^ 3 - 27)` using `by ring`. Establish `hB : ‖a ^ 3 - 24‖ = 1`. Rewrite using `[e2, norm_add_eq_left (by rw [h3]; exact hlt), h3]`.

Establish `hL : ‖a ^ 3 * (a ^ 3 - 24) ^ 3‖ = 1`. Rewrite using `[norm_mul, hA, norm_pow, hB]`. Evaluate the numerical expressions. Rewrite `hL` using `[ha, norm_mul]`. Establish `h4 : ‖j‖ * ‖a ^ 3 - 27‖ < 1`.

Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨a, ha1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hc4, hΔ, ← ha]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hΔ, hΔ1]`.
-/
theorem deuring_model : ModelDeuring := by
  intro K _ _ _ h3 j hj
  obtain ⟨a, ha⟩ := exists_root_deuring j
  have hc4 : (deuring a).c₄ = a * (a ^ 3 - 24) := by
    simp [deuring, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    ring
  have hΔ : (deuring a).Δ = a ^ 3 - 27 := by
    simp [deuring, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  have h27 : ‖(27 : K)‖ = 1 := by
    have e : (27 : K) = 3 ^ 3 := by norm_num
    rw [e, norm_pow, h3, one_pow]
  have ha1 : ‖a‖ ≤ 1 := by
    by_contra hlt
    push_neg at hlt
    have hA3 : ‖a ^ 3‖ = ‖a‖ ^ 3 := norm_pow a 3
    have hbig : 1 < ‖a‖ ^ 3 := one_lt_pow₀ hlt (by norm_num)
    have h24 : ‖(24 : K)‖ ≤ 1 := by exact_mod_cast norm_nat_le_one (K := K) 24
    have hn1 : ‖a ^ 3 - 24‖ = ‖a‖ ^ 3 := by
      rw [sub_eq_add_neg, norm_add_eq_left (by rw [norm_neg, hA3]; linarith), hA3]
    have hn2 : ‖a ^ 3 - 27‖ = ‖a‖ ^ 3 := by
      rw [sub_eq_add_neg, norm_add_eq_left (by rw [norm_neg, hA3]; linarith), hA3]
    have hL : ‖a ^ 3 * (a ^ 3 - 24) ^ 3‖ = ‖a‖ ^ 12 := by
      rw [norm_mul, hA3, norm_pow, hn1]
      ring
    have hR : ‖j * (a ^ 3 - 27)‖ ≤ ‖a‖ ^ 3 := by
      rw [norm_mul, hn2]
      calc ‖j‖ * ‖a‖ ^ 3 ≤ 1 * ‖a‖ ^ 3 := by gcongr
        _ = ‖a‖ ^ 3 := one_mul _
    rw [ha] at hL
    have hlt2 : ‖a‖ ^ 3 < ‖a‖ ^ 12 := pow_lt_pow_right₀ hlt (by norm_num)
    linarith
  have hA3le : ‖a ^ 3‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) ha1
  have hΔle : ‖a ^ 3 - 27‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hA3le (by rw [norm_neg, h27]))
  have hΔ1 : ‖a ^ 3 - 27‖ = 1 := by
    by_contra hne
    have hlt : ‖a ^ 3 - 27‖ < 1 := lt_of_le_of_ne hΔle hne
    have e1 : a ^ 3 = 27 + (a ^ 3 - 27) := by ring
    have hA : ‖a ^ 3‖ = 1 := by
      rw [e1, norm_add_eq_left (by rw [h27]; exact hlt), h27]
    have e2 : a ^ 3 - 24 = 3 + (a ^ 3 - 27) := by ring
    have hB : ‖a ^ 3 - 24‖ = 1 := by
      rw [e2, norm_add_eq_left (by rw [h3]; exact hlt), h3]
    have hL : ‖a ^ 3 * (a ^ 3 - 24) ^ 3‖ = 1 := by
      rw [norm_mul, hA, norm_pow, hB]
      norm_num
    rw [ha, norm_mul] at hL
    have h4 : ‖j‖ * ‖a ^ 3 - 27‖ < 1 := by
      calc ‖j‖ * ‖a ^ 3 - 27‖ ≤ 1 * ‖a ^ 3 - 27‖ := by gcongr
        _ < 1 := by rw [one_mul]; exact hlt
    linarith
  refine ⟨a, ha1, ?_, ?_⟩
  · rw [hc4, hΔ, ← ha]
    ring
  · rw [hΔ, hΔ1]

end Formalism.ELL
