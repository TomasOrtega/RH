import Mathlib

namespace GlobalTheory.RootProductCoeffBound

open Polynomial

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on generalizing a with`. Consider the case `empty`. Break down `a with _ | k` into its components or cases. Simplify using the standard rewrite rules. Simplify using `[Polynomial.coeff_one]`.

Consider the case `insert y S hy ih`. Establish `ihS : ∀ b, ‖(∏ x ∈ S, (X - C x)).coeff b‖ ≤ θ ^ (S.card - b)` using `fun b => ih (fun x hx => hS x (Finset.mem_insert_of_mem hx)) b`. Establish `hyθ : ‖y‖ ≤ θ` using `hS y (Finset.mem_insert_self y S)`. Rewrite using `[Finset.prod_insert hy, Finset.card_insert_of_notMem hy]`. Use `set P := ∏ x ∈ S, (X - C x) with hP`.

Rewrite using `[sub_mul, coeff_sub, coeff_C_mul]`. Establish `hyb : ∀ b, ‖y * P.coeff b‖ ≤ θ ^ (S.card + 1 - (b + 1)) * θ`. Introduce `b`. Rewrite using `[norm_mul, mul_comm]`. Use `mul_le_mul ?_ hyθ (norm_nonneg _) (pow_nonneg h0 _)` and prove the remaining obligations.

Simplify using `using ihS b`. Break down `a with _ | k` into its components or cases. Rewrite using `[coeff_X_mul_zero, zero_sub, norm_neg]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[coeff_X_mul]`.

Rewrite using `[sub_eq_add_neg]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Simplify using `using ihS k`. Rewrite using `[norm_neg]`. Combine the equalities or inequalities in the displayed calculation.

Use `hyb (k + 1)` as an intermediate fact. Simplify using `using this`. Use `_ = θ ^ (S.card - (k + 1) + 1) := by rw [pow_succ]`. Use `_ ≤ θ ^ (S.card + 1 - (k + 1)) := by`. Apply `pow_le_pow_of_le_one h0 h1` to reduce the goal to its premises.

Use linear arithmetic over natural numbers and integers.
-/
theorem coeff_prod_X_sub_C_norm_le {K : Type} [NormedField K] [IsUltrametricDist K]
    (θ : ℝ) (h0 : (0 : ℝ) ≤ θ) (h1 : θ ≤ (1 : ℝ)) (S : Finset K)
    (hS : ∀ x ∈ S, ‖x‖ ≤ θ) (a : ℕ) :
    ‖Polynomial.coeff (∏ x ∈ S, (Polynomial.X - (Polynomial.C : K → Polynomial K) x)) a‖
      ≤ θ ^ (Finset.card S - a) := by
  classical
  induction S using Finset.induction_on generalizing a with
  | empty =>
    rcases a with _ | k
    · simp
    · simp [Polynomial.coeff_one]
  | insert y S hy ih =>
    have ihS : ∀ b, ‖(∏ x ∈ S, (X - C x)).coeff b‖ ≤ θ ^ (S.card - b) :=
      fun b => ih (fun x hx => hS x (Finset.mem_insert_of_mem hx)) b
    have hyθ : ‖y‖ ≤ θ := hS y (Finset.mem_insert_self y S)
    rw [Finset.prod_insert hy, Finset.card_insert_of_notMem hy]
    set P := ∏ x ∈ S, (X - C x) with hP
    rw [sub_mul, coeff_sub, coeff_C_mul]
    have hyb : ∀ b, ‖y * P.coeff b‖ ≤ θ ^ (S.card + 1 - (b + 1)) * θ := by
      intro b
      rw [norm_mul, mul_comm]
      refine mul_le_mul ?_ hyθ (norm_nonneg _) (pow_nonneg h0 _)
      simpa using ihS b
    rcases a with _ | k
    · rw [coeff_X_mul_zero, zero_sub, norm_neg]
      calc ‖y * P.coeff 0‖ ≤ θ ^ (S.card + 1 - (0 + 1)) * θ := hyb 0
        _ = θ ^ (S.card + 1 - 0) := by simp [pow_succ]
    · rw [coeff_X_mul]
      rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · simpa using ihS k
      · rw [norm_neg]
        calc ‖y * P.coeff (k + 1)‖ ≤ θ ^ (S.card - (k + 1)) * θ := by
              have := hyb (k + 1); simpa using this
          _ = θ ^ (S.card - (k + 1) + 1) := by rw [pow_succ]
          _ ≤ θ ^ (S.card + 1 - (k + 1)) := by
              apply pow_le_pow_of_le_one h0 h1
              omega

/- English proof (translation)
Introduce `θ h0 h1 S hS a` and use `coeff_prod_X_sub_C_norm_le θ h0 h1 S hS a`.
-/
theorem main : ∀ {K : Type} [inst : NormedField K] [IsUltrametricDist K] (θ : ℝ), (0 : ℝ) ≤ θ → θ ≤ (1 : ℝ) → ∀ (S : Finset K), (∀ x ∈ S, ‖x‖ ≤ θ) → ∀ (a : ℕ), ‖Polynomial.coeff (∏ x ∈ S, (Polynomial.X - (Polynomial.C : K → Polynomial K) x)) a‖ ≤ θ ^ (Finset.card S - a) :=
  fun θ h0 h1 S hS a => coeff_prod_X_sub_C_norm_le θ h0 h1 S hS a

end GlobalTheory.RootProductCoeffBound
