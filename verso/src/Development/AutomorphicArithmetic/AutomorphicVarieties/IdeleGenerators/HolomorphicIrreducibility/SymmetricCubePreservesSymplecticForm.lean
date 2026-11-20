import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts

open Polynomial UpperTheory.V.Af Formalism.ConjugateSelfDual
open scoped Matrix

namespace UpperTheory.V.Sd

private noncomputable def s3F {S : Type} [CommRing S] (t d : S) : S[X] :=
  X ^ 4 + C (-(t ^ 3 - 2 * t * d)) * X ^ 3 + C (2 * d ^ 3 + (t ^ 3 - 3 * t * d) * d * t) * X ^ 2 +
    C (-(d ^ 3 * (t ^ 3 - 2 * t * d))) * X ^ 1 + C (d ^ 6) * X ^ 0

section Rel

variable {K : Type} [NormedField K] [IsUltrametricDist K]

private def Rl (x y : K) : Prop := ‖y‖ ≤ 1 ∧ ‖x - y‖ < 1

/- English proof (translation)
Use `IsUltrametricDist.norm_add_le_max (x - y) y` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Conclude with `this.trans (max_le h.2.le h.1)`.
-/
private theorem Rl.left {x y : K} (h : Rl x y) : ‖x‖ ≤ 1 := by
  have := IsUltrametricDist.norm_add_le_max (x - y) y
  rw [sub_add_cancel] at this
  exact this.trans (max_le h.2.le h.1)

/- English proof (translation)
Use `⟨(IsUltrametricDist.norm_add_le_max _ _).trans (max_le h.1 h'.1), ?_⟩` and prove the remaining obligations. Rewrite using `[add_sub_add_comm]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h.2 h'.2)`.
-/
private theorem Rl.add {x y z w : K} (h : Rl x y) (h' : Rl z w) : Rl (x + z) (y + w) := by
  refine ⟨(IsUltrametricDist.norm_add_le_max _ _).trans (max_le h.1 h'.1), ?_⟩
  rw [add_sub_add_comm]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h.2 h'.2)

omit [IsUltrametricDist K] in
/- English proof (translation)
Use `⟨by simpa using h.1, ?_⟩` and prove the remaining obligations. Rewrite using `[show -x - -y = -(x - y) by ring, norm_neg]`. Conclude with `h.2`.
-/
private theorem Rl.neg {x y : K} (h : Rl x y) : Rl (-x) (-y) := by
  refine ⟨by simpa using h.1, ?_⟩
  rw [show -x - -y = -(x - y) by ring, norm_neg]
  exact h.2

/- English proof (translation)
Simplify `h.add h'.neg` using `only [sub_eq_add_neg]`.
-/
private theorem Rl.sub {x y z w : K} (h : Rl x y) (h' : Rl z w) : Rl (x - z) (y - w) := by
  simpa only [sub_eq_add_neg] using h.add h'.neg

/- English proof (translation)
Use `⟨by rw [norm_mul]; exact mul_le_one₀ h.1 (norm_nonneg _) h'.1, ?_⟩` and prove the remaining obligations. Rewrite using `[show x * z - y * w = x * (z - w) + (x - y) * w by ring]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_right h.left (norm_nonneg _) h'.2`.

Rewrite using `[norm_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) h.2 h'.1`.
-/
private theorem Rl.mul {x y z w : K} (h : Rl x y) (h' : Rl z w) : Rl (x * z) (y * w) := by
  refine ⟨by rw [norm_mul]; exact mul_le_one₀ h.1 (norm_nonneg _) h'.1, ?_⟩
  rw [show x * z - y * w = x * (z - w) + (x - y) * w by ring]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
  · rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right h.left (norm_nonneg _) h'.2
  · rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) h.2 h'.1

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [Rl]`. Consider the case `succ n ih => rw [pow_succ, pow_succ]`. Conclude with `ih.mul h`.
-/
private theorem Rl.pow {x y : K} (h : Rl x y) (n : ℕ) : Rl (x ^ n) (y ^ n) := by
  induction n with
  | zero => simp [Rl]
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

/- English proof (translation)
Assemble the required witnesses or components as `⟨IsUltrametricDist.norm_natCast_le_one K n, by simp⟩`.
-/
private theorem Rl.nat (n : ℕ) : Rl (n : K) n := ⟨IsUltrametricDist.norm_natCast_le_one K n, by simp⟩

end Rel

end UpperTheory.V.Sd
