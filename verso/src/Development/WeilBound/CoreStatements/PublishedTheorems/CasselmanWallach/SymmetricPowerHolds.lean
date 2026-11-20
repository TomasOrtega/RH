import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace identity_filtration_of_scalar

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro x y`. Simplify using the standard rewrite rules. Consider the case `succ k ih`.

Introduce `x y`. Rewrite using `[pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hP]`. Use `congr 1`. Rewrite using `[← Module.End.mul_apply, ← Module.End.mul_apply, (Commute.self_pow P k).eq]`.
-/
theorem symm_pow {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (P : Module.End ℂ W)
    (hP : ∀ x y, inner ℂ (P x) y = inner ℂ x (P y)) :
    ∀ k : ℕ, ∀ x y, inner ℂ ((P ^ k) x) y = inner ℂ x ((P ^ k) y) := by
  intro k
  induction k with
  | zero => intro x y; simp
  | succ k ih =>
    intro x y
    rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hP]
    congr 1
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, (Commute.self_pow P k).eq]

end identity_filtration_of_scalar

/- English proof (translation)
Introduce `W _ _ P hP x hx h0 j`. Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih`. Establish `hsym` using `identity_filtration_of_scalar.symm_pow P hP (2 ^ j)`.

Establish `key : (inner ℂ x ((P ^ (2 ^ (j + 1))) x)).re = ‖(P ^ (2 ^ j)) x‖ ^ 2`. Rewrite using `[pow_succ, pow_mul, sq, Module.End.mul_apply, ← hsym]`. Conclude with `inner_self_eq_norm_sq (𝕜 := ℂ) ((P ^ (2 ^ j)) x)`. Establish `cs : |(inner ℂ x ((P ^ (2 ^ j)) x)).re| ≤ ‖(P ^ (2 ^ j)) x‖`. Combine the equalities or inequalities in the displayed calculation.

Establish `hpos : 0 ≤ (inner ℂ x (P x)).re ^ (2 ^ j)` using `pow_nonneg h0 _`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[pow_succ, pow_mul]`. Use `_ ≤ ((inner ℂ x ((P ^ (2 ^ j)) x)).re) ^ 2 := pow_le_pow_left₀ hpos ih 2`. Use `_ = |(inner ℂ x ((P ^ (2 ^ j)) x)).re| ^ 2 := (sq_abs _).symm`.

Use `_ ≤ ‖(P ^ (2 ^ j)) x‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) cs 2`. Use `_ = _ := key.symm`.
-/
theorem symmetric_power_holds : A7 := by
  intro W _ _ P hP x hx h0 j
  induction j with
  | zero => simp
  | succ j ih =>
    have hsym := identity_filtration_of_scalar.symm_pow P hP (2 ^ j)

    have key : (inner ℂ x ((P ^ (2 ^ (j + 1))) x)).re = ‖(P ^ (2 ^ j)) x‖ ^ 2 := by
      rw [pow_succ, pow_mul, sq, Module.End.mul_apply, ← hsym]
      exact inner_self_eq_norm_sq (𝕜 := ℂ) ((P ^ (2 ^ j)) x)

    have cs : |(inner ℂ x ((P ^ (2 ^ j)) x)).re| ≤ ‖(P ^ (2 ^ j)) x‖ := by
      calc _ ≤ ‖inner ℂ x ((P ^ (2 ^ j)) x)‖ := Complex.abs_re_le_norm _
        _ ≤ ‖x‖ * ‖(P ^ (2 ^ j)) x‖ := norm_inner_le_norm _ _
        _ = _ := by rw [hx, one_mul]
    have hpos : 0 ≤ (inner ℂ x (P x)).re ^ (2 ^ j) := pow_nonneg h0 _
    calc (inner ℂ x (P x)).re ^ (2 ^ (j + 1)) = ((inner ℂ x (P x)).re ^ (2 ^ j)) ^ 2 := by
          rw [pow_succ, pow_mul]
      _ ≤ ((inner ℂ x ((P ^ (2 ^ j)) x)).re) ^ 2 := pow_le_pow_left₀ hpos ih 2
      _ = |(inner ℂ x ((P ^ (2 ^ j)) x)).re| ^ 2 := (sq_abs _).symm
      _ ≤ ‖(P ^ (2 ^ j)) x‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) cs 2
      _ = _ := key.symm

end PositivityTheory.CW

end
