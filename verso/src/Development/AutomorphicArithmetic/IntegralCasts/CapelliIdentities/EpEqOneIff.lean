import Mathlib

/- English proof (translation)
Introduce `t`. Rewrite using `[Complex.exp_eq_one_iff]`. Use `exists_congr fun n => ?_` and prove the remaining obligations. Rewrite using `[mul_comm ((n : ℤ) : ℂ), mul_right_inj' Complex.two_pi_I_ne_zero]`. Conclude with `Iff.rfl` after adjusting the coercions.
-/
theorem UpperTheory.Reformulated.B.Qj15.ep_eq_one_iff :
    ∀ (t : ℝ),
    Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑t : ℂ)) = (1 : ℂ) ↔ ∃ (n : ℤ), t = (↑n : ℝ) := by
  intro t
  rw [Complex.exp_eq_one_iff]
  refine exists_congr fun n => ?_
  rw [mul_comm ((n : ℤ) : ℂ), mul_right_inj' Complex.two_pi_I_ne_zero]
  exact_mod_cast Iff.rfl
