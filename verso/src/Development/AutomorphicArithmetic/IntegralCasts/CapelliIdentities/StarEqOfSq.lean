import Mathlib

/- English proof (translation)
Introduce `z r hr h`. Establish `hre : z.re * z.re - z.im * z.im = r`. Simplify using `using congrArg Complex.re h`. Establish `him : z.re * z.im + z.im * z.re = 0`. Simplify using `using congrArg Complex.im h`.

Establish `h0 : z.im = 0`. Assume the negation of the conclusion as `hne`. Establish `h1 : z.re * z.im = 0` using `by linarith [mul_comm z.re z.im]`. Establish `h2 : z.re = 0` using `(mul_eq_zero.mp h1).resolve_right hne`. Establish `h3 : 0 < z.im * z.im` using `mul_self_pos.mpr hne`.

Rewrite `hre` using `[h2]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `Complex.conj_eq_iff_im.mpr h0`.
-/
theorem UpperTheory.Reformulated.B.Ra8.star_eq_of_sq :
    ∀ {z : ℂ} {r : ℝ},
    (0 : ℝ) ≤ r → z * z = (↑r : ℂ) → Star.star z = z := by
  intro z r hr h
  have hre : z.re * z.re - z.im * z.im = r := by
    simpa using congrArg Complex.re h
  have him : z.re * z.im + z.im * z.re = 0 := by
    simpa using congrArg Complex.im h
  have h0 : z.im = 0 := by
    by_contra hne
    have h1 : z.re * z.im = 0 := by linarith [mul_comm z.re z.im]
    have h2 : z.re = 0 := (mul_eq_zero.mp h1).resolve_right hne
    have h3 : 0 < z.im * z.im := mul_self_pos.mpr hne
    rw [h2] at hre
    linarith
  exact Complex.conj_eq_iff_im.mpr h0
