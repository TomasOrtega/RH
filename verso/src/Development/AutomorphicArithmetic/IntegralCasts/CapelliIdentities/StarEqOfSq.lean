import Mathlib

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
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
