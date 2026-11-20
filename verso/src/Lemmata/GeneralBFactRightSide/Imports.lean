import Mathlib

namespace Bl.general_b_fact_right_side

/- English proof (translation)
Introduce `x`. Rewrite using `[Complex.exp_eq_one_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, hn⟩`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Establish `h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0`. Simplify using `[Real.pi_ne_zero, Complex.I_ne_zero]`. Establish `h3 : (x : ℂ) = (n : ℂ)`. Rewrite `hn` using `[mul_comm (n : ℂ)]`. Conclude with `mul_left_cancel₀ h2 hn`.

Conclude with `h3` after adjusting the coercions. Introduce and unpack `⟨n, rfl⟩`. Conclude with `⟨n, by push_cast; ring⟩`.
-/
theorem goal1 :
  ∀ (x : Real),
  Iff
    (Eq.{1}
      (Complex.exp
        (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 (Complex.ofReal Real.pi)) Complex.I)
          (Complex.ofReal x)))
      1)
    (Exists.{1} fun (n : Int) ↦ Eq.{1} x (Int.cast.{0} n)) := by
  intro x
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have h3 : (x : ℂ) = (n : ℂ) := by
      rw [mul_comm (n : ℂ)] at hn
      exact mul_left_cancel₀ h2 hn
    exact_mod_cast h3
  · rintro ⟨n, rfl⟩
    exact ⟨n, by push_cast; ring⟩

end Bl.general_b_fact_right_side
