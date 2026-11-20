import Formalism.SharpRestriction.ElevenLe
import Formalism.LocalRingCardinality.NFLeTwoMulTSq

namespace Formalism.BasicNotions

open Formalism.MainNotions

/- English proof (translation)
Take `⟨hNl, -⟩` from `hN`. Take `⟨-, hMu⟩` from `hM`. Establish `hx : 1 < L.sc.x` using `L.sc.one_lt_alt`. Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `he : 0 < L.sc.eps` using `L.sc.eps_pos`.

Establish `hd0 : 0 ≤ L.sc.delta1`. Unfold `Scale.delta1`. Conclude with `Real.rpow_nonneg hx0.le _`. Establish `hsq : Real.sqrt (L.sc.x * L.sc.delta1) ^ 2 = L.sc.x * L.sc.delta1` using `Real.sq_sqrt (mul_nonneg hx0.le hd0)`. Establish `hth : szTh L = L.sc.eps / 100` using `rfl`.

Establish `e1 : (L.sc.x ^ szTh L) ^ 4 = L.sc.x ^ (szTh L * 4)`. Rewrite using `[Real.rpow_mul hx0.le]`. Use `first`. Consider the case `(norm_num; done)`. Consider the case `exact_mod_cast (Real.rpow_natCast (L.sc.x ^ szTh L) 4).symm`.

Establish `e2 : Real.sqrt (L.sc.x * L.sc.delta1) ^ 4 = L.sc.x ^ (2 - L.sc.eps / 4)`. Establish `h4 : Real.sqrt (L.sc.x * L.sc.delta1) ^ 4 = (L.sc.x * L.sc.delta1) ^ 2`. Combine the equalities or inequalities in the displayed calculation. Establish `h5 : L.sc.x ^ (2 - L.sc.eps / 4) = L.sc.x ^ (2 : ℝ) * L.sc.x ^ (-(L.sc.eps / 8) * 2)`. Rewrite using `[← Real.rpow_add hx0]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h4, h5, Real.rpow_mul hx0.le, mul_pow]`. Unfold `Scale.delta1`. Rewrite using `[Real.rpow_two, Real.rpow_two]`.

Establish `h1 : (D.R.m : ℝ) ^ 4 ≤ (L.sc.x ^ szTh L * Real.sqrt (L.sc.x * L.sc.delta1)) ^ 4` using `by first`. Consider the case `exact pow_le_pow_left₀ (Nat.cast_nonneg _) hMu 4`. Consider the case `gcongr`. Establish `h2 : (L.sc.x ^ szTh L * Real.sqrt (L.sc.x * L.sc.delta1)) ^ 4 = L.sc.x ^ (szTh L * 4 + (2 - L.sc.eps / 4))`. Rewrite using `[mul_pow, e1, e2, ← Real.rpow_add hx0]`.

Establish `h3 : L.sc.x ^ (szTh L * 4 + (2 - L.sc.eps / 4)) ≤ L.sc.x ^ (2 + 8 * L.sc.eps - szTh L)`. Apply `Real.rpow_le_rpow_of_exponent_le hx.le` to reduce the goal to its premises. Rewrite using `[hth]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h6 : ((D.R.m ^ 4 : ℕ) : ℝ) ≤ ((D.R.n : ℕ) : ℝ)`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `h6` after adjusting the coercions.
-/
theorem m_pow_four_le_n {D : D7} (L : SizeData₂ D) (hN : SizeN L) (hM : SizeM L) : D.R.m ^ 4 ≤ D.R.n := by
  obtain ⟨hNl, -⟩ := hN
  obtain ⟨-, hMu⟩ := hM
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have he : 0 < L.sc.eps := L.sc.eps_pos
  have hd0 : 0 ≤ L.sc.delta1 := by
    unfold Scale.delta1
    exact Real.rpow_nonneg hx0.le _
  have hsq : Real.sqrt (L.sc.x * L.sc.delta1) ^ 2 = L.sc.x * L.sc.delta1 :=
    Real.sq_sqrt (mul_nonneg hx0.le hd0)
  have hth : szTh L = L.sc.eps / 100 := rfl
  have e1 : (L.sc.x ^ szTh L) ^ 4 = L.sc.x ^ (szTh L * 4) := by
    rw [Real.rpow_mul hx0.le]
    first
      | (norm_num; done)
      | exact_mod_cast (Real.rpow_natCast (L.sc.x ^ szTh L) 4).symm
  have e2 : Real.sqrt (L.sc.x * L.sc.delta1) ^ 4 = L.sc.x ^ (2 - L.sc.eps / 4) := by
    have h4 : Real.sqrt (L.sc.x * L.sc.delta1) ^ 4 = (L.sc.x * L.sc.delta1) ^ 2 := by
      calc Real.sqrt (L.sc.x * L.sc.delta1) ^ 4
          = (Real.sqrt (L.sc.x * L.sc.delta1) ^ 2) ^ 2 := by ring
        _ = (L.sc.x * L.sc.delta1) ^ 2 := by rw [hsq]
    have h5 : L.sc.x ^ (2 - L.sc.eps / 4)
        = L.sc.x ^ (2 : ℝ) * L.sc.x ^ (-(L.sc.eps / 8) * 2) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    rw [h4, h5, Real.rpow_mul hx0.le, mul_pow]
    unfold Scale.delta1
    rw [Real.rpow_two, Real.rpow_two]
  have h1 : (D.R.m : ℝ) ^ 4 ≤ (L.sc.x ^ szTh L * Real.sqrt (L.sc.x * L.sc.delta1)) ^ 4 :=
    by
      first
        | exact pow_le_pow_left₀ (Nat.cast_nonneg _) hMu 4
        | gcongr
  have h2 : (L.sc.x ^ szTh L * Real.sqrt (L.sc.x * L.sc.delta1)) ^ 4
      = L.sc.x ^ (szTh L * 4 + (2 - L.sc.eps / 4)) := by
    rw [mul_pow, e1, e2, ← Real.rpow_add hx0]
  have h3 : L.sc.x ^ (szTh L * 4 + (2 - L.sc.eps / 4)) ≤ L.sc.x ^ (2 + 8 * L.sc.eps - szTh L) := by
    apply Real.rpow_le_rpow_of_exponent_le hx.le
    rw [hth]
    linarith
  have h6 : ((D.R.m ^ 4 : ℕ) : ℝ) ≤ ((D.R.n : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast h6

/- English proof (translation)
Take `⟨hN, hM, -⟩` from `h`. Establish `h4` using `m_pow_four_le_n L hN hM`. Use `show D.R.m ^ 4 ≤ 2 * D.R.n`. Use `first`. Consider the case `omega`.

Consider the case `linarith`.
-/
theorem m_pow_four_le_f {D : D7} (L : SizeData₂ D) (h : SizesAt L) : D.R.m ^ 4 ≤ D.R.f := by
  obtain ⟨hN, hM, -⟩ := h
  have h4 := m_pow_four_le_n L hN hM
  show D.R.m ^ 4 ≤ 2 * D.R.n
  first
    | omega
    | linarith

end Formalism.BasicNotions
