import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparison

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

/- English proof (translation)
Introduce `eps he he' C hC`. Take `⟨x1, h1⟩` from `GlobalTheory.scale_poly_comparison eps (5 * |(C.P.Cw : ℝ)|) (1 / 10) he (by norm_num)`. Use `⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max x1 16, fun D L hs hx hV => ?_⟩⟩⟩` and prove the remaining obligations. Establish `hx1 : x1 ≤ L.sc.x` using `le_trans (le_max_left _ _) hx`. Establish `hx16 : (16 : ℝ) ≤ L.sc.x` using `le_trans (le_max_right _ _) hx`.

Establish `hone : (1 : ℝ) ≤ L.sc.x` using `by linarith`. Establish `hx0 : (0 : ℝ) < L.sc.x` using `by linarith`. Take `⟨⟨hn1, -⟩, -, ⟨hk1, hk2⟩, -⟩` from `hV.ranks`. Rewrite `hn1`, `hk1`, `hk2` using `[hs]`. Establish `h2 : (2 : ℝ) ≤ L.sc.x ^ ((1 : ℝ) / 4)`.

Establish `h` using `Real.rpow_le_rpow (by norm_num) hx16 (show (0 : ℝ) ≤ 1 / 4 by norm_num)`. Establish `e : (16 : ℝ) ^ ((1 : ℝ) / 4) = 2`. Rewrite using `[show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]`. Evaluate the numerical expressions. Rewrite `h` using `[e]`. Then use the resulting hypothesis.

Establish `hup : ∀ a b : ℝ, 1 / 4 + a ≤ b → 2 * L.sc.x ^ a ≤ L.sc.x ^ b` using `fun a b hab => by`. Combine the equalities or inequalities in the displayed calculation. Establish `hn3 : (D.R.n : ℝ) ≤ L.sc.x ^ (3 : ℝ)` using `hV.ranks.n_le'.trans (hup _ _ (by norm_num))`. Establish `hk5 : (D.R.k : ℝ) ≤ L.sc.x ^ (5 : ℝ)` using `hk2.trans (hup _ _ (by linarith))`. Establish `hn0 : (1 : ℝ) ≤ D.R.n` using `(Real.one_le_rpow hone (by linarith)).trans hn1`.

Establish `hk0 : (1 : ℝ) ≤ D.R.k` using `(Real.one_le_rpow hone (by linarith)).trans hk1`. Take `⟨-, -, -, -, -, hw, -⟩` from `h1 L.sc hs hx1`. Take `⟨hw, -, -⟩` from `hw D.R.n (by exact_mod_cast hn0) hn3`. Establish `hb1 : (1 : ℝ) ≤ L.sc.b` using `Real.one_le_exp (Real.rpow_nonneg hx0.le _)`. Establish `hA : (1 : ℝ) ≤ L.sc.b ^ ((1 : ℝ) - 1 / 10)` using `Real.one_le_rpow hb1 (by norm_num)`.

Establish `hB : (1 : ℝ) ≤ L.sc.x ^ (5 * |(C.P.Cw : ℝ)|)` using `Real.one_le_rpow hone (by positivity)`. Establish `hcw : C.P.cw = 9 / 10` using `hC.2.2.2.2.1`. Establish `hkC : (D.R.k : ℝ) ^ (C.P.Cw : ℝ) ≤ L.sc.x ^ (5 * |(C.P.Cw : ℝ)|)`. Combine the equalities or inequalities in the displayed calculation. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Use `hkC.trans (le_trans ?_ hw)` and prove the remaining obligations. Conclude with `le_mul_of_one_le_left (by linarith) hA`. Rewrite using `[hcw, show (9 / 10 : ℝ) = 1 - 1 / 10 by norm_num]`. Conclude with `le_trans (le_mul_of_one_le_right (by linarith) hB) hw`.
-/
theorem szRow_thinSize_ge : SzRow (fun C D L => ((D.R.k : ℝ) ^ C.P.Cw ≤ L.sc.w'' D.R.n ∧ L.sc.b ^ C.P.cw ≤ L.sc.w'' D.R.n)) := by
  intro eps he he' C hC
  obtain ⟨x1, h1⟩ := GlobalTheory.scale_poly_comparison eps (5 * |(C.P.Cw : ℝ)|) (1 / 10) he (by norm_num)
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max x1 16, fun D L hs hx hV => ?_⟩⟩⟩
  have hx1 : x1 ≤ L.sc.x := le_trans (le_max_left _ _) hx
  have hx16 : (16 : ℝ) ≤ L.sc.x := le_trans (le_max_right _ _) hx
  have hone : (1 : ℝ) ≤ L.sc.x := by linarith
  have hx0 : (0 : ℝ) < L.sc.x := by linarith
  obtain ⟨⟨hn1, -⟩, -, ⟨hk1, hk2⟩, -⟩ := hV.ranks
  rw [hs] at hn1 hk1 hk2
  have h2 : (2 : ℝ) ≤ L.sc.x ^ ((1 : ℝ) / 4) := by
    have h := Real.rpow_le_rpow (by norm_num) hx16 (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    have e : (16 : ℝ) ^ ((1 : ℝ) / 4) = 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rwa [e] at h
  have hup : ∀ a b : ℝ, 1 / 4 + a ≤ b → 2 * L.sc.x ^ a ≤ L.sc.x ^ b := fun a b hab => by
    calc 2 * L.sc.x ^ a ≤ L.sc.x ^ ((1 : ℝ) / 4) * L.sc.x ^ a :=
          mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hx0.le _)
      _ = L.sc.x ^ (1 / 4 + a) := (Real.rpow_add hx0 _ _).symm
      _ ≤ L.sc.x ^ b := Real.rpow_le_rpow_of_exponent_le hone hab
  have hn3 : (D.R.n : ℝ) ≤ L.sc.x ^ (3 : ℝ) := hV.ranks.n_le'.trans (hup _ _ (by norm_num))
  have hk5 : (D.R.k : ℝ) ≤ L.sc.x ^ (5 : ℝ) := hk2.trans (hup _ _ (by linarith))
  have hn0 : (1 : ℝ) ≤ D.R.n := (Real.one_le_rpow hone (by linarith)).trans hn1
  have hk0 : (1 : ℝ) ≤ D.R.k := (Real.one_le_rpow hone (by linarith)).trans hk1
  obtain ⟨-, -, -, -, -, hw, -⟩ := h1 L.sc hs hx1
  obtain ⟨hw, -, -⟩ := hw D.R.n (by exact_mod_cast hn0) hn3
  have hb1 : (1 : ℝ) ≤ L.sc.b := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have hA : (1 : ℝ) ≤ L.sc.b ^ ((1 : ℝ) - 1 / 10) := Real.one_le_rpow hb1 (by norm_num)
  have hB : (1 : ℝ) ≤ L.sc.x ^ (5 * |(C.P.Cw : ℝ)|) := Real.one_le_rpow hone (by positivity)
  have hcw : C.P.cw = 9 / 10 := hC.2.2.2.2.1
  have hkC : (D.R.k : ℝ) ^ (C.P.Cw : ℝ) ≤ L.sc.x ^ (5 * |(C.P.Cw : ℝ)|) := by
    calc (D.R.k : ℝ) ^ (C.P.Cw : ℝ) ≤ (D.R.k : ℝ) ^ |(C.P.Cw : ℝ)| :=
          Real.rpow_le_rpow_of_exponent_le hk0 (le_abs_self _)
      _ ≤ (L.sc.x ^ (5 : ℝ)) ^ |(C.P.Cw : ℝ)| :=
          Real.rpow_le_rpow (by linarith) hk5 (abs_nonneg _)
      _ = L.sc.x ^ (5 * |(C.P.Cw : ℝ)|) := (Real.rpow_mul hx0.le _ _).symm
  refine ⟨?_, ?_⟩
  · refine hkC.trans (le_trans ?_ hw)
    exact le_mul_of_one_le_left (by linarith) hA
  · rw [hcw, show (9 / 10 : ℝ) = 1 - 1 / 10 by norm_num]
    exact le_trans (le_mul_of_one_le_right (by linarith) hB) hw

end GlobalTheory.EX
