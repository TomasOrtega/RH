import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogAddRpowMulLogPowLeRpow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowAndImp
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowCardWordsLe
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

/- English proof (translation)
Establish `hx0 : 0 < x` using `by linarith`. Establish `hlx : 0 < Real.log x` using `Real.log_pos hx`. Establish `hl2 : Real.log 2 ≤ 1`. Use `Real.log_two_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1 : Real.log k ≤ Real.log 2 + a * Real.log x`. Use `Real.log_le_log hk0 hk` as an intermediate fact. Rewrite `this` using `[Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hx0 a).ne', Real.log_rpow hx0]`. Then use the resulting hypothesis. Establish `h2 : Real.log g ≤ Real.log 2 + 8 * (Real.log k + y)`. Use `Real.log_le_log hg0 hg` as an intermediate fact.

Rewrite `this` using `[Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_mul hk0.ne' (Real.exp_pos y).ne', Real.log_exp, Nat.cast_ofNat]`. Then use the resulting hypothesis. Establish `h3 : a * Real.log x ≤ 5 * Real.log x` using `mul_le_mul_of_nonneg_right ha hlx.le`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_le_of_le_two_mul_pow_eight {x a y k g : ℝ} (hx : 1 < x) (ha : a ≤ 5) (hy : 0 ≤ y) (hk0 : 0 < k)
    (hk : k ≤ 2 * x ^ a) (hg0 : 0 < g) (hg : g ≤ 2 * (k * Real.exp y) ^ 8) :
    Real.log g ≤ 40 * Real.log x + 9 * y + 9 := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  have h1 : Real.log k ≤ Real.log 2 + a * Real.log x := by
    have := Real.log_le_log hk0 hk
    rwa [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hx0 a).ne', Real.log_rpow hx0] at this
  have h2 : Real.log g ≤ Real.log 2 + 8 * (Real.log k + y) := by
    have := Real.log_le_log hg0 hg
    rwa [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
      Real.log_mul hk0.ne' (Real.exp_pos y).ne', Real.log_exp, Nat.cast_ofNat] at this
  have h3 : a * Real.log x ≤ 5 * Real.log x := mul_le_mul_of_nonneg_right ha hlx.le
  linarith

/- English proof (translation)
Introduce `eps he he' C _`. Take `⟨x0, hx0⟩` from `GlobalTheory.log_add_rpow_mul_log_pow_le_rpow eps (eps + eps / 100) 40 9 1 0 he.le (by linarith) one_pos`. Use `⟨0, fun cD _ => ⟨0, fun ch _ => ⟨x0, ?_⟩⟩⟩` and prove the remaining obligations. Introduce `D L hLe hx hV i j`. Take `⟨-, -, ⟨hk1, hk2⟩, -⟩` from `hV.ranks`.

Take `⟨-, -, -, -, hg, -⟩` from `hV.host`. Establish `hx1` using `L.sc.one_lt_alt`. Establish `hxp : 0 < L.sc.x` using `by linarith`. Establish `hk0 : (0 : ℝ) < D.R.k` using `lt_of_lt_of_le (Real.rpow_pos_of_pos hxp _) hk1`. Establish `hb0 : 0 < L.sc.b` using `Real.exp_pos _`.

Use `⟨(hg i).1, (hg i).2.trans (by linarith [(hg j).1]), ?_⟩` and prove the remaining obligations. Establish `hg0 : (0 : ℝ) < D.host.g i` using `lt_of_lt_of_le (by positivity) (hg i).1`. Establish `hL0 : 0 ≤ L.sc.L` using `(Real.rpow_pos_of_pos hxp _).le`. Establish `h1` using `log_le_of_le_two_mul_pow_eight hx1 (by rw [hLe]; linarith) hL0 hk0 hk2 hg0 (hg i).2`. Establish `h2` using `hx0 L.sc.x hx`.

Establish `h3 : L.sc.x ^ szTh L * L.sc.L = L.sc.x ^ (eps + eps / 100)`. Simplify using `only [szTh, Scale.L, hLe]`. Rewrite using `[← Real.rpow_add hxp, add_comm]`. Rewrite using `[h3]`. Simplify using `only [Scale.L, hLe] at h1`.

Rewrite `h2` using `[pow_zero, mul_one, one_mul]`. Conclude with `h1.trans h2`.
-/
theorem szRow_sizeG : SzRow (fun _ _ L => SizeG L) := by
  intro eps he he' C _
  obtain ⟨x0, hx0⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow eps (eps + eps / 100) 40 9 1 0 he.le
    (by linarith) one_pos
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨x0, ?_⟩⟩⟩
  intro D L hLe hx hV i j
  obtain ⟨-, -, ⟨hk1, hk2⟩, -⟩ := hV.ranks
  obtain ⟨-, -, -, -, hg, -⟩ := hV.host
  have hx1 := L.sc.one_lt_alt
  have hxp : 0 < L.sc.x := by linarith
  have hk0 : (0 : ℝ) < D.R.k := lt_of_lt_of_le (Real.rpow_pos_of_pos hxp _) hk1
  have hb0 : 0 < L.sc.b := Real.exp_pos _
  refine ⟨(hg i).1, (hg i).2.trans (by linarith [(hg j).1]), ?_⟩
  have hg0 : (0 : ℝ) < D.host.g i := lt_of_lt_of_le (by positivity) (hg i).1
  have hL0 : 0 ≤ L.sc.L := (Real.rpow_pos_of_pos hxp _).le
  have h1 := log_le_of_le_two_mul_pow_eight hx1 (by rw [hLe]; linarith) hL0 hk0 hk2 hg0 (hg i).2
  have h2 := hx0 L.sc.x hx
  have h3 : L.sc.x ^ szTh L * L.sc.L = L.sc.x ^ (eps + eps / 100) := by
    simp only [szTh, Scale.L, hLe]
    rw [← Real.rpow_add hxp, add_comm]
  rw [h3]
  simp only [Scale.L, hLe] at h1
  rw [pow_zero, mul_one, one_mul] at h2
  exact h1.trans h2

/- English proof (translation)
The claim follows from `szRow_and_imp.1 _ _ szRow_sizeG szRow_card_words_le`.
-/
theorem szRow_sizeG_sizeWords : SzRow (fun _ _ L => SizeG L ∧ SizeWords L) :=
  szRow_and_imp.1 _ _ szRow_sizeG szRow_card_words_le

end GlobalTheory.EX
