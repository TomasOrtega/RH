import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScale
import Development.AutomorphicArithmetic.ShortNorms.Primes
import Development.AutomorphicArithmetic.ShortNorms.normPrimesN
import Development.AutomorphicArithmetic.ShortNorms.levelPrimeN

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

/- English proof (translation)
Take `⟨A, B, h1, h2, h3⟩` from `h`. Conclude with `⟨(A, B), h1, h2, h3⟩`.
-/
theorem normOne_pair_form {d M p : ℕ} (h : GlobalTheory.Mem.An.NormOne d M p) : GlobalTheory.EX.NormOne d M p := by
  obtain ⟨A, B, h1, h2, h3⟩ := h
  exact ⟨(A, B), h1, h2, h3⟩

/- English proof (translation)
Introduce `eps he0 he1`. Take `⟨x0, hx0⟩` from `UpperTheory.T3.normPrimesN UpperTheory.T3.shortNorm eps he0`. Use `⟨x0, fun s R N d hs hx hR hq => ?_⟩` and prove the remaining obligations. Establish `hk : (1 : ℝ) ≤ R.k`. Use `R.m_add_three_le_k` as an intermediate fact.

Conclude with `(by omega : 1 ≤ R.k)` after adjusting the coercions. Establish `hb : 0 < s.b` using `Real.exp_pos _`. Establish `hY : 0 < ((R.k : ℝ) * s.b) ^ 8` using `by positivity`. Establish `hlog : 8 * s.x ^ eps ≤ Real.log (((R.k : ℝ) * s.b) ^ 8)`. Rewrite using `[Real.log_pow, Real.log_mul (by linarith) hb.ne']`.

Establish `h1 : Real.log s.b = s.x ^ eps`. Rewrite using `[← hs]`. Conclude with `Real.log_exp _`. Establish `h2` using `Real.log_nonneg hk`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `(hx0 s.x hx N d (hs ▸ hq) _ hY hlog).trans ?_` and prove the remaining obligations. Use `Nat.cast_le.mpr (Finset.card_le_card fun g hg => ?_)` and prove the remaining obligations. Simplify using `only [GlobalTheory.Mem.An.normPrimes, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at hg ⊢`. Take `⟨⟨h1, h2⟩, h3, h4⟩` from `hg`.

Conclude with `⟨Nat.lt_succ_of_le h2, h3, (Nat.lt_of_floor_lt h1).le, normOne_pair_form h4⟩`.
-/
theorem normPrimes_unconditional : NormPrimes := by
  intro eps he0 he1
  obtain ⟨x0, hx0⟩ := UpperTheory.T3.normPrimesN UpperTheory.T3.shortNorm eps he0
  refine ⟨x0, fun s R N d hs hx hR hq => ?_⟩
  have hk : (1 : ℝ) ≤ R.k := by
    have := R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ R.k)
  have hb : 0 < s.b := Real.exp_pos _
  have hY : 0 < ((R.k : ℝ) * s.b) ^ 8 := by positivity
  have hlog : 8 * s.x ^ eps ≤ Real.log (((R.k : ℝ) * s.b) ^ 8) := by
    rw [Real.log_pow, Real.log_mul (by linarith) hb.ne']
    have h1 : Real.log s.b = s.x ^ eps := by
      rw [← hs]; exact Real.log_exp _
    have h2 := Real.log_nonneg hk
    push_cast
    linarith
  refine (hx0 s.x hx N d (hs ▸ hq) _ hY hlog).trans ?_
  refine Nat.cast_le.mpr (Finset.card_le_card fun g hg => ?_)
  simp only [GlobalTheory.Mem.An.normPrimes, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at hg ⊢
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hg
  exact ⟨Nat.lt_succ_of_le h2, h3, (Nat.lt_of_floor_lt h1).le, normOne_pair_form h4⟩

/- English proof (translation)
Introduce `eps c he0 he1 hc`. Take `⟨x0, hx0⟩` from `UpperTheory.T3.levelPrimeN UpperTheory.T3.shortNorm eps he0 he1 c 9 hc (by norm_num)`. Take `⟨x1, hx1⟩` from `rank_basic_bounds eps he0 he1`. Use `⟨max x0 x1, fun s R N d g0 g1 Ts hs hx hR hq hg0 hg1 hb0 hb1 hTs hlog => ?_⟩` and prove the remaining obligations. Take `⟨hf, -, hr, hkr, -, -, -, -, -, -, -, -, -, -, -, hm, -⟩` from `hx1 s R hs (le_trans (le_max_right _ _) hx) hR`.

Establish `hx1'` using `s.one_lt_alt`. Establish `hxp : 0 < s.x` using `by linarith`. Establish `hn : 1 ≤ R.n` using `R.toFrame.ord_pos`. Establish `hk : (1 : ℝ) ≤ R.k`. Use `R.m_add_three_le_k` as an intermediate fact.

Conclude with `(by omega : 1 ≤ R.k)` after adjusting the coercions. Establish `hf1 : (1 : ℝ) ≤ R.f`. Conclude with `(by unfold Ranks.f; omega : 1 ≤ R.f)` after adjusting the coercions. Establish `hL : s.L = s.x ^ eps` using `by rw [← hs]; rfl`. Establish `hg : ∀ g : ℕ, 1 ≤ g → (g : ℝ) ≤ s.b ^ 9 → Real.log g ≤ 9 * s.x ^ eps`.

Introduce `g h1 h2`. Establish `h3 : (0 : ℝ) < g` using `by exact_mod_cast h1`. Use `(Real.log_le_log h3 h2).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Real.log_pow, Scale.b, Real.log_exp, hL]`. Evaluate the numerical expressions.

Establish `hm' : s.x ^ ((1 : ℝ) / 3) ≤ (R.m : ℝ)` using `(Real.rpow_le_rpow_of_exponent_le hx1'.le (by rw [hs]; linarith)).trans hm`. Establish `hW1 : (1 : ℝ) ≤ (R.f : ℝ) * R.k` using `one_le_mul_of_one_le_of_one_le hf1 hk`. Establish `hW2 : (R.f : ℝ) * R.k ≤ s.x ^ (12 : ℝ)`. Establish `hk5 : (R.k : ℝ) ≤ s.x ^ (5 : ℝ)` using `(Nat.cast_le.mpr hkr).trans hr`. Conclude with `(rank_mul_le hxp (by linarith) hf hk5).trans (Real.rpow_le_rpow_of_exponent_le hx1'.le (by norm_num))`.

Take `⟨T, hT1, hT2, hT3, hT4⟩` from `hx0 s.x (le_trans (le_max_left _ _) hx) N d g0 g1 R.m (hs ▸ hq) hg0 hg1 (hg g0 hg0 hb0) (hg g1 hg1 hb1) hm' _ Ts hW1 hW2 hTs (hL ▸ hlog)`. Conclude with `⟨T, hT1, hT2.le, hT3, normOne_pair_form hT4⟩`.
-/
theorem levelPrime_unconditional : LevelPrime := by
  intro eps c he0 he1 hc
  obtain ⟨x0, hx0⟩ := UpperTheory.T3.levelPrimeN UpperTheory.T3.shortNorm eps he0 he1 c 9 hc (by norm_num)
  obtain ⟨x1, hx1⟩ := rank_basic_bounds eps he0 he1
  refine ⟨max x0 x1, fun s R N d g0 g1 Ts hs hx hR hq hg0 hg1 hb0 hb1 hTs hlog => ?_⟩
  obtain ⟨hf, -, hr, hkr, -, -, -, -, -, -, -, -, -, -, -, hm, -⟩ :=
    hx1 s R hs (le_trans (le_max_right _ _) hx) hR
  have hx1' := s.one_lt_alt
  have hxp : 0 < s.x := by linarith
  have hn : 1 ≤ R.n := R.toFrame.ord_pos
  have hk : (1 : ℝ) ≤ R.k := by
    have := R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ R.k)
  have hf1 : (1 : ℝ) ≤ R.f := by
    exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ R.f)
  have hL : s.L = s.x ^ eps := by rw [← hs]; rfl
  have hg : ∀ g : ℕ, 1 ≤ g → (g : ℝ) ≤ s.b ^ 9 → Real.log g ≤ 9 * s.x ^ eps := by
    intro g h1 h2
    have h3 : (0 : ℝ) < g := by exact_mod_cast h1
    refine (Real.log_le_log h3 h2).trans (le_of_eq ?_)
    rw [Real.log_pow, Scale.b, Real.log_exp, hL]
    norm_num
  have hm' : s.x ^ ((1 : ℝ) / 3) ≤ (R.m : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hx1'.le (by rw [hs]; linarith)).trans hm
  have hW1 : (1 : ℝ) ≤ (R.f : ℝ) * R.k := one_le_mul_of_one_le_of_one_le hf1 hk
  have hW2 : (R.f : ℝ) * R.k ≤ s.x ^ (12 : ℝ) := by
    have hk5 : (R.k : ℝ) ≤ s.x ^ (5 : ℝ) := (Nat.cast_le.mpr hkr).trans hr
    exact (rank_mul_le hxp (by linarith) hf hk5).trans
      (Real.rpow_le_rpow_of_exponent_le hx1'.le (by norm_num))
  obtain ⟨T, hT1, hT2, hT3, hT4⟩ := hx0 s.x (le_trans (le_max_left _ _) hx) N d g0 g1 R.m (hs ▸ hq)
    hg0 hg1 (hg g0 hg0 hb0) (hg g1 hg1 hb1) hm' _ Ts hW1 hW2 hTs (hL ▸ hlog)
  exact ⟨T, hT1, hT2.le, hT3, normOne_pair_form hT4⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨normPrimes_unconditional, levelPrime_unconditional⟩`.
-/
theorem normPrimes_and_levelPrime_unconditional : NormPrimes ∧ LevelPrime :=
  ⟨normPrimes_unconditional, levelPrime_unconditional⟩

end GlobalTheory.EX
