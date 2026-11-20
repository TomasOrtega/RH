import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HostBoundsTwoMulRpowLogSqLe

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

set_option maxHeartbeats 800000 in

/- English proof (translation)
Unfold `SizeKRel szTh rankBudget`. Generalize the expression as in `L.sc = s at *`. Generalize the expression as in `L.CGam = c at *`. Generalize the expression as in `Real.log D.host.rdE = ρ at *`. Generalize the expression as in `D.R = R at *`.

Establish `hn2` using `hR.n_le`. Take `⟨⟨hn1, -⟩, ⟨hm1, hm2⟩, ⟨hk1, hk2⟩, -⟩` from `hR`. Establish `hx` using `s.one_lt_alt`. Establish `hxp : 0 < s.x` using `lt_trans one_pos hx`. Establish `e0` using `s.eps_pos`.

Establish `e1` using `s.eps_lt`. Establish `hc0` using `abs_nonneg c`. Establish `hc1` using `le_abs_self c`. Establish `mono : ∀ {a b : ℝ}, a ≤ b → s.x ^ a ≤ s.x ^ b` using `fun h => Real.rpow_le_rpow_of_exponent_le hx.le h`. Establish `pos : ∀ a : ℝ, 0 < s.x ^ a` using `fun a => Real.rpow_pos_of_pos hxp a`.

Establish `one : ∀ {a : ℝ}, 0 ≤ a → 1 ≤ s.x ^ a` using `fun h => Real.one_le_rpow hx.le h`. Establish `mul : ∀ {u v a b : ℝ}, u ≤ s.x ^ a → 0 ≤ v → v ≤ s.x ^ b → u * v ≤ s.x ^ (a + b)`. Introduce `u v a b hu hv hv'`. Rewrite using `[Real.rpow_add hxp]`. Conclude with `mul_le_mul hu hv' hv (pos _).le`.

Establish `mulL : ∀ {u v a b : ℝ}, s.x ^ a ≤ u → s.x ^ b ≤ v → s.x ^ (a + b) ≤ u * v`. Introduce `u v a b hu hv`. Rewrite using `[Real.rpow_add hxp]`. Conclude with `mul_le_mul hu hv (pos _).le ((pos _).le.trans hu)`. Establish `pw : ∀ {u a : ℝ} (j : ℕ), 0 ≤ u → u ≤ s.x ^ a → u ^ j ≤ s.x ^ (a * j)`.

Introduce `u a j hu h`. Rewrite using `[Real.rpow_mul_natCast hxp.le]`. Conclude with `pow_le_pow_left₀ hu h j`. Establish `ab : ∀ {a C : ℝ}, C ≤ 100 → C * s.x ^ a ≤ s.x ^ (s.eps / 1000 + a)` using `fun hC => mul (by linarith) (pos _).le le_rfl`. Establish `hsq : Real.sqrt (s.x * s.delta1) = s.x ^ ((1 : ℝ) / 2 - s.eps / 16)`.

Establish `: s.x * s.delta1 = s.x ^ (1 + -(s.eps / 8))`. Rewrite using `[Real.rpow_add hxp, Real.rpow_one]`. Both sides reduce to the same expression. Rewrite using `[this, Real.sqrt_eq_rpow, ← Real.rpow_mul hxp.le]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `hm1`, `hm2` using `[hsq]`. Establish `h2m` using `R.two_le_m`. Establish `hmk` using `R.m_add_three_le_k`. Establish `hkr : R.k ≤ R.r` using `by unfold Ranks.r; omega`.

Establish `hkr' : (R.k : ℝ) ≤ R.r` using `by exact_mod_cast hkr`. Establish `hfk : (R.f : ℝ) ≤ R.k` using `by exact_mod_cast R.f_le_k`. Establish `hfn : (R.f : ℝ) = 2 * R.n` using `by unfold Ranks.f; push_cast; ring`. Establish `h2m' : (2 : ℝ) ≤ R.m` using `by exact_mod_cast h2m`. Establish `k5 : (5 : ℝ) ≤ R.k` using `by exact_mod_cast (by omega : 5 ≤ R.k)`.

Establish `n0 : (0 : ℝ) ≤ R.n` using `by positivity`. Establish `f0 : (0 : ℝ) ≤ R.f` using `by positivity`. Establish `m0 : (0 : ℝ) ≤ R.m` using `by positivity`. Establish `hf : (R.f : ℝ) ≤ s.x ^ (s.eps / 1000 + (2 + 8 * s.eps + s.eps / 100))`. Use `ab (C := 4) (a := 2 + 8 * s.eps + s.eps / 100) (by norm_num)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hf2 : s.x ^ (2 + 8 * s.eps) ≤ (R.f : ℝ)` using `by linarith`. Establish `hk : (R.k : ℝ) ≤ s.x ^ (s.eps / 1000 + (9 / 2 + 10 * s.eps))` using `hk2.trans (ab (by norm_num))`. Establish `hm : (R.m : ℝ) ≤ s.x ^ (s.eps / 1000 + (1 / 2 - s.eps / 16))` using `hm2.trans (ab (by norm_num))`. Establish `hL : s.L ≤ s.x ^ s.eps` using `le_rfl`.

Establish `hL1 : 1 ≤ s.L` using `one e0.le`. Establish `L0 : 0 ≤ s.L` using `by linarith`. Establish `hlog : ∀ y : ℝ, 5 ≤ y → 1 ≤ Real.log y`. Introduce `y hy`. Rewrite using `[Real.le_log_iff_exp_le (by linarith)]`.

Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlk` using `hlog _ k5`. Establish `hlr` using `hlog R.r (by linarith)`. Establish `hsx : Real.sqrt s.x = s.x ^ ((1 : ℝ) / 2)` using `Real.sqrt_eq_rpow _`.

Establish `hR0 : s.x ^ ((2 + 8 * s.eps) + -s.eps) ≤ (R.n : ℝ) * s.x ^ (-s.eps)` using `mulL hn1 le_rfl`. Establish `hlf0 : 0 ≤ Real.log R.f` using `Real.log_natCast_nonneg _`. Establish `hlf : Real.log R.f ≤ s.x ^ ((1 : ℝ) / 5)`. Establish `h1` using `Real.log_le_rpow_div f0 (show (0 : ℝ) < 1 / 30 by norm_num)`. Establish `h2 : (R.f : ℝ) ^ ((1 : ℝ) / 30) ≤ s.x ^ ((1 : ℝ) / 10)`.

Combine the equalities or inequalities in the displayed calculation. Establish `h3` using `(ab (C := 30) (a := 1 / 10) (by norm_num)).trans (mono (b := 1 / 5) (by linarith))`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlf2 : Real.log R.f ^ 2 ≤ s.x ^ ((2 : ℝ) / 5)` using `(pw 2 hlf0 hlf).trans (mono (by norm_num))`. Establish `hm4 : 4 * s.x ^ ((2 : ℝ) / 5) ≤ R.m` using `((ab (by norm_num)).trans (mono (by linarith))).trans hm1`.

Establish `h25 : 1 ≤ s.x ^ ((2 : ℝ) / 5)` using `one (by norm_num)`. Establish `hthL : s.x ^ (s.eps / 100) * s.L ≤ R.f` using `((mul le_rfl L0 hL).trans (mono (by linarith))).trans hf2`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `le_trans ?_ hk1` and prove the remaining obligations. Use `(mul (mul (mul (mul le_rfl (by positivity) (pw 5 m0 hm)) f0 hf) L0 hL) (pos _).le le_rfl).trans (mono ?_)` and prove the remaining obligations.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Use `le_trans ?_ hk1` and prove the remaining obligations. Establish `h8 : 8 * c ≤ s.x ^ (s.eps / 1000)` using `by linarith`. Use `(mul (mul (mul h8 (by positivity) (pw 5 m0 hm)) f0 hf) L0 hL).trans (mono ?_)` and prove the remaining obligations.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hsx]`. Use `hk.trans (le_trans (mono ?_) (mulL (mulL le_rfl hn1) hR0))` and prove the remaining obligations. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[Real.sqrt_le_left (by positivity), div_le_iff₀ (by linarith), sq]`. Use `hk.trans (le_trans (mono ?_) (mulL (mulL hR0 hR0) hm1))` and prove the remaining obligations. Combine the linear equalities and inequalities to obtain the conclusion. Use `le_trans ?_ hk1` and prove the remaining obligations. Use `(mul (pw 2 m0 hm) L0 hL).trans (mono ?_)` and prove the remaining obligations.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Use `le_trans ?_ hk1` and prove the remaining obligations. Establish `h1 : Real.log s.x ≤ s.x ^ (1 : ℝ)`. Rewrite using `[Real.rpow_one]`.

Combine the linear relations using `[Real.log_le_sub_one_of_pos hxp]`. Rewrite using `[hsx]`. Use `(mul (mul hm (pos _).le le_rfl) (Real.log_nonneg hx.le) h1).trans (mono ?_)` and prove the remaining obligations. Combine the linear equalities and inequalities to obtain the conclusion. Use `le_trans ?_ (hk1.trans (le_mul_of_one_le_right (by linarith) hlk))` and prove the remaining obligations.

Use `(mul (mul le_rfl (by positivity) (pw 6 m0 hm)) L0 hL).trans (mono ?_)` and prove the remaining obligations. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Use `le_trans ?_ (hk1.trans (le_mul_of_one_le_right (by linarith) (one_le_pow₀ hlk)))` and prove the remaining obligations. Use `(mul_le_mul_of_nonneg_left hrd (by positivity)).trans ?_` and prove the remaining obligations.

Use `(mul (mul (mul le_rfl (by positivity) (pw 3 m0 hm)) L0 hL) L0 hL).trans (mono ?_)` and prove the remaining obligations. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Use `Real.le_sqrt_of_sq_le ?_` and prove the remaining obligations. Establish `h1 : R.m ≤ 2 * R.rS + 2`.

Take `⟨j, hj⟩` from `R.m_even`. Unfold `Ranks.rS`. Use linear arithmetic over natural numbers and integers. Establish `h2 : (R.m : ℝ) ≤ 2 * R.rS + 2` using `by exact_mod_cast h1`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1 : (R.m : ℝ) ≤ (R.m : ℝ) ^ 2` using `le_self_pow₀ (by linarith) (by norm_num)`. Establish `h2 : (R.m : ℝ) ^ 2 ≤ (R.m : ℝ) ^ 2 * s.L` using `le_mul_of_one_le_right (by positivity) hL1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1 : Real.log (Real.log s.b) ≤ s.L`. Unfold `Scale.b`.

Rewrite using `[Real.log_exp]`. Combine the linear relations using `[Real.log_le_sub_one_of_pos (show 0 < s.L by linarith)]`. Establish `h2 : (R.f : ℝ) ≤ R.r * R.f` using `le_mul_of_one_le_left f0 (by linarith)`. Establish `h3 : (R.r : ℝ) * R.f ≤ R.r * R.f * Real.log R.r` using `le_mul_of_one_le_right (by positivity) hlr`. Establish `h4` using `mul_le_mul_of_nonneg_left h1 (pos (s.eps / 100)).le`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `hthL.trans (le_mul_of_one_le_right f0 hlk)`. Rewrite using `[hfn]`. Conclude with `mul_le_mul_of_nonneg_right (le_trans h2m' (le_self_pow₀ (by linarith) (by norm_num))) n0`. Conclude with `(hfk.trans hkr').trans (le_self_pow₀ (by linarith) (by norm_num))`.
-/
theorem sizeKRel_of_rankVal {D : D7} (L : SizeData₂ D) (hR : RankVal L.sc D.R)
    (hK : 100 + 8 * |L.CGam| ≤ L.sc.x ^ (L.sc.eps / 1000)) (hrd : Real.log D.host.rdE ≤ L.sc.L) :
    SizeKRel L := by
  unfold SizeKRel szTh rankBudget
  generalize L.sc = s at *
  generalize L.CGam = c at *
  generalize Real.log D.host.rdE = ρ at *
  generalize D.R = R at *
  have hn2 := hR.n_le
  obtain ⟨⟨hn1, -⟩, ⟨hm1, hm2⟩, ⟨hk1, hk2⟩, -⟩ := hR
  have hx := s.one_lt_alt
  have hxp : 0 < s.x := lt_trans one_pos hx
  have e0 := s.eps_pos
  have e1 := s.eps_lt
  have hc0 := abs_nonneg c
  have hc1 := le_abs_self c
  have mono : ∀ {a b : ℝ}, a ≤ b → s.x ^ a ≤ s.x ^ b :=
    fun h => Real.rpow_le_rpow_of_exponent_le hx.le h
  have pos : ∀ a : ℝ, 0 < s.x ^ a := fun a => Real.rpow_pos_of_pos hxp a
  have one : ∀ {a : ℝ}, 0 ≤ a → 1 ≤ s.x ^ a := fun h => Real.one_le_rpow hx.le h
  have mul : ∀ {u v a b : ℝ}, u ≤ s.x ^ a → 0 ≤ v → v ≤ s.x ^ b → u * v ≤ s.x ^ (a + b) := by
    intro u v a b hu hv hv'
    rw [Real.rpow_add hxp]
    exact mul_le_mul hu hv' hv (pos _).le
  have mulL : ∀ {u v a b : ℝ}, s.x ^ a ≤ u → s.x ^ b ≤ v → s.x ^ (a + b) ≤ u * v := by
    intro u v a b hu hv
    rw [Real.rpow_add hxp]
    exact mul_le_mul hu hv (pos _).le ((pos _).le.trans hu)
  have pw : ∀ {u a : ℝ} (j : ℕ), 0 ≤ u → u ≤ s.x ^ a → u ^ j ≤ s.x ^ (a * j) := by
    intro u a j hu h
    rw [Real.rpow_mul_natCast hxp.le]
    exact pow_le_pow_left₀ hu h j
  have ab : ∀ {a C : ℝ}, C ≤ 100 → C * s.x ^ a ≤ s.x ^ (s.eps / 1000 + a) :=
    fun hC => mul (by linarith) (pos _).le le_rfl
  have hsq : Real.sqrt (s.x * s.delta1) = s.x ^ ((1 : ℝ) / 2 - s.eps / 16) := by
    have : s.x * s.delta1 = s.x ^ (1 + -(s.eps / 8)) := by
      rw [Real.rpow_add hxp, Real.rpow_one]; rfl
    rw [this, Real.sqrt_eq_rpow, ← Real.rpow_mul hxp.le]
    congr 1; ring
  rw [hsq] at hm1 hm2
  have h2m := R.two_le_m
  have hmk := R.m_add_three_le_k
  have hkr : R.k ≤ R.r := by unfold Ranks.r; omega
  have hkr' : (R.k : ℝ) ≤ R.r := by exact_mod_cast hkr
  have hfk : (R.f : ℝ) ≤ R.k := by exact_mod_cast R.f_le_k
  have hfn : (R.f : ℝ) = 2 * R.n := by unfold Ranks.f; push_cast; ring
  have h2m' : (2 : ℝ) ≤ R.m := by exact_mod_cast h2m
  have k5 : (5 : ℝ) ≤ R.k := by exact_mod_cast (by omega : 5 ≤ R.k)
  have n0 : (0 : ℝ) ≤ R.n := by positivity
  have f0 : (0 : ℝ) ≤ R.f := by positivity
  have m0 : (0 : ℝ) ≤ R.m := by positivity
  have hf : (R.f : ℝ) ≤ s.x ^ (s.eps / 1000 + (2 + 8 * s.eps + s.eps / 100)) := by
    have := ab (C := 4) (a := 2 + 8 * s.eps + s.eps / 100) (by norm_num)
    linarith
  have hf2 : s.x ^ (2 + 8 * s.eps) ≤ (R.f : ℝ) := by linarith
  have hk : (R.k : ℝ) ≤ s.x ^ (s.eps / 1000 + (9 / 2 + 10 * s.eps)) :=
    hk2.trans (ab (by norm_num))
  have hm : (R.m : ℝ) ≤ s.x ^ (s.eps / 1000 + (1 / 2 - s.eps / 16)) :=
    hm2.trans (ab (by norm_num))
  have hL : s.L ≤ s.x ^ s.eps := le_rfl
  have hL1 : 1 ≤ s.L := one e0.le
  have L0 : 0 ≤ s.L := by linarith
  have hlog : ∀ y : ℝ, 5 ≤ y → 1 ≤ Real.log y := by
    intro y hy
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hlk := hlog _ k5
  have hlr := hlog R.r (by linarith)
  have hsx : Real.sqrt s.x = s.x ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
  have hR0 : s.x ^ ((2 + 8 * s.eps) + -s.eps) ≤ (R.n : ℝ) * s.x ^ (-s.eps) := mulL hn1 le_rfl
  have hlf0 : 0 ≤ Real.log R.f := Real.log_natCast_nonneg _
  have hlf : Real.log R.f ≤ s.x ^ ((1 : ℝ) / 5) := by
    have h1 := Real.log_le_rpow_div f0 (show (0 : ℝ) < 1 / 30 by norm_num)
    have h2 : (R.f : ℝ) ^ ((1 : ℝ) / 30) ≤ s.x ^ ((1 : ℝ) / 10) := by
      calc (R.f : ℝ) ^ ((1 : ℝ) / 30) ≤ (s.x ^ (3 : ℝ)) ^ ((1 : ℝ) / 30) :=
            Real.rpow_le_rpow f0 (hf.trans (mono (by linarith))) (by norm_num)
        _ = _ := by rw [← Real.rpow_mul hxp.le]; norm_num
    have h3 := (ab (C := 30) (a := 1 / 10) (by norm_num)).trans (mono (b := 1 / 5) (by linarith))
    linarith
  have hlf2 : Real.log R.f ^ 2 ≤ s.x ^ ((2 : ℝ) / 5) :=
    (pw 2 hlf0 hlf).trans (mono (by norm_num))
  have hm4 : 4 * s.x ^ ((2 : ℝ) / 5) ≤ R.m :=
    ((ab (by norm_num)).trans (mono (by linarith))).trans hm1
  have h25 : 1 ≤ s.x ^ ((2 : ℝ) / 5) := one (by norm_num)
  have hthL : s.x ^ (s.eps / 100) * s.L ≤ R.f :=
    ((mul le_rfl L0 hL).trans (mono (by linarith))).trans hf2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine le_trans ?_ hk1
    refine (mul (mul (mul (mul le_rfl (by positivity) (pw 5 m0 hm)) f0 hf) L0 hL) (pos _).le le_rfl).trans (mono ?_)
    push_cast; linarith
  · refine le_trans ?_ hk1
    have h8 : 8 * c ≤ s.x ^ (s.eps / 1000) := by linarith
    refine (mul (mul (mul h8 (by positivity) (pw 5 m0 hm)) f0 hf) L0 hL).trans (mono ?_)
    push_cast; linarith
  · rw [hsx]
    refine hk.trans (le_trans (mono ?_) (mulL (mulL le_rfl hn1) hR0))
    linarith
  · rw [Real.sqrt_le_left (by positivity), div_le_iff₀ (by linarith), sq]
    refine hk.trans (le_trans (mono ?_) (mulL (mulL hR0 hR0) hm1))
    linarith
  · refine le_trans ?_ hk1
    refine (mul (pw 2 m0 hm) L0 hL).trans (mono ?_)
    push_cast; linarith
  · refine le_trans ?_ hk1
    have h1 : Real.log s.x ≤ s.x ^ (1 : ℝ) := by
      rw [Real.rpow_one]; linarith [Real.log_le_sub_one_of_pos hxp]
    rw [hsx]
    refine (mul (mul hm (pos _).le le_rfl) (Real.log_nonneg hx.le) h1).trans (mono ?_)
    linarith
  · refine le_trans ?_ (hk1.trans (le_mul_of_one_le_right (by linarith) hlk))
    refine (mul (mul le_rfl (by positivity) (pw 6 m0 hm)) L0 hL).trans (mono ?_)
    push_cast; linarith
  · refine le_trans ?_ (hk1.trans (le_mul_of_one_le_right (by linarith) (one_le_pow₀ hlk)))
    refine (mul_le_mul_of_nonneg_left hrd (by positivity)).trans ?_
    refine (mul (mul (mul le_rfl (by positivity) (pw 3 m0 hm)) L0 hL) L0 hL).trans (mono ?_)
    push_cast; linarith
  · refine Real.le_sqrt_of_sq_le ?_
    have h1 : R.m ≤ 2 * R.rS + 2 := by
      obtain ⟨j, hj⟩ := R.m_even
      unfold Ranks.rS; omega
    have h2 : (R.m : ℝ) ≤ 2 * R.rS + 2 := by exact_mod_cast h1
    linarith
  · have h1 : (R.m : ℝ) ≤ (R.m : ℝ) ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
    have h2 : (R.m : ℝ) ^ 2 ≤ (R.m : ℝ) ^ 2 * s.L := le_mul_of_one_le_right (by positivity) hL1
    linarith
  · have h1 : Real.log (Real.log s.b) ≤ s.L := by
      unfold Scale.b
      rw [Real.log_exp]
      linarith [Real.log_le_sub_one_of_pos (show 0 < s.L by linarith)]
    have h2 : (R.f : ℝ) ≤ R.r * R.f := le_mul_of_one_le_left f0 (by linarith)
    have h3 : (R.r : ℝ) * R.f ≤ R.r * R.f * Real.log R.r := le_mul_of_one_le_right (by positivity) hlr
    have h4 := mul_le_mul_of_nonneg_left h1 (pos (s.eps / 100)).le
    linarith
  · exact hthL.trans (le_mul_of_one_le_right f0 hlk)
  · rw [hfn]
    exact mul_le_mul_of_nonneg_right (le_trans h2m' (le_self_pow₀ (by linarith) (by norm_num))) n0
  · exact (hfk.trans hkr').trans (le_self_pow₀ (by linarith) (by norm_num))

/- English proof (translation)
Introduce `eps he0 he1 C hC`. Establish `hC8 : 1 ≤ C.P.Cpde` using `hC.2.2.2.2.2.2.2.2.2.2.2.2.1`. Take `⟨x1, hx1⟩` from `hostBounds eps C.P.Cpde he0 he1 hC8`. Use `⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max x1 ((100 + 8 * |C.CGam|) ^ (eps / 1000)⁻¹), ?_⟩⟩⟩` and prove the remaining obligations. Introduce `D L hLe hx hV`.

Use `sizeKRel_of_rankVal L hV.ranks ?_ ?_` and prove the remaining obligations. Rewrite using `[hV.CGam_eq, hLe]`. Establish `h0 : (0 : ℝ) ≤ 100 + 8 * |C.CGam|` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Conclude with `(hx1 L.sc D.R D.host hLe ((le_max_left _ _).trans hx) hV.ranks hV.host).2.2.2.2.2.2.2.1`.
-/
theorem szRow_sizeKRel : SzRow (fun _ _ L => SizeKRel L) := by
  intro eps he0 he1 C hC
  have hC8 : 1 ≤ C.P.Cpde := hC.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨x1, hx1⟩ := hostBounds eps C.P.Cpde he0 he1 hC8
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max x1 ((100 + 8 * |C.CGam|) ^ (eps / 1000)⁻¹), ?_⟩⟩⟩
  intro D L hLe hx hV
  refine sizeKRel_of_rankVal L hV.ranks ?_ ?_
  · rw [hV.CGam_eq, hLe]
    have h0 : (0 : ℝ) ≤ 100 + 8 * |C.CGam| := by positivity
    calc 100 + 8 * |C.CGam| = ((100 + 8 * |C.CGam|) ^ (eps / 1000)⁻¹) ^ (eps / 1000) :=
          (Real.rpow_inv_rpow h0 (by positivity)).symm
      _ ≤ _ := Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans hx) (by positivity)
  · exact (hx1 L.sc D.R D.host hLe ((le_max_left _ _).trans hx) hV.ranks hV.host).2.2.2.2.2.2.2.1

end GlobalTheory.EX
