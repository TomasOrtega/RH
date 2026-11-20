import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogAddRpowMulLogPowLeRpow

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

/- English proof (translation)
Take `⟨x1, h1⟩` from `GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (1 / 4) 0 36 (1 / 2) 2 le_rfl (by norm_num) (by norm_num)`. Use `⟨max x1 (Real.exp 1), fun s R hx hR => ?_⟩` and prove the remaining obligations. Establish `hn` using `hR.n_le'`. Take `⟨-, ⟨hm, -⟩, -, -⟩` from `hR`. Establish `hx1` using `h1 s.x (le_trans (le_max_left _ _) hx)`.

Establish `hxe : Real.exp 1 ≤ s.x` using `le_trans (le_max_right _ _) hx`. Establish `h1x` using `s.one_lt_alt`. Establish `hx0 : 0 < s.x` using `by linarith`. Establish `he` using `s.eps_lt`. Establish `he0` using `s.eps_pos`.

Establish `hl : 1 ≤ Real.log s.x`. Rewrite using `[Real.le_log_iff_exp_le hx0]`. Conclude with `hxe`. Rewrite `hx1` using `[Real.rpow_zero]`. Establish `hm' : s.x ^ (1 / 4 : ℝ) ≤ (R.m : ℝ)`.

Use `le_trans ?_ hm` and prove the remaining obligations. Apply `Real.le_sqrt_of_sq_le` to reduce the goal to its premises. Unfold `Scale.delta1`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hx0.le]`. Establish `: s.x * s.x ^ (-(s.eps / 8)) = s.x ^ (1 + -(s.eps / 8))`.

Rewrite using `[Real.rpow_add hx0, Real.rpow_one]`. Rewrite using `[this]`. Apply `Real.rpow_le_rpow_of_exponent_le h1x.le` to reduce the goal to its premises. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hf1 : 1 ≤ R.f`. Establish `: 0 < R.ord` using `R.ord_pos`. Unfold `Ranks.f Ranks.n`. Use linear arithmetic over natural numbers and integers. Establish `hf1' : (1 : ℝ) ≤ R.f` using `by exact_mod_cast hf1`.

Establish `hf : (R.f : ℝ) ≤ 4 * s.x ^ (3 : ℝ)`. Establish `: s.x ^ ((9 : ℝ) / 4) ≤ s.x ^ (3 : ℝ)` using `Real.rpow_le_rpow_of_exponent_le h1x.le (by norm_num)`. Unfold `Ranks.f`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hlf : Real.log R.f ≤ 6 * Real.log s.x`. Establish `h2` using `Real.log_le_log (by linarith) hf`. Rewrite `h2` using `[Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx0]`. Establish `h4 : Real.log 4 ≤ 4 - 1` using `Real.log_le_sub_one_of_pos (by norm_num)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hlf0 : 0 ≤ Real.log R.f` using `Real.log_nonneg hf1'`. Establish `hsq : Real.log R.f ^ 2 ≤ (6 * Real.log s.x) ^ 2` using `pow_le_pow_left₀ hlf0 hlf 2`. Establish `hr : R.m ≤ 2 * R.rS + 3` using `by unfold Ranks.rS; omega`. Establish `hr' : (R.m : ℝ) ≤ 2 * R.rS + 3` using `by exact_mod_cast hr`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem logf_sq_le_rS : ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), x0 ≤ s.x → RankVal s R →
    Real.log R.f ^ 2 ≤ (R.rS : ℝ) := by
  obtain ⟨x1, h1⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (1 / 4) 0 36 (1 / 2) 2 le_rfl (by norm_num) (by norm_num)
  refine ⟨max x1 (Real.exp 1), fun s R hx hR => ?_⟩
  have hn := hR.n_le'
  obtain ⟨-, ⟨hm, -⟩, -, -⟩ := hR
  have hx1 := h1 s.x (le_trans (le_max_left _ _) hx)
  have hxe : Real.exp 1 ≤ s.x := le_trans (le_max_right _ _) hx
  have h1x := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have he := s.eps_lt
  have he0 := s.eps_pos
  have hl : 1 ≤ Real.log s.x := by
    rw [Real.le_log_iff_exp_le hx0]; exact hxe
  rw [Real.rpow_zero] at hx1
  have hm' : s.x ^ (1 / 4 : ℝ) ≤ (R.m : ℝ) := by
    refine le_trans ?_ hm
    apply Real.le_sqrt_of_sq_le
    unfold Scale.delta1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    have : s.x * s.x ^ (-(s.eps / 8)) = s.x ^ (1 + -(s.eps / 8)) := by
      rw [Real.rpow_add hx0, Real.rpow_one]
    rw [this]
    apply Real.rpow_le_rpow_of_exponent_le h1x.le
    push_cast
    linarith
  have hf1 : 1 ≤ R.f := by
    have : 0 < R.ord := R.ord_pos
    unfold Ranks.f Ranks.n; omega
  have hf1' : (1 : ℝ) ≤ R.f := by exact_mod_cast hf1
  have hf : (R.f : ℝ) ≤ 4 * s.x ^ (3 : ℝ) := by
    have : s.x ^ ((9 : ℝ) / 4) ≤ s.x ^ (3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h1x.le (by norm_num)
    unfold Ranks.f
    push_cast
    linarith
  have hlf : Real.log R.f ≤ 6 * Real.log s.x := by
    have h2 := Real.log_le_log (by linarith) hf
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx0] at h2
    have h4 : Real.log 4 ≤ 4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hlf0 : 0 ≤ Real.log R.f := Real.log_nonneg hf1'
  have hsq : Real.log R.f ^ 2 ≤ (6 * Real.log s.x) ^ 2 := pow_le_pow_left₀ hlf0 hlf 2
  have hr : R.m ≤ 2 * R.rS + 3 := by unfold Ranks.rS; omega
  have hr' : (R.m : ℝ) ≤ 2 * R.rS + 3 := by exact_mod_cast hr
  nlinarith

/- English proof (translation)
Introduce `eps _ _ C hC`. Take `⟨x1, h1⟩` from `logf_sq_le_rS`. Use `⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max x1 C.P.cLL⁻¹, fun D L _ hx hV => ?_⟩⟩⟩` and prove the remaining obligations. Establish `hsq` using `h1 L.sc D.R (le_trans (le_max_left _ _) hx) hV.ranks`. Establish `hxc : C.P.cLL⁻¹ ≤ L.sc.x` using `le_trans (le_max_right _ _) hx`.

Establish `hc1 : 1 ≤ C.P.cLL⁻¹` using `hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (by simp [FC.cLast])`. Establish `hc0 : 0 < C.P.cLL` using `inv_pos.mp (by linarith)`. Establish `hW : C.P.CnW = 10` using `hC.1.2.2.2.2.2.2.2.1`. Take `⟨-, -, ⟨hk, -⟩, -⟩` from `hV.ranks`. Establish `h1x` using `L.sc.one_lt_alt`.

Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `he` using `L.sc.eps_lt`. Establish `he0` using `L.sc.eps_pos`. Establish `hm2` using `D.R.two_le_m`. Establish `hmk` using `D.R.m_add_three_le_k`.

Establish `hf2 : 2 ≤ D.R.f`. Establish `: 0 < D.R.ord` using `D.R.ord_pos`. Unfold `Ranks.f Ranks.n`. Use linear arithmetic over natural numbers and integers. Establish `hf2' : (2 : ℝ) ≤ D.R.f` using `by exact_mod_cast hf2`.

Establish `hL : 1 ≤ L.sc.L` using `Real.one_le_rpow h1x.le he0.le`. Establish `hm2' : (2 : ℝ) ≤ D.R.m` using `by exact_mod_cast hm2`. Use `⟨Real.le_sqrt_of_sq_le hsq, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hr : D.R.rS ≤ D.R.m` using `by unfold Ranks.rS; omega`. Establish `hr' : (D.R.rS : ℝ) ≤ D.R.m` using `by exact_mod_cast hr`.

Establish `h2 : (D.R.m : ℝ) ≤ (D.R.m : ℝ) ^ 2` using `by nlinarith`. Establish `h3 : (D.R.m : ℝ) ^ 2 ≤ (D.R.m : ℝ) ^ 2 * L.sc.L` using `le_mul_of_one_le_right (by positivity) hL`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hkr : D.R.k ≤ D.R.r` using `by unfold Ranks.r; omega`. Establish `hkr' : (D.R.k : ℝ) ≤ D.R.r` using `by exact_mod_cast hkr`.

Establish `hxk : L.sc.x ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps)` using `by conv_lhs => rw [← Real.rpow_one L.sc.x]`. Conclude with `Real.rpow_le_rpow_of_exponent_le h1x.le (by linarith)`. Establish `hxr : L.sc.x ≤ D.R.r` using `by linarith`. Establish `hl0 : 0 ≤ Real.log L.sc.x` using `Real.log_nonneg h1x.le`. Establish `hlr : Real.log L.sc.x ≤ Real.log D.R.r` using `Real.log_le_log hx0 hxr`.

Establish `hb : Real.log (Real.log L.sc.b) = L.sc.eps * Real.log L.sc.x`. Unfold `Scale.b Scale.L`. Rewrite using `[Real.log_exp, Real.log_rpow hx0]`. Establish `hcr : 1 ≤ C.P.cLL * D.R.r`. Use `mul_le_mul_of_nonneg_left (le_trans hxc hxr) hc0.le` as an intermediate fact.

Rewrite `this` using `[mul_inv_cancel₀ hc0.ne']`. Then use the resulting hypothesis. Establish `hcrf : 1 ≤ C.P.cLL * D.R.r * D.R.f` using `by nlinarith`. Establish `h3 : Real.log D.R.r ≤ C.P.cLL * D.R.r * D.R.f * Real.log D.R.r` using `le_mul_of_one_le_left (by linarith) hcrf`. Rewrite using `[hb]`. Use the polynomial consequences of the given equalities and inequalities.

Unfold `nW`. Rewrite using `[hW]`. Establish `hk1 : (1 : ℝ) ≤ D.R.k` using `by exact_mod_cast (by omega : 1 ≤ D.R.k)`. Establish `hk0 : (0 : ℝ) ≤ (D.R.k : ℝ) - 1` using `by linarith`. Establish `h2 : 0 ≤ (D.R.f : ℝ) ^ 2 * ((D.R.k : ℝ) - 1) ^ 3 * L.sc.L ^ 2 / D.R.m` using `by positivity`.

Establish `hr0 : (0 : ℝ) ≤ D.R.r` using `by positivity`. Use polynomial arithmetic with `[mul_nonneg hr0 h2, mul_nonneg hr0 (sub_nonneg.mpr hf2')]`.
-/
theorem szRow_logf : SzRow (fun C D L => (Real.log D.R.f ≤ Real.sqrt D.R.rS) ∧
    (Real.log D.R.f ^ 2 ≤ (D.R.m : ℝ) ^ 2 * L.sc.L) ∧
    (Real.log (Real.log L.sc.b) ≤ C.P.cLL * D.R.r * D.R.f * Real.log D.R.r) ∧
    ((4 * (D.R.f : ℝ) + 10) * D.R.r ≤ nW L C.P.CnW)) := by
  intro eps _ _ C hC
  obtain ⟨x1, h1⟩ := logf_sq_le_rS
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max x1 C.P.cLL⁻¹, fun D L _ hx hV => ?_⟩⟩⟩
  have hsq := h1 L.sc D.R (le_trans (le_max_left _ _) hx) hV.ranks
  have hxc : C.P.cLL⁻¹ ≤ L.sc.x := le_trans (le_max_right _ _) hx
  have hc1 : 1 ≤ C.P.cLL⁻¹ := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (by simp [FC.cLast])
  have hc0 : 0 < C.P.cLL := inv_pos.mp (by linarith)
  have hW : C.P.CnW = 10 := hC.1.2.2.2.2.2.2.2.1
  obtain ⟨-, -, ⟨hk, -⟩, -⟩ := hV.ranks
  have h1x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have he := L.sc.eps_lt
  have he0 := L.sc.eps_pos
  have hm2 := D.R.two_le_m
  have hmk := D.R.m_add_three_le_k
  have hf2 : 2 ≤ D.R.f := by
    have : 0 < D.R.ord := D.R.ord_pos
    unfold Ranks.f Ranks.n; omega
  have hf2' : (2 : ℝ) ≤ D.R.f := by exact_mod_cast hf2
  have hL : 1 ≤ L.sc.L := Real.one_le_rpow h1x.le he0.le
  have hm2' : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
  refine ⟨Real.le_sqrt_of_sq_le hsq, ?_, ?_, ?_⟩
  · have hr : D.R.rS ≤ D.R.m := by unfold Ranks.rS; omega
    have hr' : (D.R.rS : ℝ) ≤ D.R.m := by exact_mod_cast hr
    have h2 : (D.R.m : ℝ) ≤ (D.R.m : ℝ) ^ 2 := by nlinarith
    have h3 : (D.R.m : ℝ) ^ 2 ≤ (D.R.m : ℝ) ^ 2 * L.sc.L := le_mul_of_one_le_right (by positivity) hL
    linarith
  · have hkr : D.R.k ≤ D.R.r := by unfold Ranks.r; omega
    have hkr' : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast hkr
    have hxk : L.sc.x ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps) := by
      conv_lhs => rw [← Real.rpow_one L.sc.x]
      exact Real.rpow_le_rpow_of_exponent_le h1x.le (by linarith)
    have hxr : L.sc.x ≤ D.R.r := by linarith
    have hl0 : 0 ≤ Real.log L.sc.x := Real.log_nonneg h1x.le
    have hlr : Real.log L.sc.x ≤ Real.log D.R.r := Real.log_le_log hx0 hxr
    have hb : Real.log (Real.log L.sc.b) = L.sc.eps * Real.log L.sc.x := by
      unfold Scale.b Scale.L
      rw [Real.log_exp, Real.log_rpow hx0]
    have hcr : 1 ≤ C.P.cLL * D.R.r := by
      have := mul_le_mul_of_nonneg_left (le_trans hxc hxr) hc0.le
      rwa [mul_inv_cancel₀ hc0.ne'] at this
    have hcrf : 1 ≤ C.P.cLL * D.R.r * D.R.f := by nlinarith
    have h3 : Real.log D.R.r ≤ C.P.cLL * D.R.r * D.R.f * Real.log D.R.r :=
      le_mul_of_one_le_left (by linarith) hcrf
    rw [hb]
    nlinarith
  · unfold nW
    rw [hW]
    have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
    have hk0 : (0 : ℝ) ≤ (D.R.k : ℝ) - 1 := by linarith
    have h2 : 0 ≤ (D.R.f : ℝ) ^ 2 * ((D.R.k : ℝ) - 1) ^ 3 * L.sc.L ^ 2 / D.R.m := by positivity
    have hr0 : (0 : ℝ) ≤ D.R.r := by positivity
    nlinarith [mul_nonneg hr0 h2, mul_nonneg hr0 (sub_nonneg.mpr hf2')]

end GlobalTheory.EX
