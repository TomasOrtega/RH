import Development.AutomorphicArithmetic.ShortNorms.typePrimesN
import Development.AutomorphicArithmetic.ShortNorms.ExistsThreePrimesOneModLeRpow
import Development.AutomorphicArithmetic.CoprimeRanks.SecondSetNoRelation
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScale
import Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.HC GlobalTheory.EX UpperTheory.Top HostParam.Seam

/- English proof (translation)
Establish `hc : 0 < 1 / (4 * C)` using `by positivity`. Establish `h1` using `(isLittleO_log_rpow_atTop (show 0 < eps / 5 by positivity)).bound hc`. Take `⟨x₀, hx⟩` from `Filter.eventually_atTop.1 (h1.and (Filter.eventually_ge_atTop (1 : ℝ)))`. Use `⟨x₀, fun x hxx => ?_⟩` and prove the remaining obligations. Take `⟨ha, hb⟩` from `hx x hxx`.

Establish `hx0 : 0 < x` using `by linarith`. Establish `hl0 : 0 ≤ Real.log x` using `Real.log_nonneg hb`. Rewrite `ha` using `[Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _), abs_of_nonneg hl0]`. Establish `hu : 1 ≤ x ^ (eps / 5)` using `Real.one_le_rpow hb (by positivity)`. Establish `he5 : x ^ eps = (x ^ (eps / 5)) ^ 5`.

Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hx0.le]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[he5]`.

Generalize the expression as in `x ^ (eps / 5) = u at ha hu ⊢`. Generalize the expression as in `Real.log x = l at ha hl0 ⊢`. Establish `h2 : 4 * C * l ≤ u`. Use `mul_le_mul_of_nonneg_left ha (show 0 ≤ 4 * C by positivity)` as an intermediate fact. Rewrite `this` using `[← mul_assoc, mul_one_div_cancel (by positivity), one_mul]`. Then use the resulting hypothesis.

Establish `h3 : l ≤ u` using `by nlinarith`. Establish `h4 : 4 * C * l * l ≤ u * u` using `mul_le_mul h2 h3 hl0 (by linarith)`. Establish `h5 : u ^ 3 ≤ u ^ 5` using `pow_le_pow_right₀ hu (by norm_num)`. Establish `h6 : 0 < u ^ 3` using `by positivity`. Establish `h7` using `mul_le_mul_of_nonneg_left h4 (show 0 ≤ u by linarith)`.

Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem mod_small (C eps : ℝ) (hC : 1 ≤ C) (he : 0 < eps) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, 3 * x ^ (eps / 5) * Real.log x ^ 2 * C < x ^ eps := by
  have hc : 0 < 1 / (4 * C) := by positivity
  have h1 := (isLittleO_log_rpow_atTop (show 0 < eps / 5 by positivity)).bound hc
  obtain ⟨x₀, hx⟩ := Filter.eventually_atTop.1 (h1.and (Filter.eventually_ge_atTop (1 : ℝ)))
  refine ⟨x₀, fun x hxx => ?_⟩
  obtain ⟨ha, hb⟩ := hx x hxx
  have hx0 : 0 < x := by linarith
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hb
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _), abs_of_nonneg hl0] at ha
  have hu : 1 ≤ x ^ (eps / 5) := Real.one_le_rpow hb (by positivity)
  have he5 : x ^ eps = (x ^ (eps / 5)) ^ 5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
  rw [he5]
  generalize x ^ (eps / 5) = u at ha hu ⊢
  generalize Real.log x = l at ha hl0 ⊢
  have h2 : 4 * C * l ≤ u := by
    have := mul_le_mul_of_nonneg_left ha (show 0 ≤ 4 * C by positivity)
    rwa [← mul_assoc, mul_one_div_cancel (by positivity), one_mul] at this
  have h3 : l ≤ u := by nlinarith
  have h4 : 4 * C * l * l ≤ u * u := mul_le_mul h2 h3 hl0 (by linarith)
  have h5 : u ^ 3 ≤ u ^ 5 := pow_le_pow_right₀ hu (by norm_num)
  have h6 : 0 < u ^ 3 := by positivity
  have h7 := mul_le_mul_of_nonneg_left h4 (show 0 ≤ u by linarith)
  nlinarith

/- English proof (translation)
Introduce `hN hS`. Take `⟨C8, hC, hA⟩` from `UpperTheory.T3.exists_three_primes_one_mod_le_rpow hS`. Use `⟨C8, hC, fun eps he he' => ?_⟩` and prove the remaining obligations. Take `⟨x1, h1⟩` from `UpperTheory.T3.typePrimesN hN eps he`. Take `⟨x2, h2⟩` from `GlobalTheory.EX.rank_basic_bounds eps he he'`.

Take `⟨x3, h3⟩` from `mod_small C8 eps hC he`. Use `⟨max x1 (max x2 x3), fun s R N d hs hx hR hM => ?_⟩` and prove the remaining obligations. Take `⟨hx1, hx23⟩` from `max_le_iff.1 hx`. Take `⟨hx2, hx3⟩` from `max_le_iff.1 hx23`. Take `⟨-, -, hr5, hkr, -⟩` from `h2 s R hs hx2 hR`.

Establish `hk : 1 ≤ R.k` using `by have := R.m_add_three_le_k; omega`. Take `⟨g, hg, hg01, hgd⟩` from `h1 s.x hx1 N d R.k R.r hM hk (hk.trans hkr) hr5`. Take `⟨-, -, hd, hN0, hdN, hlog⟩` from `hM`. Establish `hN30 : 30 ≤ N` using `le_trans (by omega) (Nat.le_of_dvd hN0 hdN)`. Take `⟨p, p', q0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3⟩` from `hA N hN30`.

Establish `hb : s.b = Real.exp (s.x ^ eps)` using `by rw [← hs]; rfl`. Rewrite using `[hb]`. Establish `hNpos : (0 : ℝ) < N` using `by exact_mod_cast hN0`. Establish `hlt : (N : ℝ) ^ C8 < Real.exp (s.x ^ eps)`. Rewrite using `[Real.rpow_def_of_pos hNpos]`.

Conclude with `Real.exp_lt_exp.2 ((mul_le_mul_of_nonneg_right hlog (by linarith)).trans_lt (h3 s.x hx3))`. Establish `hb1 : 1 ≤ Real.exp (s.x ^ eps)` using `Real.one_le_exp (Real.rpow_nonneg (by linarith [s.one_lt_alt]) _)`. Establish `hk1 : (1 : ℝ) ≤ R.k` using `by exact_mod_cast hk`. Establish `hkb : Real.exp (s.x ^ eps) ≤ (R.k : ℝ) * Real.exp (s.x ^ eps)` using `le_mul_of_one_le_left (by linarith) hk1`. Establish `hY : Real.exp (s.x ^ eps) ≤ ((R.k : ℝ) * Real.exp (s.x ^ eps)) ^ 8` using `hkb.trans (le_self_pow₀ (hb1.trans hkb) (by norm_num))`.

Use `⟨g, p, p', q0, hg, hg01, hgd, a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3, fun i => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce `h`. Use `(hg i).2.1` as an intermediate fact. Rewrite `this` using `[← h]`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `h`. Use `(hg i).2.1` as an intermediate fact. Rewrite `this` using `[← h]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.T3.levelData :
    UpperTheory.T3.ShortNorm → UpperTheory.T3.SmallOne → ∃ C8 : ℝ, 1 ≤ C8 ∧ ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ,
      ∀ (s : Scale) (R : Ranks) (N d : ℕ), s.eps = eps → x0 ≤ s.x → RankVal s R → UpperTheory.T3.ModAt s.x eps N d →
      ∃ (g : Fin 2 → ℕ) (p p' q0 : ℕ), (∀ i, (g i).Prime ∧ ((R.k : ℝ) * s.b) ^ 8 ≤ (g i : ℝ) ∧ (g i : ℝ) ≤ 2 * ((R.k : ℝ) * s.b) ^ 8 ∧
          GlobalTheory.Mem.An.NormOne d N (g i)) ∧ g 0 ≠ g 1 ∧ Disjoint (Formalism.CyclotomicNorms.BB R.r (g 0)) (Formalism.CyclotomicNorms.BB R.r (g 1)) ∧
        p.Prime ∧ p'.Prime ∧ q0.Prime ∧ p ≠ p' ∧ q0 ≠ p ∧ q0 ≠ p' ∧ p % (15 * N) = 1 ∧ p' % (15 * N) = 1 ∧ q0 % N = 1 ∧
        (p : ℝ) ≤ (N : ℝ) ^ C8 ∧ (p' : ℝ) ≤ (N : ℝ) ^ C8 ∧ (q0 : ℝ) ≤ (N : ℝ) ^ C8 ∧ ∀ i, p ≠ g i ∧ p' ≠ g i := by
  intro hN hS
  obtain ⟨C8, hC, hA⟩ := UpperTheory.T3.exists_three_primes_one_mod_le_rpow hS
  refine ⟨C8, hC, fun eps he he' => ?_⟩
  obtain ⟨x1, h1⟩ := UpperTheory.T3.typePrimesN hN eps he
  obtain ⟨x2, h2⟩ := GlobalTheory.EX.rank_basic_bounds eps he he'
  obtain ⟨x3, h3⟩ := mod_small C8 eps hC he
  refine ⟨max x1 (max x2 x3), fun s R N d hs hx hR hM => ?_⟩
  obtain ⟨hx1, hx23⟩ := max_le_iff.1 hx
  obtain ⟨hx2, hx3⟩ := max_le_iff.1 hx23
  obtain ⟨-, -, hr5, hkr, -⟩ := h2 s R hs hx2 hR
  have hk : 1 ≤ R.k := by have := R.m_add_three_le_k; omega
  obtain ⟨g, hg, hg01, hgd⟩ := h1 s.x hx1 N d R.k R.r hM hk (hk.trans hkr) hr5
  obtain ⟨-, -, hd, hN0, hdN, hlog⟩ := hM
  have hN30 : 30 ≤ N := le_trans (by omega) (Nat.le_of_dvd hN0 hdN)
  obtain ⟨p, p', q0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3⟩ := hA N hN30
  have hb : s.b = Real.exp (s.x ^ eps) := by rw [← hs]; rfl
  rw [hb]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hlt : (N : ℝ) ^ C8 < Real.exp (s.x ^ eps) := by
    rw [Real.rpow_def_of_pos hNpos]
    exact Real.exp_lt_exp.2 ((mul_le_mul_of_nonneg_right hlog (by linarith)).trans_lt (h3 s.x hx3))
  have hb1 : 1 ≤ Real.exp (s.x ^ eps) := Real.one_le_exp (Real.rpow_nonneg (by linarith [s.one_lt_alt]) _)
  have hk1 : (1 : ℝ) ≤ R.k := by exact_mod_cast hk
  have hkb : Real.exp (s.x ^ eps) ≤ (R.k : ℝ) * Real.exp (s.x ^ eps) := le_mul_of_one_le_left (by linarith) hk1
  have hY : Real.exp (s.x ^ eps) ≤ ((R.k : ℝ) * Real.exp (s.x ^ eps)) ^ 8 :=
    hkb.trans (le_self_pow₀ (hb1.trans hkb) (by norm_num))
  refine ⟨g, p, p', q0, hg, hg01, hgd, a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3, fun i => ⟨?_, ?_⟩⟩
  · intro h
    have := (hg i).2.1
    rw [← h] at this
    linarith
  · intro h
    have := (hg i).2.1
    rw [← h] at this
    linarith
