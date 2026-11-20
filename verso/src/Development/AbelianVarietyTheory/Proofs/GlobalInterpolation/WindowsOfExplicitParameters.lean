import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparisonStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScaleStatement
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.HostTorsionOrderLe

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨x1, h1⟩` from `GlobalTheory.T.scale_polynomial_quantities_comparison eps (ch + 2) (1 / 2) he (by norm_num)`. Take `⟨x2, h2⟩` from `GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he he'`. Use `⟨max 6 (max x1 x2), fun s R hs hx hR => ?_⟩` and prove the remaining obligations. Establish `hx6 : 6 ≤ s.x` using `le_trans (le_max_left _ _) hx`. Establish `hx1 : x1 ≤ s.x` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx`.

Establish `hx2 : x2 ≤ s.x` using `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx`. Take `⟨-, -, -, hb', -, hw, -⟩` from `h1 s hs hx1`. Take `⟨hf, hm, hr, hkr, -, -, -, -, -, -, -, -, -, ht, hN, -, -⟩` from `h2 s R hs hx2 hR`. Establish `hx0 : 0 < s.x` using `by linarith`. Establish `hxo : 1 ≤ s.x` using `by linarith`.

Establish `hbpos : 0 < s.b` using `Real.exp_pos _`. Establish `hb1 : 1 ≤ s.b` using `Real.one_le_exp (Real.rpow_nonneg hx0.le _)`. Establish `hb'pos : 0 < s.b'` using `div_pos (mul_pos hx0 hbpos) (Real.exp_pos _)`. Establish `hP1 : 1 ≤ s.x ^ ch` using `Real.one_le_rpow hxo (by linarith)`. Establish `hP5 : s.x ^ (5 : ℝ) ≤ s.x ^ ch` using `Real.rpow_le_rpow_of_exponent_le hxo (by linarith)`.

Establish `hPe : s.x ^ (ch + 2) = s.x ^ ch * (s.x * s.x)`. Rewrite using `[Real.rpow_add hx0, Real.rpow_two, sq]`. Take `⟨hw1, -, -⟩` from `hw 1 le_rfl (by`. Simplify using `using Real.one_le_rpow hxo (show (0 : ℝ) ≤ 3 by norm_num))`. Establish `hbh : 1 ≤ s.b ^ (1 - 1 / 2 : ℝ)` using `Real.one_le_rpow hb1 (by norm_num)`.

Establish `hw2 : s.x ^ ch * (s.x * s.x) ≤ s.b' / s.x`. Establish `e1 : s.w'' 1 = s.b' / s.x` using `by simp [Scale.w'']`. Rewrite `hw1` using `[e1, hPe]`. Establish `: 0 ≤ s.x ^ ch * (s.x * s.x)` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hxx : 36 ≤ s.x * s.x` using `by nlinarith`. Establish `hdiv : s.b' / s.x ≤ s.b'` using `div_le_self hb'pos.le hxo`. Establish `hbb : s.b' ≤ s.b`. Rewrite `hb'` using `[hPe]`. Establish `: 1 ≤ s.x ^ ch * (s.x * s.x)` using `by nlinarith`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hk : (R.k : ℝ) ≤ s.x ^ ch`. Establish `: (R.k : ℝ) ≤ R.r` using `by exact_mod_cast hkr`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hh : (h0v s ch : ℝ) ≤ 4 * s.x ^ ch`.

Use `Nat.ceil_lt_add_one (show 0 ≤ s.x ^ ch by linarith)` as an intermediate fact. Unfold `h0v`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨by nlinarith, ?_, hbb, by nlinarith, ht, ?_⟩` and prove the remaining obligations.

Establish `a1 : (R.m : ℝ) * (h0v s ch : ℝ) ≤ s.x * (4 * s.x ^ ch)` using `mul_le_mul hm hh (Nat.cast_nonneg _) hx0.le`. Establish `a2 : s.x * (4 * s.x ^ ch) ≤ s.x ^ ch * (s.x * s.x)`. Establish `: 0 ≤ s.x ^ ch * s.x * (s.x - 4)`. Apply `mul_nonneg (by positivity) (by linarith)` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn : (R.n : ℝ) ≤ s.x ^ (3 : ℝ)`. Establish `: (R.n : ℝ) ≤ R.f`. Establish `: R.n ≤ R.f` using `by unfold Ranks.f; omega`. Conclude with `this` after adjusting the coercions.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hm1 : (1 : ℝ) ≤ R.m`. Use `R.two_le_m` as an intermediate fact. Conclude with `(by omega : 1 ≤ R.m)` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation.
-/
theorem windows_scale_facts (eps ch : ℝ) (he : 0 < eps) (he' : eps < 1 / 52) (hch : 402 ≤ ch) :
    ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R →
      (R.k : ℝ) + 5 ≤ s.b' / s.x ∧ (R.m : ℝ) * (h0v s ch : ℝ) ≤ s.b ∧ s.b' ≤ s.b ∧ 6 ≤ s.b ∧
      (R.t : ℝ) ≤ s.x ^ (401 : ℝ) ∧ (R.n : ℝ) * R.N R.m / R.m ≤ s.x ^ (405 : ℝ) := by
  obtain ⟨x1, h1⟩ := GlobalTheory.T.scale_polynomial_quantities_comparison eps (ch + 2) (1 / 2) he (by norm_num)
  obtain ⟨x2, h2⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he he'
  refine ⟨max 6 (max x1 x2), fun s R hs hx hR => ?_⟩
  have hx6 : 6 ≤ s.x := le_trans (le_max_left _ _) hx
  have hx1 : x1 ≤ s.x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx2 : x2 ≤ s.x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨-, -, -, hb', -, hw, -⟩ := h1 s hs hx1
  obtain ⟨hf, hm, hr, hkr, -, -, -, -, -, -, -, -, -, ht, hN, -, -⟩ := h2 s R hs hx2 hR
  have hx0 : 0 < s.x := by linarith
  have hxo : 1 ≤ s.x := by linarith
  have hbpos : 0 < s.b := Real.exp_pos _
  have hb1 : 1 ≤ s.b := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have hb'pos : 0 < s.b' := div_pos (mul_pos hx0 hbpos) (Real.exp_pos _)
  have hP1 : 1 ≤ s.x ^ ch := Real.one_le_rpow hxo (by linarith)
  have hP5 : s.x ^ (5 : ℝ) ≤ s.x ^ ch := Real.rpow_le_rpow_of_exponent_le hxo (by linarith)
  have hPe : s.x ^ (ch + 2) = s.x ^ ch * (s.x * s.x) := by
    rw [Real.rpow_add hx0, Real.rpow_two, sq]
  obtain ⟨hw1, -, -⟩ := hw 1 le_rfl (by
    simpa using Real.one_le_rpow hxo (show (0 : ℝ) ≤ 3 by norm_num))
  have hbh : 1 ≤ s.b ^ (1 - 1 / 2 : ℝ) := Real.one_le_rpow hb1 (by norm_num)
  have hw2 : s.x ^ ch * (s.x * s.x) ≤ s.b' / s.x := by
    have e1 : s.w'' 1 = s.b' / s.x := by simp [Scale.w'']
    rw [e1, hPe] at hw1
    have : 0 ≤ s.x ^ ch * (s.x * s.x) := by positivity
    nlinarith
  have hxx : 36 ≤ s.x * s.x := by nlinarith
  have hdiv : s.b' / s.x ≤ s.b' := div_le_self hb'pos.le hxo
  have hbb : s.b' ≤ s.b := by
    rw [hPe] at hb'
    have : 1 ≤ s.x ^ ch * (s.x * s.x) := by nlinarith
    nlinarith
  have hk : (R.k : ℝ) ≤ s.x ^ ch := by
    have : (R.k : ℝ) ≤ R.r := by exact_mod_cast hkr
    linarith
  have hh : (h0v s ch : ℝ) ≤ 4 * s.x ^ ch := by
    have := Nat.ceil_lt_add_one (show 0 ≤ s.x ^ ch by linarith)
    unfold h0v
    push_cast
    linarith
  refine ⟨by nlinarith, ?_, hbb, by nlinarith, ht, ?_⟩
  · have a1 : (R.m : ℝ) * (h0v s ch : ℝ) ≤ s.x * (4 * s.x ^ ch) :=
      mul_le_mul hm hh (Nat.cast_nonneg _) hx0.le
    have a2 : s.x * (4 * s.x ^ ch) ≤ s.x ^ ch * (s.x * s.x) := by
      have : 0 ≤ s.x ^ ch * s.x * (s.x - 4) := by
        apply mul_nonneg (by positivity) (by linarith)
      nlinarith
    linarith
  · have hn : (R.n : ℝ) ≤ s.x ^ (3 : ℝ) := by
      have : (R.n : ℝ) ≤ R.f := by
        have : R.n ≤ R.f := by unfold Ranks.f; omega
        exact_mod_cast this
      linarith
    have hm1 : (1 : ℝ) ≤ R.m := by
      have := R.two_le_m
      exact_mod_cast (by omega : 1 ≤ R.m)
    calc (R.n : ℝ) * R.N R.m / R.m ≤ (R.n : ℝ) * R.N R.m := div_le_self (by positivity) hm1
      _ ≤ s.x ^ (3 : ℝ) * s.x ^ (402 : ℝ) :=
        mul_le_mul hn hN (Nat.cast_nonneg _) (by positivity)
      _ = s.x ^ (405 : ℝ) := by rw [← Real.rpow_add hx0]; norm_num

/- English proof (translation)
Establish `hx` using `s.one_lt_alt`. Establish `hx0 : 0 < s.x` using `by linarith`. Establish `hl : 0 ≤ Real.log s.x` using `Real.log_nonneg hx.le`. Establish `h5 : 1 ≤ Real.log 5`. Rewrite using `[Real.le_log_iff_exp_le (by norm_num)]`.

Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `key : Real.logb 5 y ≤ 405 * Real.log s.x`. Establish `a1 : Real.log y ≤ 405 * Real.log s.x`. Break down `hy0.eq_or_lt with h | h` into its components or cases.

Rewrite using `[← h, Real.log_zero]`. Check the signs of the components of the expression. Rewrite using `[← Real.log_rpow hx0]`. Conclude with `Real.log_le_log h hy`. Unfold `Real.logb`.

Rewrite using `[div_le_iff₀ (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities. Use `Nat.ceil_mono key` as an intermediate fact. Unfold `Lwv`. Use linear arithmetic over natural numbers and integers.
-/
theorem ten_ceil_logb_le_Lwv (s : Scale) (y : ℝ) (hy0 : 0 ≤ y) (hy : y ≤ s.x ^ (405 : ℝ)) :
    10 * ⌈Real.logb 5 y⌉₊ + 20 ≤ Lwv s := by
  have hx := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have hl : 0 ≤ Real.log s.x := Real.log_nonneg hx.le
  have h5 : 1 ≤ Real.log 5 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have key : Real.logb 5 y ≤ 405 * Real.log s.x := by
    have a1 : Real.log y ≤ 405 * Real.log s.x := by
      rcases hy0.eq_or_lt with h | h
      · rw [← h, Real.log_zero]; positivity
      · rw [← Real.log_rpow hx0]; exact Real.log_le_log h hy
    unfold Real.logb
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have := Nat.ceil_mono key
  unfold Lwv
  omega

/- English proof (translation)
Take `⟨x2, h2⟩` from `GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he he'`. Use `⟨max 8 x2, fun s R H hs hx hR => ?_⟩` and prove the remaining obligations. Establish `hx8 : 8 ≤ s.x` using `le_trans (le_max_left _ _) hx`. Establish `hx2 : x2 ≤ s.x` using `le_trans (le_max_right _ _) hx`. Establish `hf : (R.f : ℝ) ≤ s.x ^ (3 : ℝ)` using `(h2 s R hs hx2 hR).1`.

Establish `hx0 : 0 < s.x` using `by linarith`. Establish `hxo : 1 ≤ s.x` using `by linarith`. Establish `hw : (Units.torsionOrder H.E : ℝ) ≤ 8 * (R.f : ℝ) ^ 2`. Conclude with `UpperTheory.Mu.host_torsionOrder_le H` after adjusting the coercions. Establish `h7 : s.x ^ (7 : ℝ) = s.x * (s.x ^ (3 : ℝ)) ^ 2`.

Rewrite using `[sq, ← Real.rpow_add hx0, show (7 : ℝ) = 1 + (3 + 3) by norm_num, Real.rpow_add hx0 1, Real.rpow_one]`. Establish `h7c : s.x ^ (7 : ℝ) ≤ s.x ^ ch` using `Real.rpow_le_rpow_of_exponent_le hxo (by linarith)`. Establish `hf2 : (R.f : ℝ) ^ 2 ≤ (s.x ^ (3 : ℝ)) ^ 2` using `pow_le_pow_left₀ (Nat.cast_nonneg _) hf 2`. Establish `h8 : 8 * (s.x ^ (3 : ℝ)) ^ 2 ≤ s.x * (s.x ^ (3 : ℝ)) ^ 2` using `mul_le_mul_of_nonneg_right hx8 (sq_nonneg _)`. Establish `hc` using `Nat.le_ceil (s.x ^ ch)`.

Establish `e : (h0v s ch : ℝ) / 2 = (⌈s.x ^ ch⌉₊ : ℝ)`. Unfold `h0v`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `hw.trans ((mul_le_mul_of_nonneg_left hf2 (by norm_num)).trans (h8.trans (h7.symm.le.trans (h7c.trans hc))))`.
-/
private theorem torsionOrder_le_half_gap (eps ch : ℝ) (he : 0 < eps) (he' : eps < 1 / 52) (hch : 402 ≤ ch) :
    ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (H : Host R), s.eps = eps → x0 ≤ s.x → RankVal s R →
      (Units.torsionOrder H.E : ℝ) ≤ (h0v s ch : ℝ) / 2 := by
  obtain ⟨x2, h2⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he he'
  refine ⟨max 8 x2, fun s R H hs hx hR => ?_⟩
  have hx8 : 8 ≤ s.x := le_trans (le_max_left _ _) hx
  have hx2 : x2 ≤ s.x := le_trans (le_max_right _ _) hx
  have hf : (R.f : ℝ) ≤ s.x ^ (3 : ℝ) := (h2 s R hs hx2 hR).1
  have hx0 : 0 < s.x := by linarith
  have hxo : 1 ≤ s.x := by linarith
  have hw : (Units.torsionOrder H.E : ℝ) ≤ 8 * (R.f : ℝ) ^ 2 := by
    exact_mod_cast UpperTheory.Mu.host_torsionOrder_le H
  have h7 : s.x ^ (7 : ℝ) = s.x * (s.x ^ (3 : ℝ)) ^ 2 := by
    rw [sq, ← Real.rpow_add hx0, show (7 : ℝ) = 1 + (3 + 3) by norm_num, Real.rpow_add hx0 1, Real.rpow_one]
  have h7c : s.x ^ (7 : ℝ) ≤ s.x ^ ch := Real.rpow_le_rpow_of_exponent_le hxo (by linarith)
  have hf2 : (R.f : ℝ) ^ 2 ≤ (s.x ^ (3 : ℝ)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hf 2
  have h8 : 8 * (s.x ^ (3 : ℝ)) ^ 2 ≤ s.x * (s.x ^ (3 : ℝ)) ^ 2 :=
    mul_le_mul_of_nonneg_right hx8 (sq_nonneg _)
  have hc := Nat.le_ceil (s.x ^ ch)
  have e : (h0v s ch : ℝ) / 2 = (⌈s.x ^ ch⌉₊ : ℝ) := by
    unfold h0v
    push_cast
    ring
  rw [e]
  exact hw.trans ((mul_le_mul_of_nonneg_left hf2 (by norm_num)).trans
    (h8.trans (h7.symm.le.trans (h7c.trans hc))))

/- English proof (translation)
Introduce `eps cD ch C8 he he' hcD hch`. Take `⟨x0, hx0⟩` from `windows_scale_facts eps ch he he' hch`. Take `⟨x1, hx1'⟩` from `torsionOrder_le_half_gap eps ch he he' hch`. Use `⟨max x0 x1, fun s D bT hs hx hR hH hbT hC => ?_⟩` and prove the remaining obligations. Take `⟨hk5, hη, hbb, hb6, ht, hnN⟩` from `hx0 s D.R hs (le_trans (le_max_left _ _) hx) hR`.

Establish `htor` using `hx1' s D.R D.host hs (le_trans (le_max_right _ _) hx) hR`. Take `⟨hv, hu, ⟨b1, hbe, htop, hthick, hthin⟩, -⟩` from `hC`. Take `⟨-, -, hT2, -, -, hLw, -, -⟩` from `hH`. Introduce `η S`. Establish `hx1` using `s.one_lt_alt`.

Establish `hxp : 0 < s.x` using `by linarith`. Establish `hb'pos : 0 < s.b'` using `div_pos (mul_pos hxp (Real.exp_pos _)) (Real.exp_pos _)`. Establish `hdiv : s.b' / s.x ≤ s.b'` using `div_le_self hb'pos.le hx1.le`. Establish `hh2 : (2 : ℝ) ≤ (h0v s ch : ℝ)`. Establish `: 1 ≤ ⌈s.x ^ ch⌉₊` using `Nat.one_le_ceil_iff.2 (Real.rpow_pos_of_pos hxp _)`.

Conclude with `(show 2 ≤ h0v s ch by unfold h0v; omega)` after adjusting the coercions. Establish `hD1 : (1 : ℝ) ≤ (Delv s cD : ℝ)`. Establish `: 1 ≤ ⌈s.x ^ cD⌉₊` using `Nat.one_le_ceil_iff.2 (Real.rpow_pos_of_pos hxp _)`. Conclude with `this` after adjusting the coercions. Establish `hbR : ∀ τ (j : Fin D.R.m), (((D.hc τ).b j : ℚ) : ℝ) = (b1 τ : ℝ) + (j.1 : ℝ) * (h0v s ch : ℝ)`.

Introduce `τ j`. Rewrite using `[(hbe τ j).1]`. Use `push_cast`. Both sides reduce to the same expression. Establish `heR : ∀ τ (j : Fin D.R.m), (((D.hc τ).e j : ℚ) : ℝ) = (b1 τ : ℝ) + (j.1 : ℝ) * (h0v s ch : ℝ) + (h0v s ch : ℝ) / 2`.

Introduce `τ j`. Rewrite using `[(hbe τ j).2, (hbe τ j).1]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hjη : ∀ j : Fin D.R.m, (j.1 : ℝ) * (h0v s ch : ℝ) + (h0v s ch : ℝ) ≤ η`.

Introduce `j`. Establish `: (j.1 : ℝ) + 1 ≤ D.R.m` using `by exact_mod_cast j.2`. Use `show _ ≤ (D.R.m : ℝ) * (h0v s ch : ℝ)`. Use the polynomial consequences of the given equalities and inequalities. Establish `hj0 : ∀ j : Fin D.R.m, 0 ≤ (j.1 : ℝ) * (h0v s ch : ℝ)` using `fun j => by positivity`.

Establish `hw : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, (b1 τ : ℝ) + 1 ≤ wj D j τ ∧ wj D j τ ≤ (b1 τ : ℝ) + η - (h0v s ch : ℝ) / 2`. Introduce `j h1 h2 τ`. Establish `hj : j - 1 < D.R.m` using `by omega`. Unfold `wj`. Rewrite using `[dif_pos hj, heR]`.

Establish `a1` using `hjη ⟨j - 1, hj⟩`. Establish `a2` using `hj0 ⟨j - 1, hj⟩`. Apply the tactic sequence `constructor <;> linarith`. Establish `htopR : ∀ τ (t : D.host.TT), (D.eTau τ : D.R.GG) = D.R.tau1 t → (bT t : ℝ) + s.b' / s.x - 1 < b1 τ ∧ (b1 τ : ℝ) ≤ (bT t : ℝ) + s.b' / s.x`. Introduce `τ t h`.

Rewrite using `[htop τ t h]`. Use `push_cast`. Establish `a1` using `Int.floor_le (s.b' / s.x)`. Establish `a2` using `Int.sub_one_lt_floor (s.b' / s.x)`. Apply the tactic sequence `constructor <;> linarith`.

Establish `hthickR : ∀ τ, (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces → s.b ≤ b1 τ ∧ (b1 τ : ℝ) ≤ s.b + (h0v s ch : ℝ) / 2`. Introduce `τ h`. Establish `a1` using `Int.le_ceil s.b`. Establish `a2` using `Int.ceil_lt_add_one s.b`. Take `⟨h1, h2⟩` from `hthick τ h`.

Establish `a3 : ((⌈s.b⌉ : ℤ) : ℝ) ≤ b1 τ` using `by exact_mod_cast h1`. Establish `a4 : (b1 τ : ℝ) + 1 ≤ ((⌈s.b⌉ : ℤ) : ℝ) + (Units.torsionOrder D.host.E : ℝ)`. Conclude with `Int.add_one_le_of_lt h2` after adjusting the coercions. Apply the tactic sequence `constructor <;> linarith`. Establish `hthinR : ∀ τ, D.host.IsThin (D.eTau τ : D.R.GG) → s.w'' D.R.n ≤ b1 τ ∧ (b1 τ : ℝ) ≤ s.w'' D.R.n + 1`.

Introduce `τ h`. Establish `a1` using `Int.le_ceil (s.w'' D.R.n)`. Establish `a2` using `Int.ceil_lt_add_one (s.w'' D.R.n)`. Rewrite using `[hthin τ h]`. Apply the tactic sequence `constructor <;> linarith`.

Establish `hn1 : (1 : ℝ) ≤ D.R.n`. Conclude with `(show 1 ≤ D.R.n from D.R.ord_pos)` after adjusting the coercions. Establish `hk3 : 3 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Establish `hk3R : (3 : ℝ) ≤ D.R.k` using `by exact_mod_cast hk3`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ht, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `τ t hm h`. Rewrite using `[hbR]`. Use `(htopR τ t h).1` as an intermediate fact. Simplify using `only [Nat.cast_zero, zero_mul, add_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `τ j`. Establish `hb1 : (b1 τ : ℝ) ≤ 3 * s.b + 2`. Distinguish the cases in `h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces`. Unfold `Host.topPlaces at h1`. Take `⟨t, ht1, ht2⟩` from `Finset.mem_image.1 h1`.

Establish `a1` using `(htopR τ ⟨t, ht1⟩ ht2.symm).2`. Establish `a2` using `(hbT ⟨t, ht1⟩).2`. Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces`. Use `(hthickR τ h2).2` as an intermediate fact.

Establish `a1` using `hjη j`. Establish `a2` using `hj0 j`. Establish `a3 : η ≤ s.b` using `hη`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `a1` using `(hthinR τ ⟨(D.eTau τ).2, h1, h2⟩).2`.

Establish `a2 : s.w'' D.R.n ≤ s.b'` using `div_le_self hb'pos.le (by nlinarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hbR]`. Establish `a1` using `hjη j`. Establish `a2 : η ≤ s.b` using `hη`.

Use the polynomial consequences of the given equalities and inequalities. Introduce `j h1 h2 τ h`. Establish `a1` using `hw j h1 h2 τ`. Establish `a2` using `hthickR τ h`. Apply the tactic sequence `constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]`.

Introduce `j h1 h2 τ t h`. Establish `a1` using `hw j h1 h2 τ`. Establish `a2` using `htopR τ t h`. Apply the tactic sequence `constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]`. Introduce `j h1 h2 τ h`.

Establish `a1` using `hw j h1 h2 τ`. Establish `a2` using `hthinR τ h`. Apply the tactic sequence `constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]`. Introduce `τ h0 h`. Establish `e1 : (((D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) = S + 1 / 2`.

Rewrite using `[(hu τ (by omega) h).1, hv τ ⟨0, h0⟩]`. Simplify using `only [Nat.sub_zero, S]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hS : 1 ≤ S` using `by show 1 ≤ (D.R.k : ℝ) * (4 * (Delv s cD : ℝ))`.

Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[e1]`. Apply the tactic sequence `constructor <;> linarith`. Introduce `τ i`. Rewrite using `[hv τ i]`.

Establish `a1 : ((D.R.k - 2 - i.1 : ℕ) : ℝ) ≤ D.R.k`. Conclude with `(by omega : D.R.k - 2 - i.1 ≤ D.R.k)` after adjusting the coercions. Simplify using `only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]`. Conclude with `⟨by positivity, mul_le_mul_of_nonneg_right a1 (by positivity)⟩`. Introduce `τ i j`.

Rewrite using `[Rat.cast_sub, hbR, heR, abs_le]`. Establish `a1` using `hjη i`. Establish `a2` using `hjη j`. Establish `a3` using `hj0 i`. Establish `a4` using `hj0 j`.

Apply the tactic sequence `constructor <;> linarith`. Use `D.R.rank_add_five_le` as an intermediate fact. Conclude with `(by omega : 1 ≤ D.R.t)` after adjusting the coercions. Rewrite using `[hLw]`. Conclude with `ten_ceil_logb_le_Lwv s _ (by positivity) hnN`.

Establish `a1 : 0 < s.x ^ (-s.eps) * (D.R.n : ℝ)` using `mul_pos (Real.rpow_pos_of_pos hxp _) (by linarith)`. Conclude with `lt_of_lt_of_le a1 hT2` after adjusting the coercions. Establish `hsub : D.host.T2 ⊆ Finset.range D.R.n`. Introduce `a ha`. Establish `a1` using `D.host.second_set_range a ha`.

Establish `a2` using `D.host.two_le_Lw`. Rewrite using `[Finset.mem_range]`. Establish `a3 : D.R.n0 ≤ D.R.n` using `addOrderOf_le_card.trans (le_of_eq D.R.toFrame.natCard_A)`. Use the polynomial consequences of the given equalities and inequalities. Simplify using `using Finset.card_le_card hsub`.
-/
theorem windows_of_large_scale : ∀ eps cD ch C8 : ℝ, 0 < eps → eps < 1 / 52 → 0 ≤ cD → 402 ≤ ch → ∃ x0 : ℝ, ∀ (s : Scale) (D : D7) (bT : D.host.TT → ℤ), s.eps = eps → x0 ≤ s.x → RankVal s D.R → HostVal s C8 D.host → (∀ t, s.b' ≤ (bT t : ℝ) ∧ (bT t : ℝ) ≤ 2 * s.b') → HCVal s cD ch D.host (fun τ => (D.eTau τ : D.R.GG)) D.hc bT → let η : ℝ := (D.R.m : ℝ) * (h0v s ch : ℝ); let S : ℝ := (D.R.k : ℝ) * (4 * (Delv s cD : ℝ)); (∀ τ (t : D.host.TT) (hm : 0 < D.R.m), (D.eTau τ : D.R.GG) = D.R.tau1 t → (((D.hc τ).b ⟨0, hm⟩ : ℚ) : ℝ) - (bT t : ℝ) > ((D.R.k : ℝ) - 1) / 2 + 3) ∧ (∀ τ j, (((D.hc τ).b j : ℚ) : ℝ) ≤ s.b ^ 2) ∧ (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces → s.b ≤ wj D j τ ∧ wj D j τ ≤ s.b + η + 1) ∧ (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ (t : D.host.TT), (D.eTau τ : D.R.GG) = D.R.tau1 t → (bT t : ℝ) + s.b' / s.x ≤ wj D j τ ∧ wj D j τ ≤ (bT t : ℝ) + s.b' / s.x + η) ∧ (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, D.host.IsThin (D.eTau τ : D.R.GG) → s.w'' D.R.n ≤ wj D j τ ∧ wj D j τ ≤ s.w'' D.R.n + η) ∧ (∀ τ (h0 : 0 < D.R.k - 1), (D.eTau τ : D.R.GG) ∉ D.host.topPlaces → S ≤ (((D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) ∧ (((D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) ≤ 2 * S) ∧ (∀ τ (i : Fin (D.R.k - 1)), 0 ≤ (((D.hc τ).v i : ℚ) : ℝ) ∧ (((D.hc τ).v i : ℚ) : ℝ) ≤ S) ∧ (∀ τ (i j : Fin D.R.m), |(((D.hc τ).b i - (D.hc τ).e j : ℚ) : ℝ)| ≤ η) ∧ 1 ≤ (D.R.t : ℝ) ∧ (D.R.t : ℝ) ≤ s.x ^ (401 : ℝ) ∧ 10 * ⌈Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m)⌉₊ + 20 ≤ D.host.Lw ∧ 0 < D.host.T2.card ∧ D.host.T2.card ≤ D.R.n := by
  intro eps cD ch C8 he he' hcD hch
  obtain ⟨x0, hx0⟩ := windows_scale_facts eps ch he he' hch
  obtain ⟨x1, hx1'⟩ := torsionOrder_le_half_gap eps ch he he' hch
  refine ⟨max x0 x1, fun s D bT hs hx hR hH hbT hC => ?_⟩
  obtain ⟨hk5, hη, hbb, hb6, ht, hnN⟩ := hx0 s D.R hs (le_trans (le_max_left _ _) hx) hR
  have htor := hx1' s D.R D.host hs (le_trans (le_max_right _ _) hx) hR
  obtain ⟨hv, hu, ⟨b1, hbe, htop, hthick, hthin⟩, -⟩ := hC
  obtain ⟨-, -, hT2, -, -, hLw, -, -⟩ := hH
  intro η S
  have hx1 := s.one_lt_alt
  have hxp : 0 < s.x := by linarith
  have hb'pos : 0 < s.b' := div_pos (mul_pos hxp (Real.exp_pos _)) (Real.exp_pos _)
  have hdiv : s.b' / s.x ≤ s.b' := div_le_self hb'pos.le hx1.le
  have hh2 : (2 : ℝ) ≤ (h0v s ch : ℝ) := by
    have : 1 ≤ ⌈s.x ^ ch⌉₊ := Nat.one_le_ceil_iff.2 (Real.rpow_pos_of_pos hxp _)
    exact_mod_cast (show 2 ≤ h0v s ch by unfold h0v; omega)
  have hD1 : (1 : ℝ) ≤ (Delv s cD : ℝ) := by
    have : 1 ≤ ⌈s.x ^ cD⌉₊ := Nat.one_le_ceil_iff.2 (Real.rpow_pos_of_pos hxp _)
    exact_mod_cast this
  have hbR : ∀ τ (j : Fin D.R.m), (((D.hc τ).b j : ℚ) : ℝ) = (b1 τ : ℝ) + (j.1 : ℝ) * (h0v s ch : ℝ) := by
    intro τ j; rw [(hbe τ j).1]; push_cast; rfl
  have heR : ∀ τ (j : Fin D.R.m), (((D.hc τ).e j : ℚ) : ℝ) =
      (b1 τ : ℝ) + (j.1 : ℝ) * (h0v s ch : ℝ) + (h0v s ch : ℝ) / 2 := by
    intro τ j; rw [(hbe τ j).2, (hbe τ j).1]; push_cast; rfl
  have hjη : ∀ j : Fin D.R.m, (j.1 : ℝ) * (h0v s ch : ℝ) + (h0v s ch : ℝ) ≤ η := by
    intro j
    have : (j.1 : ℝ) + 1 ≤ D.R.m := by exact_mod_cast j.2
    show _ ≤ (D.R.m : ℝ) * (h0v s ch : ℝ)
    nlinarith
  have hj0 : ∀ j : Fin D.R.m, 0 ≤ (j.1 : ℝ) * (h0v s ch : ℝ) := fun j => by positivity
  have hw : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, (b1 τ : ℝ) + 1 ≤ wj D j τ ∧
      wj D j τ ≤ (b1 τ : ℝ) + η - (h0v s ch : ℝ) / 2 := by
    intro j h1 h2 τ
    have hj : j - 1 < D.R.m := by omega
    unfold wj
    rw [dif_pos hj, heR]
    have a1 := hjη ⟨j - 1, hj⟩
    have a2 := hj0 ⟨j - 1, hj⟩
    constructor <;> linarith
  have htopR : ∀ τ (t : D.host.TT), (D.eTau τ : D.R.GG) = D.R.tau1 t →
      (bT t : ℝ) + s.b' / s.x - 1 < b1 τ ∧ (b1 τ : ℝ) ≤ (bT t : ℝ) + s.b' / s.x := by
    intro τ t h
    rw [htop τ t h]
    push_cast
    have a1 := Int.floor_le (s.b' / s.x)
    have a2 := Int.sub_one_lt_floor (s.b' / s.x)
    constructor <;> linarith
  have hthickR : ∀ τ, (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces →
      s.b ≤ b1 τ ∧ (b1 τ : ℝ) ≤ s.b + (h0v s ch : ℝ) / 2 := by
    intro τ h
    have a1 := Int.le_ceil s.b
    have a2 := Int.ceil_lt_add_one s.b
    obtain ⟨h1, h2⟩ := hthick τ h
    have a3 : ((⌈s.b⌉ : ℤ) : ℝ) ≤ b1 τ := by exact_mod_cast h1
    have a4 : (b1 τ : ℝ) + 1 ≤ ((⌈s.b⌉ : ℤ) : ℝ) + (Units.torsionOrder D.host.E : ℝ) := by
      exact_mod_cast Int.add_one_le_of_lt h2
    constructor <;> linarith
  have hthinR : ∀ τ, D.host.IsThin (D.eTau τ : D.R.GG) →
      s.w'' D.R.n ≤ b1 τ ∧ (b1 τ : ℝ) ≤ s.w'' D.R.n + 1 := by
    intro τ h
    have a1 := Int.le_ceil (s.w'' D.R.n)
    have a2 := Int.ceil_lt_add_one (s.w'' D.R.n)
    rw [hthin τ h]
    constructor <;> linarith
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    exact_mod_cast (show 1 ≤ D.R.n from D.R.ord_pos)
  have hk3 : 3 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hk3R : (3 : ℝ) ≤ D.R.k := by exact_mod_cast hk3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ht, ?_, ?_, ?_⟩
  · intro τ t hm h
    rw [hbR]
    have := (htopR τ t h).1
    simp only [Nat.cast_zero, zero_mul, add_zero]
    linarith
  · intro τ j
    have hb1 : (b1 τ : ℝ) ≤ 3 * s.b + 2 := by
      by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
      · unfold Host.topPlaces at h1
        obtain ⟨t, ht1, ht2⟩ := Finset.mem_image.1 h1
        have a1 := (htopR τ ⟨t, ht1⟩ ht2.symm).2
        have a2 := (hbT ⟨t, ht1⟩).2
        linarith
      · by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
        · have := (hthickR τ h2).2
          have a1 := hjη j
          have a2 := hj0 j
          have a3 : η ≤ s.b := hη
          linarith
        · have a1 := (hthinR τ ⟨(D.eTau τ).2, h1, h2⟩).2
          have a2 : s.w'' D.R.n ≤ s.b' := div_le_self hb'pos.le (by nlinarith)
          linarith
    rw [hbR]
    have a1 := hjη j
    have a2 : η ≤ s.b := hη
    nlinarith
  · intro j h1 h2 τ h
    have a1 := hw j h1 h2 τ
    have a2 := hthickR τ h
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
  · intro j h1 h2 τ t h
    have a1 := hw j h1 h2 τ
    have a2 := htopR τ t h
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
  · intro j h1 h2 τ h
    have a1 := hw j h1 h2 τ
    have a2 := hthinR τ h
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
  · intro τ h0 h
    have e1 : (((D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) = S + 1 / 2 := by
      rw [(hu τ (by omega) h).1, hv τ ⟨0, h0⟩]
      simp only [Nat.sub_zero, S]
      push_cast
      ring
    have hS : 1 ≤ S := by
      show 1 ≤ (D.R.k : ℝ) * (4 * (Delv s cD : ℝ))
      nlinarith
    rw [e1]
    constructor <;> linarith
  · intro τ i
    rw [hv τ i]
    have a1 : ((D.R.k - 2 - i.1 : ℕ) : ℝ) ≤ D.R.k := by
      exact_mod_cast (by omega : D.R.k - 2 - i.1 ≤ D.R.k)
    simp only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
    exact ⟨by positivity, mul_le_mul_of_nonneg_right a1 (by positivity)⟩
  · intro τ i j
    rw [Rat.cast_sub, hbR, heR, abs_le]
    have a1 := hjη i
    have a2 := hjη j
    have a3 := hj0 i
    have a4 := hj0 j
    constructor <;> linarith
  · have := D.R.rank_add_five_le
    exact_mod_cast (by omega : 1 ≤ D.R.t)
  · rw [hLw]
    exact ten_ceil_logb_le_Lwv s _ (by positivity) hnN
  · have a1 : 0 < s.x ^ (-s.eps) * (D.R.n : ℝ) := mul_pos (Real.rpow_pos_of_pos hxp _) (by linarith)
    exact_mod_cast lt_of_lt_of_le a1 hT2
  · have hsub : D.host.T2 ⊆ Finset.range D.R.n := by
      intro a ha
      have a1 := D.host.second_set_range a ha
      have a2 := D.host.two_le_Lw
      rw [Finset.mem_range]
      have a3 : D.R.n0 ≤ D.R.n :=
        addOrderOf_le_card.trans (le_of_eq D.R.toFrame.natCard_A)
      nlinarith
    simpa using Finset.card_le_card hsub

end GlobalTheory.EX
