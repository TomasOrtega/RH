import Formalism.SizeWindowBrackets.SChain
import Formalism.SizeWindowBrackets.ChainSlopeWindows.LevelOfCongruence
import Formalism.SizeWindowBrackets.ChainSlopeWindows.LipschitzWeightAndMinimum
import Formalism.SizeWindowBrackets.ChainSlopeWindows.SubThreeMulLogTwoLe

open Finset

noncomputable section

namespace Formalism.LFunctionChainParameters.LChain

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr

/- English proof (translation)
Introduce `H _ _ _ D ell N m TT T2 a w x ε b b' η X' θ Cd CL Err`. Unfold `GrowthInequalityHypotheses GrowthInequalityRemainingHyps GrowthInequalitySizes`. The claim follows by propositional logic.
-/
theorem proposition_hypothesis_split : GrowthHypothesesSplit := by
  intro H _ _ _ D ell N m TT T2 a w x ε b b' η X' θ Cd CL Err
  unfold GrowthInequalityHypotheses GrowthInequalityRemainingHyps GrowthInequalitySizes
  tauto

/- English proof (translation)
Introduce `x ε f b η θ Cd CL`. Conclude with `Iff.rfl`.
-/
theorem small_costs_split : SmallCostsSplit := by
  intro x ε f b η θ Cd CL
  exact Iff.rfl

/- English proof (translation)
Introduce `C ε x n nT nT2 m b k aE Err`. Unfold `SizeWindows RestSize errorBracketSizeWindows`. The claim follows by propositional logic.
-/
theorem size_windows_split : SizeWindowsSplit := by
  intro C ε x n nT nT2 m b k aE Err
  unfold SizeWindows RestSize errorBracketSizeWindows
  tauto

/- English proof (translation)
Introduce and unpack `Cd eD eL ε x ⟨K, cHH, eK, CL, hCore, hx3, h26, hLX, hMove⟩`. Take `⟨H, i1, i2, i3, W, i4, i5, Top, i6, m, f, Dd, C, Xpp, D, ell, N, TT, T2, a, w, eT, eP, η, X', θ, hx, hε, heD, heL, hcHH, hHost, hId, hLed, hWin, hBN, hRest, hCost, hSize⟩` from `hCore`. Substitute `hx hε` using the available equality. Take `⟨j1, j2, j3, j4, j5⟩` from `hId`. Take `⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩` from `hLed`.

Establish `hWin'` using `hWin`. Take `⟨⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, wC⟩, wEta⟩` from `hWin'`. Take `⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17⟩` from `wC`. Establish `hLX' : LargeX Dd.x Dd.ε K C.cHH eK`. Use `⟨hLX.1, le_trans ?_ hLX.2⟩` and prove the remaining obligations.

Unfold `KBig`. Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) (by linarith)`. Establish `hTop : topExcess D N ell TT a w ≤ Dd.x ^ (CErr C * Dd.ε) * errorBracketSizeWindows Dd.x Dd.ε (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a` using `joint_error_bound (H := H) top_from_weighted_mean Dd C Xpp eK K D N ell TT T2 a w eT eP (uniform_bound_statement Dd C Xpp) l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 hWin hLX' hBN.1 hBN.2 j1 j2 j3 j4 j5`. Establish `hb : 0 < Dd.b` using `by linarith`. Establish `hx0 : 0 < Dd.x` using `by linarith`.

Establish `hk : 0 < Dd.k` using `by linarith`. Establish `ha : 0 ≤ Dd.a` using `l1.2.2.1`. Establish `hBr : 0 ≤ errorBracketSizeWindows Dd.x Dd.ε (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a`. Unfold `errorBracketSizeWindows`. Check the signs of the components of the expression.

Establish `hExp : Dd.x ^ (CErr C * Dd.ε) ≤ Dd.x ^ ((eD + eL + 3) * Dd.ε)`. Use `Real.rpow_le_rpow_of_exponent_le w1 (mul_le_mul_of_nonneg_right ?_ w2.le)` and prove the remaining obligations. Unfold `CErr`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hTop'` using `le_trans hTop (mul_le_mul_of_nonneg_right hExp hBr)`.

Take `⟨⟨r1, r2, r3, r4, r5, r6, r7, r8⟩, r9, r10⟩` from `hRest`. Use `⟨H, i1, i2, i3, D, ell, N, m, TT, T2, a, w, Dd.b, Dd.b', η, X', θ, CL, Dd.x ^ ((eD + eL + 3) * Dd.ε) * errorBracketSizeWindows Dd.x Dd.ε (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a, Dd.k, Dd.a, hHost, ⟨hx3, hb, r1, r2, r3, r4, r5, r6, r7, r8, hTop', r9, r10⟩, (small_costs_s …` and prove the remaining obligations. Use `(size_windows_split _ _ _ _ _ _ _ _ _ _ _).2 ⟨hSize, le_refl _, ⟨hx3, h26⟩, w2, by linarith, Fintype.card_pos, hb, ha, Finset.card_le_univ T2, w7, w8⟩` and prove the remaining obligations.
-/
theorem chain_top_bound : ChainTop := by
  rintro Cd eD eL ε x ⟨K, cHH, eK, CL, hCore, hx3, h26, hLX, hMove⟩
  obtain ⟨H, i1, i2, i3, W, i4, i5, Top, i6, m, f, Dd, C, Xpp, D, ell, N, TT, T2, a, w, eT, eP, η, X', θ,
    hx, hε, heD, heL, hcHH, hHost, hId, hLed, hWin, hBN, hRest, hCost, hSize⟩ := hCore
  subst hx hε
  obtain ⟨j1, j2, j3, j4, j5⟩ := hId
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩ := hLed
  have hWin' := hWin
  obtain ⟨⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22,
    w23, w24, w25, w26, w27, wC⟩, wEta⟩ := hWin'
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17⟩ := wC

  have hLX' : LargeX Dd.x Dd.ε K C.cHH eK := by
    refine ⟨hLX.1, le_trans ?_ hLX.2⟩
    unfold KBig
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) (by linarith)

  have hTop : topExcess D N ell TT a w ≤
      Dd.x ^ (CErr C * Dd.ε) * errorBracketSizeWindows Dd.x Dd.ε (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a :=
    joint_error_bound (H := H) top_from_weighted_mean Dd C Xpp eK K D N ell TT T2 a w eT eP
      (uniform_bound_statement Dd C Xpp) l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 hWin hLX' hBN.1 hBN.2 j1 j2 j3 j4 j5
  have hb : 0 < Dd.b := by linarith
  have hx0 : 0 < Dd.x := by linarith
  have hk : 0 < Dd.k := by linarith
  have ha : 0 ≤ Dd.a := l1.2.2.1
  have hBr : 0 ≤ errorBracketSizeWindows Dd.x Dd.ε (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a := by
    unfold errorBracketSizeWindows
    positivity
  have hExp : Dd.x ^ (CErr C * Dd.ε) ≤ Dd.x ^ ((eD + eL + 3) * Dd.ε) := by
    refine Real.rpow_le_rpow_of_exponent_le w1 (mul_le_mul_of_nonneg_right ?_ w2.le)
    unfold CErr
    linarith
  have hTop' := le_trans hTop (mul_le_mul_of_nonneg_right hExp hBr)
  obtain ⟨⟨r1, r2, r3, r4, r5, r6, r7, r8⟩, r9, r10⟩ := hRest
  refine ⟨H, i1, i2, i3, D, ell, N, m, TT, T2, a, w, Dd.b, Dd.b', η, X', θ, CL,
    Dd.x ^ ((eD + eL + 3) * Dd.ε)
      * errorBracketSizeWindows Dd.x Dd.ε (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a,
    Dd.k, Dd.a, hHost, ⟨hx3, hb, r1, r2, r3, r4, r5, r6, r7, r8, hTop', r9, r10⟩,
    (small_costs_split _ _ _ _ _ _ _ _).2 ⟨hMove, hCost⟩, ?_⟩
  refine (size_windows_split _ _ _ _ _ _ _ _ _ _ _).2 ⟨hSize, le_refl _, ⟨hx3, h26⟩, w2, by linarith,
    Fintype.card_pos, hb, ha, Finset.card_le_univ T2, w7, w8⟩

/- English proof (translation)
Take `⟨Cd, hCd, hDer⟩` from `derivative_integral_all`. Use `⟨Cd, hCd, fun eD eL ε x h => ?_⟩` and prove the remaining obligations. Take `⟨H, i1, i2, i3, D, ell, N, m, TT, T2, a, w, b, b', η, X', θ, CL, Err, k, aE, hD, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩, hS, hW⟩` from `chain_top_bound Cd eD eL ε x h`. Use `proposition_at_point (eD + eL + 3) ε x ⟨H, i1, i2, i3, D, ell, N, m, TT, T2, a, w, b, b', η, X', θ, Cd, CL, Err, k, aE, hD, ⟨h1, h2, h3, h4, h5, h6, h7, hCd, h8, h9, h10, h11, h12, lipschitz_weight_all H D ell, hDer H D ell, h13⟩, hS, hW⟩` as an intermediate fact. Establish `e : eD + eL + 3 + 3 = eD + eL + 6` using `by ring`.

Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
theorem chain_at_alt : ChainAt := by
  obtain ⟨Cd, hCd, hDer⟩ := derivative_integral_all
  refine ⟨Cd, hCd, fun eD eL ε x h => ?_⟩
  obtain ⟨H, i1, i2, i3, D, ell, N, m, TT, T2, a, w, b, b', η, X', θ, CL, Err, k, aE, hD,
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩, hS, hW⟩ := chain_top_bound Cd eD eL ε x h
  have := proposition_at_point (eD + eL + 3) ε x
    ⟨H, i1, i2, i3, D, ell, N, m, TT, T2, a, w, b, b', η, X', θ, Cd, CL, Err, k, aE, hD,
      ⟨h1, h2, h3, h4, h5, h6, h7, hCd, h8, h9, h10, h11, h12, lipschitz_weight_all H D ell, hDer H D ell, h13⟩, hS, hW⟩
  have e : eD + eL + 3 + 3 = eD + eL + 6 := by ring
  rwa [e] at this

/- English proof (translation)
Take `⟨Cd, hCd, hFin⟩` from `proposition_final_minimum`. Use `⟨Cd, hCd, fun eD eL ε₁ hε₁ h => hFin (eD + eL + 3) ε₁ hε₁ ?_⟩` and prove the remaining obligations. Introduce `ε h0 h1`. Take `⟨x₀, hx₀⟩` from `h ε h0 h1`. Conclude with `⟨x₀, fun x hx => chain_top_bound Cd eD eL ε x (hx₀ x hx)⟩`.
-/
theorem chain_weighted_mean_to_unit_weight : ChainGivesRiemannHypothesis := by
  obtain ⟨Cd, hCd, hFin⟩ := proposition_final_minimum
  refine ⟨Cd, hCd, fun eD eL ε₁ hε₁ h => hFin (eD + eL + 3) ε₁ hε₁ ?_⟩
  intro ε h0 h1
  obtain ⟨x₀, hx₀⟩ := h ε h0 h1
  exact ⟨x₀, fun x hx => chain_top_bound Cd eD eL ε x (hx₀ x hx)⟩

/- English proof (translation)
Use `set A : ℝ := 4 * |Cd| + 15 + 12 * |CL| with hA`. Establish `hA0 : 0 ≤ A` using `by positivity`. Use `⟨max 1 (A ^ 4), fun x hx => ?_⟩` and prove the remaining obligations. Establish `hx1 : 1 ≤ x` using `le_trans (le_max_left _ _) hx`. Establish `hxA : A ^ 4 ≤ x` using `le_trans (le_max_right _ _) hx`.

Establish `hx0 : 0 < x` using `by linarith`. Use `set y : ℝ := x ^ ((1 : ℝ) / 4) with hy`. Establish `hy1 : 1 ≤ y` using `Real.one_le_rpow hx1 (by norm_num)`. Establish `hyA : A ≤ y`. Establish `h1` using `Real.rpow_le_rpow (by positivity) hxA (by norm_num : (0 : ℝ) ≤ 1 / 4)`.

Establish `h2 : (A ^ 4) ^ ((1 : ℝ) / 4) = A`. Use `Real.pow_rpow_inv_natCast hA0 (by norm_num : (4 : ℕ) ≠ 0)` as an intermediate fact. Evaluate the numerical expressions using `at this ⊢`. Conclude with `this`. Rewrite `h1` using `[h2]`. Then use the resulting hypothesis.

Establish `hlog : Real.log x ≤ 4 * y`. Use `Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 4)` as an intermediate fact. Rewrite `this` using `[← hy]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlog0 : 0 ≤ Real.log x` using `Real.log_nonneg hx1`.

Establish `hlog1 : Real.log (x + 1) ≤ 1 + Real.log x`. Establish `h1 : Real.log (x + 1) ≤ Real.log (2 * x)` using `Real.log_le_log (by linarith) (by linarith)`. Rewrite `h1` using `[Real.log_mul (by norm_num) hx0.ne']`. Establish `h2 : Real.log 2 ≤ 2 - 1` using `Real.log_le_sub_one_of_pos (by norm_num)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hCL : CL * Real.log x ≤ |CL| * (4 * y)` using `le_trans (mul_le_mul_of_nonneg_right (le_abs_self CL) hlog0) (mul_le_mul_of_nonneg_left hlog (abs_nonneg _))`. Establish `hyy : y * y ≤ x ^ ((1 : ℝ) / 2 + ε)`. Rewrite using `[hy, ← Real.rpow_add hx0]`. Conclude with `Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)`. Establish `hCd : Cd ≤ |Cd|` using `le_abs_self Cd`.

Establish `hCd0 : 0 ≤ |Cd|` using `abs_nonneg Cd`. Establish `h1 : moveCost x Cd CL ≤ A * y`. Unfold `moveCost`. Establish `e1 : 4 * |Cd| ≤ 4 * |Cd| * y` using `by nlinarith`. Establish `e2 : A * y = 4 * |Cd| * y + 15 * y + 12 * |CL| * y` using `by rw [hA]; ring`.

Rewrite using `[e2]`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `le_trans h1 (le_trans (mul_le_mul_of_nonneg_right hyA (by linarith)) hyy)`.
-/
lemma moveCostEv (Cd CL ε : ℝ) (hε : 0 < ε) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → moveCost x Cd CL ≤ x ^ ((1 : ℝ) / 2 + ε) := by
  set A : ℝ := 4 * |Cd| + 15 + 12 * |CL| with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨max 1 (A ^ 4), fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hxA : A ^ 4 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  set y : ℝ := x ^ ((1 : ℝ) / 4) with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow hx1 (by norm_num)
  have hyA : A ≤ y := by
    have h1 := Real.rpow_le_rpow (by positivity) hxA (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have h2 : (A ^ 4) ^ ((1 : ℝ) / 4) = A := by
      have := Real.pow_rpow_inv_natCast hA0 (by norm_num : (4 : ℕ) ≠ 0)
      norm_num at this ⊢
      exact this
    rwa [h2] at h1
  have hlog : Real.log x ≤ 4 * y := by
    have := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 4)
    rw [← hy] at this
    linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlog1 : Real.log (x + 1) ≤ 1 + Real.log x := by
    have h1 : Real.log (x + 1) ≤ Real.log (2 * x) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) hx0.ne'] at h1
    have h2 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hCL : CL * Real.log x ≤ |CL| * (4 * y) :=
    le_trans (mul_le_mul_of_nonneg_right (le_abs_self CL) hlog0) (mul_le_mul_of_nonneg_left hlog (abs_nonneg _))
  have hyy : y * y ≤ x ^ ((1 : ℝ) / 2 + ε) := by
    rw [hy, ← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hCd : Cd ≤ |Cd| := le_abs_self Cd
  have hCd0 : 0 ≤ |Cd| := abs_nonneg Cd
  have h1 : moveCost x Cd CL ≤ A * y := by
    unfold moveCost
    have e1 : 4 * |Cd| ≤ 4 * |Cd| * y := by nlinarith
    have e2 : A * y = 4 * |Cd| * y + 15 * y + 12 * |CL| * y := by rw [hA]; ring
    rw [e2]
    nlinarith
  exact le_trans h1 (le_trans (mul_le_mul_of_nonneg_right hyA (by linarith)) hyy)

/- English proof (translation)
Establish `h2 : 0 ≤ 3 * ε / 8` using `by positivity`. Establish `h3` using `Real.rpow_le_rpow (by positivity) h1 h2`. Rewrite `h3` using `[← Real.rpow_mul (by norm_num)]`. Establish `h4 : 8 / (3 * ε) * (3 * ε / 8) = 1` using `by field_simp`. Rewrite `h3` using `[h4, Real.rpow_one]`. Then use the resulting hypothesis.
-/
lemma le_rpow_26 (ε x : ℝ) (hε : 0 < ε) (h1 : (26 : ℝ) ^ (8 / (3 * ε)) ≤ x) : 26 ≤ x ^ (3 * ε / 8) := by
  have h2 : 0 ≤ 3 * ε / 8 := by positivity
  have h3 := Real.rpow_le_rpow (by positivity) h1 h2
  rw [← Real.rpow_mul (by norm_num)] at h3
  have h4 : 8 / (3 * ε) * (3 * ε / 8) = 1 := by field_simp
  rwa [h4, Real.rpow_one] at h3

/- English proof (translation)
Introduce `K cHH eK Cd CL ε hε`. Take `⟨x₁, hx₁⟩` from `large_x_eventually ε K cHH eK hε`. Take `⟨x₂, hx₂⟩` from `moveCostEv Cd CL ε hε`. Use `⟨max (max x₁ x₂) (max 3 ((26 : ℝ) ^ (8 / (3 * ε)))), fun x hx => ⟨?_, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx`.

Conclude with `le_rpow_26 ε x hε (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx)`. Conclude with `hx₁ x (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx)`. Conclude with `hx₂ x (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx)`.
-/
theorem x_large_eventually : XLargeEv := by
  intro K cHH eK Cd CL ε hε
  obtain ⟨x₁, hx₁⟩ := large_x_eventually ε K cHH eK hε
  obtain ⟨x₂, hx₂⟩ := moveCostEv Cd CL ε hε
  refine ⟨max (max x₁ x₂) (max 3 ((26 : ℝ) ^ (8 / (3 * ε)))), fun x hx => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  · exact le_rpow_26 ε x hε (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx)
  · exact hx₁ x (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx)
  · exact hx₂ x (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx)

/- English proof (translation)
Take `⟨Cd, -, hChain⟩` from `chain_weighted_mean_to_unit_weight`. Introduce `eD eL ε₁ hε₁ h`. Use `hChain eD eL ε₁ hε₁ ?_` and prove the remaining obligations. Introduce `ε h0 h1`. Take `⟨K, cHH, eK, CL, x₀, hx₀⟩` from `h ε h0 h1`.

Take `⟨x₁, hx₁⟩` from `x_large_eventually K cHH eK Cd CL ε h0`. Conclude with `⟨max x₀ x₁, fun x hx => ⟨K, cHH, eK, CL, hx₀ x (le_trans (le_max_left _ _) hx), hx₁ x (le_trans (le_max_right _ _) hx)⟩⟩`.
-/
theorem chain_eventually : ChainEventualGivesRiemannHypothesis := by
  obtain ⟨Cd, -, hChain⟩ := chain_weighted_mean_to_unit_weight
  intro eD eL ε₁ hε₁ h
  refine hChain eD eL ε₁ hε₁ ?_
  intro ε h0 h1
  obtain ⟨K, cHH, eK, CL, x₀, hx₀⟩ := h ε h0 h1
  obtain ⟨x₁, hx₁⟩ := x_large_eventually K cHH eK Cd CL ε h0
  exact ⟨max x₀ x₁, fun x hx => ⟨K, cHH, eK, CL, hx₀ x (le_trans (le_max_left _ _) hx),
    hx₁ x (le_trans (le_max_right _ _) hx)⟩⟩

section
variable {U0 : Type} [Fintype U0] {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ}

def sLog (D0 : Data U0 W Top m f) (u0 : U0) : ℝ :=
  ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D0.w u0 j ρ)

def compl (D0 : Data U0 W Top m f) (C : Consts) : Data U0 (fun _ => Unit) Top m f where
  x := D0.x
  ε := D0.ε
  a := D0.a
  b := D0.b
  b' := D0.b'
  k := D0.k
  L := D0.L
  La := D0.La
  B0 := D0.B0
  Nc := D0.Nc
  gam := D0.gam
  LpL := D0.LpL
  v := Real.pi
  lg := 0
  logGam := 0
  aT := D0.aT
  w := D0.w
  d := fun _ _ => 1
  T := fun u0 _ => Real.exp (sLog D0 u0)
  muN := fun u0 _ => D0.ASK u0 - D0.LoP C
  muMaxN := fun u0 _ => D0.ASK u0 - D0.LoP C
  h := fun _ _ => 0
  muM := fun _ _ => 0
  muMaxM := fun _ _ => 0
  EeJ := fun _ _ _ => 0
  muCC := fun u0 => D0.ASK u0 - D0.LoP C
  muMinCC := fun u0 => D0.ASK u0 - D0.LoP C
  Fo := fun _ => 0
  Ga := fun u0 => D0.ASK u0 - D0.LoP C
  Ta := fun _ => 0
  ASK := D0.ASK
  IO := fun _ => 0
  HH := fun _ => D0.x ^ C.cHH * D0.b
  del := fun _ => 0
  η := fun _ => 0
  e := fun _ => 0
  delBar := 0
  etaBar := 0
  eBar := 0

/- English proof (translation)
Simplify using `[Data.s, wmean, compl]`.
-/
lemma compl_alt (D0 : Data U0 W Top m f) (C : Consts) (u0 : U0) :
    (compl D0 C).s u0 = D0.ASK u0 - D0.LoP C := by
  simp [Data.s, wmean, compl]

/- English proof (translation)
Unfold `Data.uF`. Rewrite using `[compl_alt]`. Simplify using `[compl]`.
-/
lemma compl_uF (D0 : Data U0 W Top m f) (C : Consts) (u0 : U0) : (compl D0 C).uF u0 = 0 := by
  unfold Data.uF
  rw [compl_alt]
  simp [compl]

/- English proof (translation)
Unfold `Data.Main sLog ph`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum, Finset.sum_sub_distrib]`. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma compl_main (D0 : Data U0 W Top m f) (u0 : U0) :
    D0.Main u0 = ∑ t, ((m : ℝ) * (ph (D0.aT t) - D0.aT t * (D0.gam - D0.LpL)) - D0.aT t * sLog D0 u0) := by
  unfold Data.Main sLog ph
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/- English proof (translation)
Take `⟨cE, cH, cCount, cSlope, cSl1, cLoss⟩` from `hC`. Establish `hk0 : 0 < D0.k` using `by linarith`. Establish `hnT : 0 ≤ D0.nT` using `by unfold Data.nT; positivity`. Establish `hLoP : 0 ≤ D0.LoP C` using `by unfold Data.LoP; positivity`. Establish `hm : (0 : ℝ) ≤ m` using `Nat.cast_nonneg m`.

Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `⟨hx, hb, ha, hb', hk0, Real.pi_pos, hf, haT, hw, fun _ _ => one_pos, fun _ _ => Real.exp_pos _, fun _ _ => le_refl _, cSl1, one_pos, le_refl _, le_refl _, by norm_num [compl]⟩`. Introduce `u0 u`. Establish `h1` using `hTop u0`. Rewrite `h1` using `[compl_main]`.

Establish `h2 : (compl D0 C).logOm = D0.gam - D0.LpL`. Simplify using `[Data.logOm, compl, Real.pi_ne_zero]`. Rewrite using `[h2]`. Simplify using `only [compl, Real.log_exp, Data.nT] at h1 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `u0 u`. Establish `: 0 ≤ C.cE * (m : ℝ) * D0.B0` using `by positivity`. Simplify `this` using `[compl, Data.Ee]`. Introduce `u0 u u'`. Establish `: 0 ≤ C.cH * (D0.nT * D0.a * D0.La + (m : ℝ) * D0.B0)` using `by positivity`.

Simplify `this` using `[compl, Data.nT]`. Introduce `u0 u`. Use `⟨?_, ?_, fun u' => ?_⟩` and prove the remaining obligations. Establish `h1 : 0 ≤ C.cCount * (D0.La + (m : ℝ) ^ 2 * D0.La / D0.k)` using `by positivity`. Establish `h2 : ∀ y : ℝ, y * Real.pi / Real.pi = y` using `fun y => by field_simp`.

Simplify using `only [compl, Real.log_exp, h2, mul_zero, add_zero]`. Unfold `sLog`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify `hS1 u0` using `[compl, sLog]`. Establish `: 0 ≤ C.cCount * Real.log D0.k` using `mul_nonneg cCount (Real.log_nonneg hk)`.

Simplify `this` using `[compl]`. Introduce `u0 u`. Establish `h1 : 0 ≤ C.cSlope * D0.nT * D0.a * D0.La * (1 + (m : ℝ) / D0.k)` using `by positivity`. Establish `h2 : 0 ≤ C.cSlope * D0.nT * D0.a * D0.La` using `by positivity`. Conclude with `⟨by simpa [compl, Data.nT] using h1, by simpa [compl, Data.nT] using h2⟩`.

Introduce `u0 u`. Establish `h1 : 0 ≤ C.cSl1 * (m : ℝ) * D0.B0` using `by positivity`. Establish `hS` using `hS0 u0`. Establish `h2 : 0 ≤ C.cSl1 * D0.nT * (m : ℝ) * (D0.a / D0.k + D0.b') * sLog D0 u0` using `mul_nonneg (by positivity) hS`. Establish `h3 : 0 ≤ C.cSl1 * Xpp` using `by positivity`.

Prove the components needed by the constructor for the conclusion. Simplify using `only [compl, Data.Ee, Finset.sum_const_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [Lo5, compl, Data.Ee, Finset.sum_const_zero, Real.log_exp, Data.nT] at h2 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `u0`. Establish `e : (compl D0 C).LoP C = D0.LoP C` using `rfl`. Rewrite using `[e]`. Conclude with `⟨by simp [compl], hLoP⟩`. Introduce `u0 _ _ _ _ _ _ _`.

Rewrite using `[compl_uF, compl_alt]`. Simplify using `[compl]`. Introduce `u0`. Rewrite using `[compl_alt]`. Use `⟨?_, ?_, le_refl _⟩` and prove the remaining obligations.

Establish `: 0 ≤ D0.x ^ C.cHH * D0.b` using `by positivity`. Simplify `this` using `[compl]`. Establish `: 0 < D0.x ^ C.cHH * D0.b` using `by positivity`. Simplify `this` using `[compl]`. Introduce `u0`.

Simplify using `[compl]`.
-/
lemma data_completion_bounds (D0 : Data U0 W Top m f) (C : Consts) (Xpp : ℝ)
    (hx : 0 < D0.x) (hb : 0 < D0.b) (ha : 0 ≤ D0.a) (hb' : 0 ≤ D0.b') (hk : 1 ≤ D0.k) (hLa : 0 ≤ D0.La)
    (hB0 : 0 ≤ D0.B0) (hXpp : 0 ≤ Xpp) (hf : 0 < f) (haT : ∀ t, 0 ≤ D0.aT t) (hw : ∀ u0 j ρ, 0 < D0.w u0 j ρ)
    (hC : 0 ≤ C.cE ∧ 0 ≤ C.cH ∧ 0 ≤ C.cCount ∧ 0 ≤ C.cSlope ∧ 0 ≤ C.cSl1 ∧ 0 ≤ C.cLoss)
    (hS0 : ∀ u0, 0 ≤ ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D0.w u0 j ρ))
    (hS1 : ∀ u0, ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D0.w u0 j ρ) ≤ C.cCount * (m : ℝ) * D0.L)
    (hTop : ∀ u0, D0.ASK u0 ≤ D0.Main u0 + C.cDiv * D0.nT * D0.a * D0.La
      + C.cDiv * (m : ℝ) * (D0.B0 + D0.Nc) * D0.x ^ (C.eDiv * D0.ε) + D0.LoP C) :
    SizeData₂ (compl D0 C) C Xpp := by
  obtain ⟨cE, cH, cCount, cSlope, cSl1, cLoss⟩ := hC
  have hk0 : 0 < D0.k := by linarith
  have hnT : 0 ≤ D0.nT := by unfold Data.nT; positivity
  have hLoP : 0 ≤ D0.LoP C := by unfold Data.LoP; positivity
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact ⟨hx, hb, ha, hb', hk0, Real.pi_pos, hf, haT, hw, fun _ _ => one_pos, fun _ _ => Real.exp_pos _,
      fun _ _ => le_refl _, cSl1, one_pos, le_refl _, le_refl _, by norm_num [compl]⟩
  ·
    intro u0 u
    have h1 := hTop u0
    rw [compl_main] at h1
    have h2 : (compl D0 C).logOm = D0.gam - D0.LpL := by
      simp [Data.logOm, compl, Real.pi_ne_zero]
    rw [h2]
    simp only [compl, Real.log_exp, Data.nT] at h1 ⊢
    linarith
  ·
    intro u0 u
    have : 0 ≤ C.cE * (m : ℝ) * D0.B0 := by positivity
    simpa [compl, Data.Ee] using this
  ·
    intro u0 u u'
    have : 0 ≤ C.cH * (D0.nT * D0.a * D0.La + (m : ℝ) * D0.B0) := by positivity
    simpa [compl, Data.nT] using this
  ·
    intro u0 u
    refine ⟨?_, ?_, fun u' => ?_⟩
    · have h1 : 0 ≤ C.cCount * (D0.La + (m : ℝ) ^ 2 * D0.La / D0.k) := by positivity
      have h2 : ∀ y : ℝ, y * Real.pi / Real.pi = y := fun y => by field_simp
      simp only [compl, Real.log_exp, h2, mul_zero, add_zero]
      unfold sLog
      linarith
    · simpa [compl, sLog] using hS1 u0
    · have : 0 ≤ C.cCount * Real.log D0.k := mul_nonneg cCount (Real.log_nonneg hk)
      simpa [compl] using this
  ·
    intro u0 u
    have h1 : 0 ≤ C.cSlope * D0.nT * D0.a * D0.La * (1 + (m : ℝ) / D0.k) := by positivity
    have h2 : 0 ≤ C.cSlope * D0.nT * D0.a * D0.La := by positivity
    exact ⟨by simpa [compl, Data.nT] using h1, by simpa [compl, Data.nT] using h2⟩
  ·
    intro u0 u
    have h1 : 0 ≤ C.cSl1 * (m : ℝ) * D0.B0 := by positivity
    have hS := hS0 u0
    have h2 : 0 ≤ C.cSl1 * D0.nT * (m : ℝ) * (D0.a / D0.k + D0.b') * sLog D0 u0 :=
      mul_nonneg (by positivity) hS
    have h3 : 0 ≤ C.cSl1 * Xpp := by positivity
    constructor
    · simp only [compl, Data.Ee, Finset.sum_const_zero]
      linarith
    · simp only [Lo5, compl, Data.Ee, Finset.sum_const_zero, Real.log_exp, Data.nT] at h2 ⊢
      linarith
  ·
    intro u0
    have e : (compl D0 C).LoP C = D0.LoP C := rfl
    rw [e]
    exact ⟨by simp [compl], hLoP⟩
  ·
    intro u0 _ _ _ _ _ _ _
    rw [compl_uF, compl_alt]
    simp [compl]
  ·
    intro u0
    rw [compl_alt]
    refine ⟨?_, ?_, le_refl _⟩
    · have : 0 ≤ D0.x ^ C.cHH * D0.b := by positivity
      simpa [compl] using this
    · have : 0 < D0.x ^ C.cHH * D0.b := by positivity
      simpa [compl] using this
  ·
    intro u0
    simp [compl]

/- English proof (translation)
Introduce `U0 _ W Top _ m f D0 C Xpp hx hb ha hb' hk hLa hB0 hXpp hf haT hw hC hS0 hS1 hTop`. Conclude with `⟨compl D0 C, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, data_completion_bounds D0 C Xpp hx hb ha hb' hk hLa hB0 hXpp hf haT hw hC hS0 hS1 hTop⟩`.
-/
theorem exists_data_completion : DataCompletion := by
  intro U0 _ W Top _ m f D0 C Xpp hx hb ha hb' hk hLa hB0 hXpp hf haT hw hC hS0 hS1 hTop
  exact ⟨compl D0 C, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl,
    data_completion_bounds D0 C Xpp hx hb ha hb' hk hLa hB0 hXpp hf haT hw hC hS0 hS1 hTop⟩

end

/- English proof (translation)
Introduce `H i1 i2 i3 Top i6 m f D0 C Xpp eK K CL D ell N TT T2 a w eT eP η X' θ hHost hId hWin hBN hRest hCost hSize hS0 hS1 hTop`. Take `⟨⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, wC⟩, wEta⟩` from `hWin`. Establish `wC'` using `wC`. Take `⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17⟩` from `wC'`. Establish `hx0 : 0 < D0.x` using `by linarith`.

Establish `hb0 : 0 < D0.b` using `by linarith`. Establish `ha0 : 0 ≤ D0.a` using `le_trans (by positivity) w5`. Establish `hf : 0 < f` using `Fin.pos (eP.symm ⟨0, by simp [PhiSet, InPhi]⟩)`. Establish `hw : ∀ u0 j ρ, 0 < D0.w u0 j ρ`. Introduce `u0 j ρ`.

Rewrite using `[hId.2.1 u0 j ρ]`. Conclude with `hRest.1.2.2.2.2.2.2.1.1 u0 j _ (Finset.mem_filter.1 (eP ρ).2).2`. Establish `hLed` using `data_completion_bounds D0 C Xpp hx0 hb0 ha0 w17 w10 w15 w22 w19 hf (fun t => (w21 t).1) hw ⟨c3, c5, c7, c9, c11, c13⟩ hS0 hS1 hTop`. Establish `hnT : 0 ≤ D0.nT` using `by linarith`. Use `⟨H, i1, i2, i3, fun _ => Unit, inferInstance, inferInstance, Top, i6, m, f, compl D0 C, C, Xpp, D, ell, N, TT, T2, a, w, eT, eP, η, X', θ, rfl, rfl, le_refl _, le_refl _, le_refl _, hHost, hId, hLed, ?_, hBN, hRest, hCost, hSize⟩` and prove the remaining obligations.

Use `⟨⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, ?_, le_refl _, le_refl _, wC⟩, ?_⟩` and prove the remaining obligations. Use `show (0 : ℝ) ≤ 1 / 2`. Evaluate the numerical expressions. Establish `h1 : 0 ≤ K * D0.x ^ D0.ε * (D0.nT * D0.a)`. Establish `hK : 0 ≤ K` using `le_trans c1 c2`.

Check the signs of the components of the expression. Use `show ((0 : ℝ) + 4 * Real.sqrt 0) * (D0.x ^ C.cHH * D0.b) ≤ K * D0.x ^ D0.ε * (D0.nT * D0.a)`. Simplify using `using h1`.
-/
theorem chain_reduction_of_top : ChainCoreOfTop := by
  intro H i1 i2 i3 Top i6 m f D0 C Xpp eK K CL D ell N TT T2 a w eT eP η X' θ hHost hId hWin hBN hRest hCost hSize
    hS0 hS1 hTop
  obtain ⟨⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22,
    w23, w24, w25, w26, w27, wC⟩, wEta⟩ := hWin
  have wC' := wC
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17⟩ := wC'
  have hx0 : 0 < D0.x := by linarith
  have hb0 : 0 < D0.b := by linarith
  have ha0 : 0 ≤ D0.a := le_trans (by positivity) w5
  have hf : 0 < f := Fin.pos (eP.symm ⟨0, by simp [PhiSet, InPhi]⟩)
  have hw : ∀ u0 j ρ, 0 < D0.w u0 j ρ := by
    intro u0 j ρ
    rw [hId.2.1 u0 j ρ]
    exact hRest.1.2.2.2.2.2.2.1.1 u0 j _ (Finset.mem_filter.1 (eP ρ).2).2
  have hLed := data_completion_bounds D0 C Xpp hx0 hb0 ha0 w17 w10 w15 w22 w19 hf (fun t => (w21 t).1) hw
    ⟨c3, c5, c7, c9, c11, c13⟩ hS0 hS1 hTop
  have hnT : 0 ≤ D0.nT := by linarith
  refine ⟨H, i1, i2, i3, fun _ => Unit, inferInstance, inferInstance, Top, i6, m, f, compl D0 C, C, Xpp, D, ell, N,
    TT, T2, a, w, eT, eP, η, X', θ, rfl, rfl, le_refl _, le_refl _, le_refl _, hHost, hId, hLed, ?_, hBN, hRest, hCost,
    hSize⟩
  refine ⟨⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22,
    w23, w24, ?_, le_refl _, le_refl _, wC⟩, ?_⟩
  · show (0 : ℝ) ≤ 1 / 2
    norm_num
  · have h1 : 0 ≤ K * D0.x ^ D0.ε * (D0.nT * D0.a) := by
      have hK : 0 ≤ K := le_trans c1 c2
      positivity
    show ((0 : ℝ) + 4 * Real.sqrt 0) * (D0.x ^ C.cHH * D0.b) ≤ K * D0.x ^ D0.ε * (D0.nT * D0.a)
    simpa using h1

namespace Model

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

/- English proof (translation)
Establish `h11 : (1 : ZMod 2) + 1 = 0` using `rfl`. Simplify using `[sgc0, h11]`.
-/
lemma model_sigma_add_self : (sgc0 : E0 × H) + sgc0 = 0 := by
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  simp [sgc0, h11]

def Id : AddSubgroup (E0 × H) where
  carrier := {x | x = 0 ∨ x = sgc0}
  zero_mem' := Or.inl rfl
  add_mem' := by
    rintro a b (rfl | rfl) (rfl | rfl)
    · left; simp
    · right; simp
    · right; simp
    · left; exact model_sigma_add_self
  neg_mem' := by
    rintro a (rfl | rfl)
    · left; simp
    · right; exact neg_eq_of_add_eq_zero_left model_sigma_add_self

def DA : ArithData H where
  q1 := 11
  d := 7
  inertia p := if p = 7 then Id else ⊥
  frob _ := 0

/- English proof (translation)
Use `show Nat.Prime 11; norm_num d_prime := by show Nat.Prime 7; norm_num first_prime_ne_two := by show (11 : ℕ) ≠ 2; norm_num d_ne_two := by show (7 : ℕ) ≠ 2; norm_num firstPrime_ne_secondPrime := by show (11 : ℕ) ≠ 7; norm_num unram := by`. Introduce `p _ _ _ h7`. Establish `h7' : p ≠ 7` using `h7`. Use `show (if p = 7 then Id else ⊥) = ⊥`. Rewrite using `[if_neg h7']`.

Use `split_inertia := by`. Introduce `p hp x hx`. Establish `h7 : p ≠ 7`. Break down `hp with rfl | rfl` into its components or cases. Evaluate the numerical expressions.

Use `show (11 : ℕ) ≠ 7`. Evaluate the numerical expressions. Establish `hx' : x ∈ (if p = 7 then Id else (⊥ : AddSubgroup (E0 × H)))` using `hx`. Rewrite `hx'` using `[if_neg h7, AddSubgroup.mem_bot]`. Substitute `hx'` using the available equality.

Simplify using `[InPhi]`. Use `split_frob := by`. Introduce `p _`. Use `show InPhi (0 : E0 × H)`. Simplify using `[InPhi]`.

Use `inertia_d := by`. Introduce `x`. Use `show x ∈ (if (7 : ℕ) = 7 then Id else (⊥ : AddSubgroup (E0 × H))) ↔ _`. Rewrite using `[if_pos rfl]`. Conclude with `Iff.rfl`.
-/
lemma hostFacts_DA : HostFacts (DA (H := H)) where
  first_prime_prime := by show Nat.Prime 11; norm_num
  d_prime := by show Nat.Prime 7; norm_num
  first_prime_ne_two := by show (11 : ℕ) ≠ 2; norm_num
  d_ne_two := by show (7 : ℕ) ≠ 2; norm_num
  firstPrime_ne_secondPrime := by show (11 : ℕ) ≠ 7; norm_num
  unram := by
    intro p _ _ _ h7
    have h7' : p ≠ 7 := h7
    show (if p = 7 then Id else ⊥) = ⊥
    rw [if_neg h7']
  split_inertia := by
    intro p hp x hx
    have h7 : p ≠ 7 := by
      rcases hp with rfl | rfl
      · norm_num
      · show (11 : ℕ) ≠ 7; norm_num
    have hx' : x ∈ (if p = 7 then Id else (⊥ : AddSubgroup (E0 × H))) := hx
    rw [if_neg h7, AddSubgroup.mem_bot] at hx'
    subst hx'
    simp [InPhi]
  split_frob := by
    intro p _
    show InPhi (0 : E0 × H)
    simp [InPhi]
  inertia_d := by
    intro x
    show x ∈ (if (7 : ℕ) = 7 then Id else (⊥ : AddSubgroup (E0 × H))) ↔ _
    rw [if_pos rfl]
    exact Iff.rfl

/- English proof (translation)
Unfold `fPl PhiSet`. Establish `: (univ.filter (InPhi (H` using `H))) = (({((0:ZMod 2),(0:ZMod 2)), (0,1)} : Finset E0) ×ˢ (univ : Finset H)) := by`. Use extensionality with `⟨⟨a, b⟩, h⟩`. Simplify using `only [mem_filter, mem_univ, true_and, InPhi, mem_product, mem_insert, mem_singleton, Prod.mk.injEq, and_true]`. Use `revert a b`.

Evaluate the decidable proposition. Rewrite using `[this, card_product]`. Simplify using `[Finset.card_univ]`.
-/
lemma fPl_eq : fPl H = 2 * (Fintype.card H : ℝ) := by
  unfold fPl PhiSet
  have : (univ.filter (InPhi (H := H))) = (({((0:ZMod 2),(0:ZMod 2)), (0,1)} : Finset E0) ×ˢ (univ : Finset H)) := by
    ext ⟨⟨a, b⟩, h⟩
    simp only [mem_filter, mem_univ, true_and, InPhi, mem_product, mem_insert, mem_singleton, Prod.mk.injEq, and_true]
    revert a b; decide
  rw [this, card_product]
  simp [Finset.card_univ]

def wM : H → Fin 1 → E0 × H → ℝ := fun u0 _ ρ => if IsThickAt univ u0 ρ then 2 ^ 60 else 2 ^ 56

def aM : H → ℝ := fun _ => 65536 * 2 ^ 60

def fM (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] : ℕ := (PhiSet (H := H)).card

def ePM : Fin (fM H) ≃ PhiSet (H := H) := (Finset.equivFin _).symm

def modelData : Data H (fun _ => Unit) (univ : Finset H) 1 (fM H) where
  x := 65536
  ε := 1
  a := 65536 * 2 ^ 60
  b := 2 ^ 60
  b' := 2 ^ 56
  k := 65536
  L := 60
  La := 100
  B0 := 0
  Nc := 0
  gam := Real.eulerMascheroniConstant
  LpL := 0
  v := 1
  lg := 0
  logGam := 0
  aT := fun _ => 65536 * 2 ^ 60
  w := fun u0 j ρ => wM u0 j (ePM ρ)
  d := fun _ _ => 1
  T := fun _ _ => 1
  muN := fun _ _ => 0
  muMaxN := fun _ _ => 0
  h := fun _ _ => 0
  muM := fun _ _ => 0
  muMaxM := fun _ _ => 0
  EeJ := fun _ _ _ => 0
  muCC := fun _ => 0
  muMinCC := fun _ => 0
  Fo := fun _ => 0
  Ga := fun _ => 0
  Ta := fun _ => 0
  ASK := fun u0 => ∑ t ∈ (univ : Finset H), ∑ j : Fin 1, ASK DA 1048576 (aM t) t (wM u0 j)
  IO := fun _ => 0
  HH := fun _ => 1
  del := fun _ => 0
  η := fun _ => 0
  e := fun _ => 0
  delBar := 0
  etaBar := 0
  eBar := 0

def CM : Consts := ⟨1, 1, 1, 1, 1, 1, 1, 1, 1, 1⟩

/- English proof (translation)
Unfold `wM`. Use `split_ifs`. Conclude with `Or.inl rfl`. Conclude with `Or.inr rfl`.
-/
lemma wM_cases (u0 : H) (j : Fin 1) (ρ : E0 × H) : wM u0 j ρ = 2 ^ 60 ∨ wM u0 j ρ = 2 ^ 56 := by
  unfold wM; split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/- English proof (translation)
Establish `h2 : Real.log 2 ≤ 2 - 1` using `Real.log_le_sub_one_of_pos (by norm_num)`. Establish `h0 : 0 ≤ Real.log 2` using `Real.log_nonneg (by norm_num)`. Apply the tactic sequence `rcases wM_cases u0 j ρ with h | h <;> rw [h, Real.log_pow] <;> constructor <;> push_cast <;> nlinarith`.
-/
lemma log_wM (u0 : H) (j : Fin 1) (ρ : E0 × H) : 0 ≤ Real.log (wM u0 j ρ) ∧ Real.log (wM u0 j ρ) ≤ 60 := by
  have h2 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rcases wM_cases u0 j ρ with h | h <;> rw [h, Real.log_pow] <;> constructor <;> push_cast <;> nlinarith

/- English proof (translation)
The claim follows from `Fin.pos (ePM.symm ⟨0, by simp [PhiSet, InPhi]⟩)`.
-/
lemma fM_pos : 0 < fM H := Fin.pos (ePM.symm ⟨0, by simp [PhiSet, InPhi]⟩)

/- English proof (translation)
Use `⟨fun τ => ?_, fun u0 j ρ => ?_, ?_, ?_, fun u0 => ?_⟩` and prove the remaining obligations. Simplify using `only [modelData, aM]`. Simplify using `only [modelData]`. Simplify using `only [modelData]`. Simplify using `only [modelData, Complex.zero_re]`.

Simplify using `only [modelData]`.
-/
lemma identM : Ident (modelData (H := H)) DA 1048576 (fun _ => 0) univ aM wM (Equiv.refl _) ePM := by
  refine ⟨fun τ => ?_, fun u0 j ρ => ?_, ?_, ?_, fun u0 => ?_⟩
  · simp only [modelData, aM]
  · simp only [modelData]
  · simp only [modelData]
  · simp only [modelData, Complex.zero_re]
  · simp only [modelData]

/- English proof (translation)
Establish `hx : (1 : ℝ) ≤ 65536` using `by norm_num`. Establish `hnT : (modelData (H` using `H)).nT = 65536 := by`. Unfold `Data.nT`. Rewrite using `[Fintype.card_coe, Finset.card_univ, cardHM]`. Evaluate the numerical expressions.

Establish `hcu : (univ : Finset H).card = 65536` using `by rw [Finset.card_univ, cardHM]`. Use `⟨(univ : Finset H), inferInstance, 1, fM H, modelData, CM, 0, 1, 1, DA, fun _ => 0, 1048576, univ, univ, aM, wM, Equiv.refl _, ePM, 0, 2 ^ 20, 1 / 2 ^ 60, hostFacts_DA, identM, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, by positivity, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩⟩` and prove the remaining obligations. Use `⟨hx, by norm_num [modelData], by norm_num [modelData], by norm_num [modelData], by norm_num [modelData], by rw [hnT]; norm_num, ?_, by norm_num [modelData], by norm_num, by norm_num [modelData], by norm_num [modelData], by norm_num [modelData], by norm_num [modelData], by norm_nu …` and prove the remaining obligations. Establish `: (1 : ℝ) ≤ (65536 : ℝ) ^ ((1 : ℝ) / 2 + 1 / 2)` using `Real.one_le_rpow hx (by norm_num)`. Simplify `this` using `[modelData]`.

Establish `hl2 : 0 ≤ Real.log 2` using `Real.log_nonneg (by norm_num)`. Simplify using `only [Fintype.card_unit, Nat.cast_one, Real.log_one]`. Conclude with `mul_nonneg (by norm_num [modelData]) hl2`. Apply the tactic sequence `refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [CM]`. Rewrite using `[hnT]`.

Evaluate the numerical expressions using `[modelData]`. Use `show (0 : ℝ) ≤ _`. Establish `: (0 : ℝ) < (modelData (H` using `H)).x := by norm_num [modelData]`. Establish `: (0 : ℝ) < (modelData (H` using `H)).b := by norm_num [modelData]`. Check the signs of the components of the expression.

Use `show (0 : ℝ) ≤ _`. Establish `: (0 : ℝ) < (modelData (H` using `H)).x := by norm_num [modelData]`. Establish `: (0 : ℝ) < (modelData (H` using `H)).b := by norm_num [modelData]`. Establish `: (0 : ℝ) < (modelData (H` using `H)).k := by norm_num [modelData]`. Check the signs of the components of the expression.

Use `⟨le_refl _, by positivity, by norm_num [modelData], by norm_num [modelData], by positivity, fun t _ => ?_, ⟨fun u0 j ρ _ => ?_, fun u0 j ρ h => ?_, fun u0 j ρ _ h => ?_⟩, fun u0 j t ρ _ _ => ?_⟩` and prove the remaining obligations. Evaluate the numerical expressions using `[modelData, aM]`. Apply the tactic sequence `rcases wM_cases u0 j ρ with h | h <;> rw [h] <;> positivity`. Establish `: wM u0 j ρ = 2 ^ 60` using `by unfold wM; rw [if_pos h]`. Rewrite using `[this]`.

Evaluate the numerical expressions using `[modelData]`. Establish `: wM u0 j ρ = 2 ^ 56` using `by unfold wM; rw [if_neg h]`. Rewrite using `[this]`. Evaluate the numerical expressions using `[modelData]`. Apply the tactic sequence `rcases wM_cases u0 j ρ with h | h <;> rw [h] <;> norm_num [aM]`.

Rewrite using `[fPl_eq, cardHM]`. Evaluate the numerical expressions using `[modelData]`. Rewrite using `[fPl_eq, cardHM]`. Evaluate the numerical expressions using `[modelData]`. Evaluate the numerical expressions using `[modelData]`.

Establish `: (65536 : ℝ) ^ (-((1 : ℝ) / 8)) ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)`. Rewrite using `[hcu, cardHM]`. Use `show (65536 : ℝ) ^ (-((1 : ℝ) / 8)) * ((65536 : ℕ) : ℝ) / 2 ≤ ((65536 : ℕ) : ℝ)`. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities.

Establish `: (65536 : ℝ) ^ (-(1 : ℝ)) ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)`. Rewrite using `[hcu, cardHM]`. Use `show (65536 : ℝ) ^ (-(1 : ℝ)) ≤ ((65536 : ℕ) : ℝ) / ((65536 : ℕ) : ℝ)`. Rewrite using `[div_self (by norm_num)]`. Conclude with `this`.

Establish `: (65536 : ℝ) ^ ((1 : ℝ) / 2 - 1) ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num) show (65536 : ℝ) ^ ((1 : ℝ) / 2 - 1) ≤ ((1 : ℕ) : ℝ)`. Simplify using `using this`. Establish `h3 : (65536 : ℝ) ^ (-1 : ℝ) ≤ (65536 : ℝ) ^ ((1 : ℝ) / 2 - 1)` using `Real.rpow_le_rpow_of_exponent_le hx (by norm_num)`. Rewrite `h3` using `[Real.rpow_neg_one]`. Rewrite using `[cardHM]`.

Use `show (65536 : ℝ) ≤ ((65536 : ℕ) : ℝ) ^ 2 * (65536 : ℝ) ^ ((1 : ℝ) / 2 - 1)`. Use `push_cast`. Establish `h4 : (65536 : ℝ) = 65536 ^ 2 * (65536 : ℝ)⁻¹` using `by norm_num`. Combine the equalities or inequalities in the displayed calculation. Introduce `u0`.

Use `Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (Finset.sum_nonneg fun ρ _ => ?_)` and prove the remaining obligations. Conclude with `(log_wM u0 j (ePM ρ)).1`. Introduce `u0`. Establish `hf : (0 : ℝ) < (fM H : ℝ)` using `by exact_mod_cast fM_pos`. Establish `h1 : ∀ j : Fin 1, (1 / (fM H : ℝ)) * ∑ ρ : Fin (fM H), Real.log (modelData.w u0 j ρ) ≤ 60`.

Introduce `j`. Establish `h2 : ∑ ρ : Fin (fM H), Real.log (modelData.w u0 j ρ) ≤ ∑ _ρ : Fin (fM H), (60 : ℝ)` using `Finset.sum_le_sum fun ρ _ => (log_wM u0 j (ePM ρ)).2`. Rewrite `h2` using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `h3` using `Finset.sum_le_sum (s := (univ : Finset (Fin 1))) fun j _ => h1 j`.

Simplify `h3` using `[CM, modelData]`. Evaluate the numerical expressions using `[modelData]`. Use `le_rpow_26 _ _ (by norm_num [modelData]) ?_` and prove the remaining obligations. Establish `h1 : (26 : ℝ) ^ ((8 : ℝ) / (3 * 1)) ≤ (26 : ℝ) ^ ((3 : ℕ) : ℝ)` using `Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)`. Rewrite `h1` using `[Real.rpow_natCast]`.

Use `show (26 : ℝ) ^ ((8 : ℝ) / (3 * 1)) ≤ 65536`. Combine the linear relations using `[h1, (by norm_num : (26 : ℝ) ^ 3 ≤ 65536)]`. Use `Real.log_le_self (by norm_num : (0 : ℝ) ≤ 65536)` as an intermediate fact. Simplify `this` using `[modelData]`. Evaluate the numerical expressions using `[modelData, CM, KBig]`.
-/
theorem sizesModelAt (cardHM : Fintype.card H = 65536) : SizesModelAt H := by
  have hx : (1 : ℝ) ≤ 65536 := by norm_num
  have hnT : (modelData (H := H)).nT = 65536 := by
    unfold Data.nT
    rw [Fintype.card_coe, Finset.card_univ, cardHM]
    norm_num
  have hcu : (univ : Finset H).card = 65536 := by rw [Finset.card_univ, cardHM]
  refine ⟨(univ : Finset H), inferInstance, 1, fM H, modelData, CM, 0, 1, 1,
    DA, fun _ => 0, 1048576, univ, univ, aM, wM, Equiv.refl _, ePM, 0, 2 ^ 20, 1 / 2 ^ 60,
    hostFacts_DA, identM, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_,
    by positivity, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩⟩
  ·
    refine ⟨hx, by norm_num [modelData], by norm_num [modelData], by norm_num [modelData], by norm_num [modelData], by rw [hnT]; norm_num, ?_,
      by norm_num [modelData], by norm_num, by norm_num [modelData], by norm_num [modelData], by norm_num [modelData], by norm_num [modelData],
      by norm_num [modelData], by norm_num [modelData], by norm_num [modelData], by norm_num [modelData], by norm_num [modelData], le_refl _,
      by norm_num [modelData], fun _ => by norm_num [modelData], le_refl _, le_refl _, fun _ => ?_, by norm_num [modelData], le_refl _,
      le_refl _, ?_⟩
    · have : (1 : ℝ) ≤ (65536 : ℝ) ^ ((1 : ℝ) / 2 + 1 / 2) := Real.one_le_rpow hx (by norm_num)
      simpa [modelData] using this
    · have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      simp only [Fintype.card_unit, Nat.cast_one, Real.log_one]
      exact mul_nonneg (by norm_num [modelData]) hl2
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [CM]
  ·
    rw [hnT]
    norm_num [modelData]
  ·
    show (0 : ℝ) ≤ _
    have : (0 : ℝ) < (modelData (H := H)).x := by norm_num [modelData]
    have : (0 : ℝ) < (modelData (H := H)).b := by norm_num [modelData]
    positivity
  ·
    show (0 : ℝ) ≤ _
    have : (0 : ℝ) < (modelData (H := H)).x := by norm_num [modelData]
    have : (0 : ℝ) < (modelData (H := H)).b := by norm_num [modelData]
    have : (0 : ℝ) < (modelData (H := H)).k := by norm_num [modelData]
    positivity
  ·
    refine ⟨le_refl _, by positivity, by norm_num [modelData], by norm_num [modelData], by positivity, fun t _ => ?_,
      ⟨fun u0 j ρ _ => ?_, fun u0 j ρ h => ?_, fun u0 j ρ _ h => ?_⟩, fun u0 j t ρ _ _ => ?_⟩
    · norm_num [modelData, aM]
    · rcases wM_cases u0 j ρ with h | h <;> rw [h] <;> positivity
    · have : wM u0 j ρ = 2 ^ 60 := by unfold wM; rw [if_pos h]
      rw [this]
      norm_num [modelData]
    · have : wM u0 j ρ = 2 ^ 56 := by unfold wM; rw [if_neg h]
      rw [this]
      norm_num [modelData]
    · rcases wM_cases u0 j ρ with h | h <;> rw [h] <;> norm_num [aM]
  ·
    rw [fPl_eq, cardHM]
    norm_num [modelData]
  ·
    rw [fPl_eq, cardHM]
    norm_num [modelData]
  · norm_num [modelData]
  · have : (65536 : ℝ) ^ (-((1 : ℝ) / 8)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
    rw [hcu, cardHM]
    show (65536 : ℝ) ^ (-((1 : ℝ) / 8)) * ((65536 : ℕ) : ℝ) / 2 ≤ ((65536 : ℕ) : ℝ)
    push_cast
    nlinarith
  · have : (65536 : ℝ) ^ (-(1 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
    rw [hcu, cardHM]
    show (65536 : ℝ) ^ (-(1 : ℝ)) ≤ ((65536 : ℕ) : ℝ) / ((65536 : ℕ) : ℝ)
    rw [div_self (by norm_num)]
    exact this
  · have : (65536 : ℝ) ^ ((1 : ℝ) / 2 - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
    show (65536 : ℝ) ^ ((1 : ℝ) / 2 - 1) ≤ ((1 : ℕ) : ℝ)
    simpa using this
  · have h3 : (65536 : ℝ) ^ (-1 : ℝ) ≤ (65536 : ℝ) ^ ((1 : ℝ) / 2 - 1) :=
      Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
    rw [Real.rpow_neg_one] at h3
    rw [cardHM]
    show (65536 : ℝ) ≤ ((65536 : ℕ) : ℝ) ^ 2 * (65536 : ℝ) ^ ((1 : ℝ) / 2 - 1)
    push_cast
    have h4 : (65536 : ℝ) = 65536 ^ 2 * (65536 : ℝ)⁻¹ := by norm_num
    calc (65536 : ℝ) = 65536 ^ 2 * (65536 : ℝ)⁻¹ := h4
      _ ≤ 65536 ^ 2 * (65536 : ℝ) ^ ((1 : ℝ) / 2 - 1) := mul_le_mul_of_nonneg_left h3 (by norm_num)
  ·
    intro u0
    refine Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (Finset.sum_nonneg fun ρ _ => ?_)
    exact (log_wM u0 j (ePM ρ)).1
  ·
    intro u0
    have hf : (0 : ℝ) < (fM H : ℝ) := by exact_mod_cast fM_pos
    have h1 : ∀ j : Fin 1, (1 / (fM H : ℝ)) * ∑ ρ : Fin (fM H), Real.log (modelData.w u0 j ρ) ≤ 60 := by
      intro j
      have h2 : ∑ ρ : Fin (fM H), Real.log (modelData.w u0 j ρ) ≤ ∑ _ρ : Fin (fM H), (60 : ℝ) :=
        Finset.sum_le_sum fun ρ _ => (log_wM u0 j (ePM ρ)).2
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
      calc (1 / (fM H : ℝ)) * ∑ ρ : Fin (fM H), Real.log (modelData.w u0 j ρ) ≤ (1 / (fM H : ℝ)) * ((fM H : ℝ) * 60) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 60 := by field_simp
    have h3 := Finset.sum_le_sum (s := (univ : Finset (Fin 1))) fun j _ => h1 j
    simpa [CM, modelData] using h3
  · norm_num [modelData]
  · refine le_rpow_26 _ _ (by norm_num [modelData]) ?_
    have h1 : (26 : ℝ) ^ ((8 : ℝ) / (3 * 1)) ≤ (26 : ℝ) ^ ((3 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    rw [Real.rpow_natCast] at h1
    show (26 : ℝ) ^ ((8 : ℝ) / (3 * 1)) ≤ 65536
    linarith [h1, (by norm_num : (26 : ℝ) ^ 3 ≤ 65536)]
  · have := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 65536)
    simpa [modelData] using this
  · norm_num [modelData, CM, KBig]

end

end Model

/- English proof (translation)
Assemble the required witnesses or components as `⟨ZMod 65536, inferInstance, inferInstance, inferInstance, Model.sizesModelAt (ZMod.card 65536)⟩`.
-/
theorem chain_sizes_model : ChainSizesModel :=
  ⟨ZMod 65536, inferInstance, inferInstance, inferInstance, Model.sizesModelAt (ZMod.card 65536)⟩

end Formalism.LFunctionChainParameters.LChain

section Check
open Formalism.LFunctionChainParameters.LChain
end Check

namespace Formalism.LFunctionChainParameters.LChain

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.ConditionalMainTheorem Formalism.LFunctionChainParameters.LErr

/- English proof (translation)
Introduce `H _ _ _ W _ _ Top _ m f Dd C Xpp D ell N TT a w eT eP hId hLed u0`. Take `⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩` from `hLed`. Rewrite using `[← hId.2.2.2.2 u0]`. Conclude with `each_unit_bound_statement Dd C Xpp l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 u0`.
-/
theorem top_each_bound : CoreTopEach := by
  intro H _ _ _ W _ _ Top _ m f Dd C Xpp D ell N TT a w eT eP hId hLed u0
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩ := hLed
  rw [← hId.2.2.2.2 u0]
  exact each_unit_bound_statement Dd C Xpp l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 u0

/- English proof (translation)
Take `⟨⟨hx, hε, hε1, hb, hxb, hnT, hm, hxm, heK, hk1, hkx, hka, hL0, hL, hLa0, hLa, hb', hkb', hX0, hXa, haT, hB0, hNc, hlW, hdel, -, -, hC⟩, het⟩` from `hW`. Take `⟨c1, c1', c2, c2', c3, c3', c4, c4', c5, c5', c6, c6', c7, c7', hD, hLs, hHH⟩` from `hC`. Take `⟨hlog, hbig⟩` from `hX`. Establish `hx0 : 0 < D.x` using `by linarith only [hx]`. Establish `hy : 1 ≤ D.x ^ D.ε` using `Real.one_le_rpow hx hε.le`.

Establish `hyD : 1 ≤ D.x ^ (C.eDiv * D.ε)` using `Real.one_le_rpow hx (mul_nonneg hD hε.le)`. Establish `hyL : 1 ≤ D.x ^ (C.eLoss * D.ε)` using `Real.one_le_rpow hx (mul_nonneg hLs hε.le)`. Establish `hb0 : 0 ≤ D.b` using `by linarith only [hb]`. Establish `hbxb : D.b ≤ D.x * D.b` using `le_mul_of_one_le_left hb0 hx`. Establish `hba : D.b ≤ D.a` using `hbxb.trans hxb`.

Establish `ha1 : 1 ≤ D.a` using `hb.trans hba`. Establish `hM : (0 : ℝ) ≤ (m : ℝ)` using `Nat.cast_nonneg m`. Establish `hk : 0 < D.k` using `by linarith only [hk1]`. Establish `hmx : (m : ℝ) ≤ D.x`. Use `hm.trans ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Establish `hMk : (m : ℝ) ≤ D.k` using `(le_mul_of_one_le_left hM hx).trans hxm`. Establish `hMb : (m : ℝ) * D.b ≤ D.a` using `(mul_le_mul_of_nonneg_right hmx hb0).trans hxb`. Establish `hsA0 : 0 ≤ D.sumA` using `Finset.sum_nonneg (fun t _ => (haT t).1)`. Establish `hsA : D.sumA ≤ 2 * (D.nT * D.a)`.

Unfold `Data.sumA Data.nT`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hlWk : Real.log (Fintype.card (W u0) : ℝ) ≤ D.a` using `((hlW u0).trans (sub_three_mul_log_two_le hk.le)).trans hka`.

Establish `hlk0 : 0 ≤ Real.log D.k` using `Real.log_nonneg hk1`. Establish `hlk : Real.log D.k ≤ (1 + eK) * D.x ^ D.ε` using `log_le_of_le_rpow hx heK hk hkx hlog hy`. Establish `hxH : 1 ≤ D.x ^ C.cHH` using `Real.one_le_rpow hx hHH`. Establish `hlH0 : 0 ≤ Real.log (1 + D.x ^ C.cHH)` using `Real.log_nonneg (by linarith only [hxH])`. Establish `hlH : Real.log (1 + D.x ^ C.cHH) ≤ (1 + C.cHH) * D.x ^ D.ε` using `log_one_add_rpow_le hx hHH hlog hy`.

Take `⟨hdI0, hdI⟩` from `inv_one_sub_le_two hdel`. Establish `hpow : D.x ^ (CErr C * D.ε) = D.x ^ (C.eDiv * D.ε) * D.x ^ (C.eLoss * D.ε) * D.x ^ D.ε * D.x ^ D.ε * D.x ^ D.ε`. Rewrite using `[← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0]`. Use `congr 1`. Unfold `CErr`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hpow]`. Unfold `KBig at hbig`. Use `core_ineq (nT := D.nT) (a := D.a) (b := D.b) (b' := D.b') (k := D.k) (L := D.L) (La := D.La) (B0 := D.B0) (Nc := D.Nc) (M := (m : ℝ)) (sA := D.sumA) (lW := Real.log (Fintype.card (W u0) : ℝ)) (lk := Real.log D.k) (lH := Real.log (1 + D.x ^ C.cHH)) (dI := (1 - D.delBar)⁻¹) (et := …` as an intermediate fact. Unfold `ErrX5at UBar5 MLo5 Data.Vvar Data.LoP ErrText`.

Conclude with `this`.
-/
lemma errX5at_le {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ} (D : Data U0 W Top m f) (C : Consts) (Xpp eK K : ℝ)
    (hW : ErrWindows D C Xpp eK K) (hX : LargeX D.x D.ε K C.cHH eK) (u0 : U0) :
    ErrX5at D C Xpp u0 ≤ D.x ^ (CErr C * D.ε) * ErrText D := by
  obtain ⟨⟨hx, hε, hε1, hb, hxb, hnT, hm, hxm, heK, hk1, hkx, hka, hL0, hL, hLa0, hLa, hb', hkb', hX0,
    hXa, haT, hB0, hNc, hlW, hdel, -, -, hC⟩, het⟩ := hW
  obtain ⟨c1, c1', c2, c2', c3, c3', c4, c4', c5, c5', c6, c6', c7, c7', hD, hLs, hHH⟩ := hC
  obtain ⟨hlog, hbig⟩ := hX
  have hx0 : 0 < D.x := by linarith only [hx]
  have hy : 1 ≤ D.x ^ D.ε := Real.one_le_rpow hx hε.le
  have hyD : 1 ≤ D.x ^ (C.eDiv * D.ε) := Real.one_le_rpow hx (mul_nonneg hD hε.le)
  have hyL : 1 ≤ D.x ^ (C.eLoss * D.ε) := Real.one_le_rpow hx (mul_nonneg hLs hε.le)
  have hb0 : 0 ≤ D.b := by linarith only [hb]
  have hbxb : D.b ≤ D.x * D.b := le_mul_of_one_le_left hb0 hx
  have hba : D.b ≤ D.a := hbxb.trans hxb
  have ha1 : 1 ≤ D.a := hb.trans hba
  have hM : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hk : 0 < D.k := by linarith only [hk1]
  have hmx : (m : ℝ) ≤ D.x := by
    refine hm.trans ?_
    calc D.x ^ ((1 : ℝ) / 2 + D.ε / 2) ≤ D.x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx (by linarith only [hε1])
      _ = D.x := Real.rpow_one _
  have hMk : (m : ℝ) ≤ D.k := (le_mul_of_one_le_left hM hx).trans hxm
  have hMb : (m : ℝ) * D.b ≤ D.a := (mul_le_mul_of_nonneg_right hmx hb0).trans hxb
  have hsA0 : 0 ≤ D.sumA := Finset.sum_nonneg (fun t _ => (haT t).1)
  have hsA : D.sumA ≤ 2 * (D.nT * D.a) := by
    unfold Data.sumA Data.nT
    calc ∑ t, D.aT t ≤ ∑ _t : Top, 2 * D.a := Finset.sum_le_sum (fun t _ => (haT t).2)
      _ = 2 * ((Fintype.card Top : ℝ) * D.a) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hlWk : Real.log (Fintype.card (W u0) : ℝ) ≤ D.a :=
    ((hlW u0).trans (sub_three_mul_log_two_le hk.le)).trans hka
  have hlk0 : 0 ≤ Real.log D.k := Real.log_nonneg hk1
  have hlk : Real.log D.k ≤ (1 + eK) * D.x ^ D.ε := log_le_of_le_rpow hx heK hk hkx hlog hy
  have hxH : 1 ≤ D.x ^ C.cHH := Real.one_le_rpow hx hHH
  have hlH0 : 0 ≤ Real.log (1 + D.x ^ C.cHH) := Real.log_nonneg (by linarith only [hxH])
  have hlH : Real.log (1 + D.x ^ C.cHH) ≤ (1 + C.cHH) * D.x ^ D.ε :=
    log_one_add_rpow_le hx hHH hlog hy
  obtain ⟨hdI0, hdI⟩ := inv_one_sub_le_two hdel
  have hpow : D.x ^ (CErr C * D.ε)
      = D.x ^ (C.eDiv * D.ε) * D.x ^ (C.eLoss * D.ε) * D.x ^ D.ε * D.x ^ D.ε * D.x ^ D.ε := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
    congr 1
    unfold CErr
    ring
  rw [hpow]
  unfold KBig at hbig
  have := core_ineq (nT := D.nT) (a := D.a) (b := D.b) (b' := D.b') (k := D.k) (L := D.L) (La := D.La)
    (B0 := D.B0) (Nc := D.Nc) (M := (m : ℝ)) (sA := D.sumA)
    (lW := Real.log (Fintype.card (W u0) : ℝ)) (lk := Real.log D.k)
    (lH := Real.log (1 + D.x ^ C.cHH)) (dI := (1 - D.delBar)⁻¹)
    (et := (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b)) (Xpp := Xpp)
    (y := D.x ^ D.ε) (yD := D.x ^ (C.eDiv * D.ε)) (yL := D.x ^ (C.eLoss * D.ε)) (K := K)
    (h := 1 + C.cHH) (g := 1 + eK)
    hy hyD hyL hnT ha1 hb0 hba hM hk hMk hMb hL0 hL hLa0 hLa hb' hkb' hX0 hXa hsA0 hsA hB0 hNc hlWk
    hlk0 hlk hlH0 hlH hdI0 hdI het c1 c1' c2 c2' c3 c3' c4 c4' c5 c5' c6 c6' c7 c7'
    (by linarith only [hHH]) (by linarith only [heK]) hbig
  unfold ErrX5at UBar5 MLo5 Data.Vvar Data.LoP ErrText
  exact this

/- English proof (translation)
Introduce `H _ _ _ W _ _ Top _ m f Dd C Xpp eK K D ell N TT T2 a w eT eP hId hLed hWin hBN hX u0`. Establish `h1` using `top_each_bound Dd C Xpp D ell N TT a w eT eP hId hLed u0`. Establish `h2` using `errX5at_le Dd C Xpp eK K hWin hX u0`. Establish `hx : 1 ≤ Dd.x` using `hWin.1.1`. Establish `hnT : Dd.nT = (TT.card : ℝ)`.

Unfold `Data.nT`. Rewrite using `[Fintype.card_congr eT, Fintype.card_coe]`. Take `⟨hB0, hNc⟩` from `hBN`. Establish `hbr : ErrText Dd ≤ errorBracketSizeWindows Dd.x Dd.ε (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a`. Unfold `ErrText errorBracketSizeWindows`.

Rewrite using `[hnT]`. Use `gcongr`. Establish `hp : 0 ≤ Dd.x ^ (CErr C * Dd.ε)` using `Real.rpow_nonneg (by linarith) _`. Use `mul_le_mul_of_nonneg_left hbr hp` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem top_each_bound_sized : CoreTopEachSized := by
  intro H _ _ _ W _ _ Top _ m f Dd C Xpp eK K D ell N TT T2 a w eT eP hId hLed hWin hBN hX u0
  have h1 := top_each_bound Dd C Xpp D ell N TT a w eT eP hId hLed u0
  have h2 := errX5at_le Dd C Xpp eK K hWin hX u0
  have hx : 1 ≤ Dd.x := hWin.1.1
  have hnT : Dd.nT = (TT.card : ℝ) := by
    unfold Data.nT
    rw [Fintype.card_congr eT, Fintype.card_coe]
  obtain ⟨hB0, hNc⟩ := hBN
  have hbr : ErrText Dd
      ≤ errorBracketSizeWindows Dd.x Dd.ε (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a := by
    unfold ErrText errorBracketSizeWindows
    rw [hnT]
    gcongr
  have hp : 0 ≤ Dd.x ^ (CErr C * Dd.ε) := Real.rpow_nonneg (by linarith) _
  have := mul_le_mul_of_nonneg_left hbr hp
  linarith

/- English proof (translation)
Take `⟨H, i1, i2, i3, W, i4, i5, Top, i6, m, f, Dd, C, Xpp, D, ell, N, TT, T2, a, w, eT, eP, η, X', θ, hx, hε, heD, heL, hcHH, hHost, hId, hLed, hWin, hBN, hRest, hCost, hSize⟩` from `h`. Take `⟨⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, wC⟩, wEta⟩` from `hWin`. Take `⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17⟩` from `wC`. Conclude with `⟨by linarith, by linarith, hε ▸ w2⟩`.
-/
lemma core_exp_nonneg {eD eL K cHH eK CL ε x : ℝ} (h : ChainCore eD eL K cHH eK CL ε x) : 0 ≤ eD ∧ 0 ≤ eL ∧ 0 < ε := by
  obtain ⟨H, i1, i2, i3, W, i4, i5, Top, i6, m, f, Dd, C, Xpp, D, ell, N, TT, T2, a, w, eT, eP, η, X', θ,
    hx, hε, heD, heL, hcHH, hHost, hId, hLed, hWin, hBN, hRest, hCost, hSize⟩ := h
  obtain ⟨⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22,
    w23, w24, w25, w26, w27, wC⟩, wEta⟩ := hWin
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17⟩ := wC
  exact ⟨by linarith, by linarith, hε ▸ w2⟩

/- English proof (translation)
Introduce and unpack `eD eL ε ⟨K, cHH, eK, CL, x₀, h⟩`. Take `⟨-, -, hε⟩` from `core_exp_nonneg (h x₀ (le_refl _))`. Take `⟨Cd, -, hAt⟩` from `chain_at_alt`. Take `⟨x₂, hx₂⟩` from `x_large_eventually K cHH eK Cd CL ε hε`. Conclude with `⟨max x₀ x₂, fun x hx => hAt eD eL ε x ⟨K, cHH, eK, CL, h x (le_trans (le_max_left _ _) hx), hx₂ x (le_trans (le_max_right _ _) hx)⟩⟩`.
-/
theorem chain_epsilon_g : ChainEpsG := by
  rintro eD eL ε ⟨K, cHH, eK, CL, x₀, h⟩
  obtain ⟨-, -, hε⟩ := core_exp_nonneg (h x₀ (le_refl _))
  obtain ⟨Cd, -, hAt⟩ := chain_at_alt
  obtain ⟨x₂, hx₂⟩ := x_large_eventually K cHH eK Cd CL ε hε
  exact ⟨max x₀ x₂, fun x hx => hAt eD eL ε x ⟨K, cHH, eK, CL, h x (le_trans (le_max_left _ _) hx),
    hx₂ x (le_trans (le_max_right _ _) hx)⟩⟩

/- English proof (translation)
Introduce `eD eL ε h s hs`. Take `⟨x₁, hx₁⟩` from `chain_epsilon_g eD eL ε h`. Take `⟨K, cHH, eK, CL, x₀, h⟩` from `h`. Take `⟨h1, h2, hε⟩` from `core_exp_nonneg (h x₀ (le_refl _))`. Establish `hpos : 0 ≤ (eD + eL + 6) * ε` using `by positivity`.

Distinguish the cases in `hsmall : (eD + eL + 6) * ε < 1 / 2`. Conclude with `landau_zero_free_half_plane _ (by linarith) (by linarith) x₁ hx₁ s hs`. Conclude with `riemannZeta_ne_zero_of_one_le_re (by linarith)`.
-/
theorem chain_epsilon_half_plane : ChainEpsHalfPlane := by
  intro eD eL ε h s hs
  obtain ⟨x₁, hx₁⟩ := chain_epsilon_g eD eL ε h
  obtain ⟨K, cHH, eK, CL, x₀, h⟩ := h
  obtain ⟨h1, h2, hε⟩ := core_exp_nonneg (h x₀ (le_refl _))
  have hpos : 0 ≤ (eD + eL + 6) * ε := by positivity
  by_cases hsmall : (eD + eL + 6) * ε < 1 / 2
  · exact landau_zero_free_half_plane _ (by linarith) (by linarith) x₁ hx₁ s hs
  · exact riemannZeta_ne_zero_of_one_le_re (by linarith)

/- English proof (translation)
Introduce `eD eL K cHH eK CL ε hε`. Establish `hc : 0 < (|CL| + 1)⁻¹` using `by positivity`. Take `⟨x₀, hx₀⟩` from `Filter.eventually_atTop.1 (((isLittleO_log_rpow_atTop hε).bound hc).and (Filter.eventually_ge_atTop (2 : ℝ)))`. Use `⟨x₀, fun x hx h => ?_⟩` and prove the remaining obligations. Take `⟨hb, hx2⟩` from `hx₀ x hx`.

Establish `hlog : 0 < Real.log x` using `Real.log_pos (by linarith)`. Rewrite `hb` using `[Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _), Real.norm_of_nonneg hlog.le]`. Establish `h1 : CL * Real.log x ≤ x ^ ε`. Establish `h2 : (|CL| + 1) * Real.log x ≤ (|CL| + 1) * ((|CL| + 1)⁻¹ * x ^ ε)` using `by gcongr`. Rewrite `h2` using `[mul_inv_cancel_left₀ (by positivity)]`.

Establish `h3 : CL * Real.log x ≤ |CL| * Real.log x` using `by gcongr; exact le_abs_self CL`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨H, i1, i2, i3, W, i4, i5, Top, i6, m, f, Dd, C, Xpp, D, ell, N, TT, T2, a, w, eT, eP, η, X', θ, hx', hε', heD, heL, hcHH, hHost, hId, hLed, hWin, hBN, ⟨r1, r2, r3⟩, hCost, hSize⟩` from `h`. Use `⟨H, i1, i2, i3, W, i4, i5, Top, i6, m, f, Dd, C, Xpp, D, ell, N, TT, T2, a, w, eT, eP, η, X', θ, hx', hε', heD, heL, hcHH, hHost, hId, hLed, hWin, hBN, ⟨r1, r2, fun ψ hψ => ⟨(r3 ψ hψ).1, ?_⟩⟩, hCost, hSize⟩` and prove the remaining obligations. Rewrite using `[div_mul_cancel₀ _ hlog.ne']`.

Conclude with `(r3 ψ hψ).2.trans h1`.
-/
theorem chain_reduction_weak_l : ChainCoreWeakL := by
  intro eD eL K cHH eK CL ε hε
  have hc : 0 < (|CL| + 1)⁻¹ := by positivity
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1
    (((isLittleO_log_rpow_atTop hε).bound hc).and (Filter.eventually_ge_atTop (2 : ℝ)))
  refine ⟨x₀, fun x hx h => ?_⟩
  obtain ⟨hb, hx2⟩ := hx₀ x hx
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _), Real.norm_of_nonneg hlog.le] at hb
  have h1 : CL * Real.log x ≤ x ^ ε := by
    have h2 : (|CL| + 1) * Real.log x ≤ (|CL| + 1) * ((|CL| + 1)⁻¹ * x ^ ε) := by gcongr
    rw [mul_inv_cancel_left₀ (by positivity)] at h2
    have h3 : CL * Real.log x ≤ |CL| * Real.log x := by gcongr; exact le_abs_self CL
    linarith
  obtain ⟨H, i1, i2, i3, W, i4, i5, Top, i6, m, f, Dd, C, Xpp, D, ell, N, TT, T2, a, w, eT, eP, η, X', θ,
    hx', hε', heD, heL, hcHH, hHost, hId, hLed, hWin, hBN, ⟨r1, r2, r3⟩, hCost, hSize⟩ := h
  refine ⟨H, i1, i2, i3, W, i4, i5, Top, i6, m, f, Dd, C, Xpp, D, ell, N, TT, T2, a, w, eT, eP, η, X', θ,
    hx', hε', heD, heL, hcHH, hHost, hId, hLed, hWin, hBN, ⟨r1, r2, fun ψ hψ => ⟨(r3 ψ hψ).1, ?_⟩⟩, hCost, hSize⟩
  rw [div_mul_cancel₀ _ hlog.ne']
  exact (r3 ψ hψ).2.trans h1

/- English proof (translation)
Take `⟨x₁, hx₁⟩` from `x_large_eventually K cHH eK Cd 0 ε h0`. Take `⟨x₂, hx₂⟩` from `x_large_eventually K cHH eK Cd 0 (ε / 2) (by positivity)`. Establish `e1 : ∀ᶠ x : ℝ in Filter.atTop, (6 : ℝ) ≤ x ^ ((1 : ℝ) / 2)` using `(tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop _`. Establish `e2 : ∀ᶠ x : ℝ in Filter.atTop, (2 : ℝ) ≤ x ^ (ε / 2)` using `(tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _`. Take `⟨x₃, hx₃⟩` from `Filter.eventually_atTop.1 (e1.and e2)`.

Use `⟨max x₁ (max x₂ x₃), fun x hx => ?_⟩` and prove the remaining obligations. Establish `g1 : x₁ ≤ x` using `le_trans (le_max_left _ _) hx`. Establish `g2 : x₂ ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx`. Establish `g3 : x₃ ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx`. Take `⟨a1, a2, a3, -⟩` from `hx₁ x g1`.

Take `⟨-, -, -, b4⟩` from `hx₂ x g2`. Take `⟨d1, d2⟩` from `hx₃ x g3`. Use `⟨a1, a2, a3, ?_⟩` and prove the remaining obligations. Establish `hxpos : 0 < x` using `by linarith`. Establish `hlog : 0 < Real.log x` using `Real.log_pos (by linarith)`.

Unfold `moveCost at b4 ⊢`. Rewrite using `[div_mul_cancel₀ _ hlog.ne']`. Establish `hA : x ^ ((1 : ℝ) / 2 + ε) = x ^ ((1 : ℝ) / 2) * x ^ ε` using `Real.rpow_add hxpos _ _`. Establish `hB : x ^ ((1 : ℝ) / 2 + ε) = x ^ ((1 : ℝ) / 2 + ε / 2) * x ^ (ε / 2)`. Rewrite using `[← Real.rpow_add hxpos]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `p1 : 0 < x ^ ε` using `Real.rpow_pos_of_pos hxpos _`. Establish `p2 : 0 < x ^ ((1 : ℝ) / 2 + ε / 2)` using `Real.rpow_pos_of_pos hxpos _`. Establish `q1 : 6 * x ^ ε ≤ x ^ ((1 : ℝ) / 2 + ε)` using `by rw [hA]; gcongr`.

Establish `q2 : 2 * x ^ ((1 : ℝ) / 2 + ε / 2) ≤ x ^ ((1 : ℝ) / 2 + ε)` using `by rw [hB]; nlinarith`. Simplify using `only [zero_mul, add_zero] at b4`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma xLargeEv_weakL (K cHH eK Cd ε : ℝ) (h0 : 0 < ε) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → XLarge K cHH eK Cd (x ^ ε / Real.log x) ε x := by
  obtain ⟨x₁, hx₁⟩ := x_large_eventually K cHH eK Cd 0 ε h0
  obtain ⟨x₂, hx₂⟩ := x_large_eventually K cHH eK Cd 0 (ε / 2) (by positivity)
  have e1 : ∀ᶠ x : ℝ in Filter.atTop, (6 : ℝ) ≤ x ^ ((1 : ℝ) / 2) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop _
  have e2 : ∀ᶠ x : ℝ in Filter.atTop, (2 : ℝ) ≤ x ^ (ε / 2) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  obtain ⟨x₃, hx₃⟩ := Filter.eventually_atTop.1 (e1.and e2)
  refine ⟨max x₁ (max x₂ x₃), fun x hx => ?_⟩
  have g1 : x₁ ≤ x := le_trans (le_max_left _ _) hx
  have g2 : x₂ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have g3 : x₃ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨a1, a2, a3, -⟩ := hx₁ x g1
  obtain ⟨-, -, -, b4⟩ := hx₂ x g2
  obtain ⟨d1, d2⟩ := hx₃ x g3
  refine ⟨a1, a2, a3, ?_⟩
  have hxpos : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  unfold moveCost at b4 ⊢
  rw [div_mul_cancel₀ _ hlog.ne']
  have hA : x ^ ((1 : ℝ) / 2 + ε) = x ^ ((1 : ℝ) / 2) * x ^ ε := Real.rpow_add hxpos _ _
  have hB : x ^ ((1 : ℝ) / 2 + ε) = x ^ ((1 : ℝ) / 2 + ε / 2) * x ^ (ε / 2) := by
    rw [← Real.rpow_add hxpos]; congr 1; ring
  have p1 : 0 < x ^ ε := Real.rpow_pos_of_pos hxpos _
  have p2 : 0 < x ^ ((1 : ℝ) / 2 + ε / 2) := Real.rpow_pos_of_pos hxpos _
  have q1 : 6 * x ^ ε ≤ x ^ ((1 : ℝ) / 2 + ε) := by rw [hA]; gcongr
  have q2 : 2 * x ^ ((1 : ℝ) / 2 + ε / 2) ≤ x ^ ((1 : ℝ) / 2 + ε) := by rw [hB]; nlinarith
  simp only [zero_mul, add_zero] at b4
  linarith

/- English proof (translation)
Take `⟨Cd, -, hChain⟩` from `chain_weighted_mean_to_unit_weight`. Introduce `eD eL ε₁ hε₁ h`. Use `hChain eD eL ε₁ hε₁ ?_` and prove the remaining obligations. Introduce `ε h0 h1`. Take `⟨K, cHH, eK, x₀, hx₀⟩` from `h ε h0 h1`.

Take `⟨x₁, hx₁⟩` from `xLargeEv_weakL K cHH eK Cd ε h0`. Conclude with `⟨max x₀ x₁, fun x hx => ⟨K, cHH, eK, x ^ ε / Real.log x, hx₀ x (le_trans (le_max_left _ _) hx), hx₁ x (le_trans (le_max_right _ _) hx)⟩⟩`.
-/
theorem chain_eventually_weak_l : ChainWeakLogDerivGivesRiemannHyp := by
  obtain ⟨Cd, -, hChain⟩ := chain_weighted_mean_to_unit_weight
  intro eD eL ε₁ hε₁ h
  refine hChain eD eL ε₁ hε₁ ?_
  intro ε h0 h1
  obtain ⟨K, cHH, eK, x₀, hx₀⟩ := h ε h0 h1
  obtain ⟨x₁, hx₁⟩ := xLargeEv_weakL K cHH eK Cd ε h0
  exact ⟨max x₀ x₁, fun x hx => ⟨K, cHH, eK, x ^ ε / Real.log x, hx₀ x (le_trans (le_max_left _ _) hx),
    hx₁ x (le_trans (le_max_right _ _) hx)⟩⟩

namespace ModelEv

open Model

def SizesAt (K cHH eK ε x : ℝ) : Prop :=
  ∃ (H : Type) (_ : AddCommGroup H) (_ : Fintype H) (_ : DecidableEq H)
    (Top : Type) (_ : Fintype Top) (m f : ℕ)
    (D0 : Data H (fun _ => Unit) Top m f) (C : Consts) (Xpp : ℝ)
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H)) (η X' θ : ℝ),
    D0.x = x ∧ D0.ε = ε ∧ C.eDiv ≤ 1 ∧ C.eLoss ≤ 1 ∧ C.cHH ≤ cHH ∧
    HostFacts D ∧ Ident D0 D N ell TT a w eT eP ∧ ErrWindows D0 C Xpp eK K ∧ BNBounds D0 T2 ∧
    GrowthInequalitySizes TT T2 a w N D0.x D0.b D0.b' η X' θ ∧ 0 < θ ∧ CostWindows D0.x (fPl H) D0.b η θ ∧
    RestSize D0.ε D0.x (Fintype.card H) TT.card T2.card m D0.b D0.k D0.a ∧
    (∀ u0, 0 ≤ ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D0.w u0 j ρ)) ∧
    (∀ u0, ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D0.w u0 j ρ) ≤ C.cCount * (m : ℝ) * D0.L) ∧
    (∀ u0, D0.ASK u0 ≤ D0.Main u0 + C.cDiv * D0.nT * D0.a * D0.La
      + C.cDiv * (m : ℝ) * (D0.B0 + D0.Nc) * D0.x ^ (C.eDiv * D0.ε) + D0.LoP C)

/- English proof (translation)
Take `⟨H, i1, i2, i3, Top, i6, m, f, D0, C, Xpp, D, ell, N, TT, T2, a, w, eT, eP, η, X', θ, hx, hε, heD, heL, hcHH, hHost, hId, hWin, hBN, hSz, hθ, hCost, hSize, hS0, hS1, hTop⟩` from `h`. Substitute `hx hε` using the available equality. Take `⟨⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, wC⟩, wEta⟩` from `hWin`. Establish `wC'` using `wC`. Take `⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17⟩` from `wC'`.

Establish `hx0 : 0 < D0.x` using `by linarith`. Establish `hb0 : 0 < D0.b` using `by linarith`. Establish `ha0 : 0 ≤ D0.a` using `le_trans (by positivity) w5`. Establish `hf : 0 < f` using `Fin.pos (eP.symm ⟨0, by simp [PhiSet, InPhi]⟩)`. Establish `hw : ∀ u0 j ρ, 0 < D0.w u0 j ρ`.

Introduce `u0 j ρ`. Rewrite using `[hId.2.1 u0 j ρ]`. Conclude with `hSz.2.2.2.2.2.2.1.1 u0 j _ (Finset.mem_filter.1 (eP ρ).2).2`. Take `⟨D1, ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15⟩, z1, z2, z3, hLed⟩` from `exists_data_completion D0 C Xpp hx0 hb0 ha0 w17 w10 w15 w22 w19 hf (fun t => (w21 t).1) hw ⟨c3, c5, c7, c9, c11, c13⟩ hS0 hS1 hTop`. Establish `hnT : D1.nT = D0.nT` using `rfl`.

Use `⟨H, i1, i2, i3, fun _ => Unit, inferInstance, inferInstance, Top, i6, m, f, D1, C, Xpp, D, ell, N, TT, T2, a, w, eT, eP, η, X', θ, s1, s2, heD, heL, hcHH, hHost, ?_, hLed, ?_, ?_, ?_, hθ, ?_, ?_⟩` and prove the remaining obligations. Take `⟨j1, j2, j3, j4, j5⟩` from `hId`. Conclude with `⟨by rw [s13]; exact j1, by rw [s14]; exact j2, by rw [s11]; exact j3, by rw [s12]; exact j4, by rw [s15]; exact j5⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `ErrWindows0`.

Rewrite using `[s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s13, z1, z2, z3, hnT]`. Conclude with `⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, by norm_num, le_refl _, le_refl _, wC⟩`. Rewrite using `[s1, s2, s3, s4, z2, z3, hnT]`. Establish `h1 : 0 ≤ K * D0.x ^ D0.ε * (D0.nT * D0.a)`. Establish `hK : 0 ≤ K` using `le_trans c1 c2`.

Establish `: 0 ≤ D0.nT` using `by linarith`. Check the signs of the components of the expression. Simplify using `using h1`. Unfold `BNBounds`. Rewrite using `[s1, s2, s4, s6, s9, s10]`.

Conclude with `hBN`. Rewrite using `[s4, s5]`. Conclude with `hSz`. Rewrite using `[s4]`. Conclude with `hCost`.

Rewrite using `[s3, s4, s6]`. Conclude with `hSize`.
-/
theorem coreOfSizes {K cHH eK ε x : ℝ} (h : SizesAt K cHH eK ε x) : ChainCoreNoAnalytic 1 1 K cHH eK ε x := by
  obtain ⟨H, i1, i2, i3, Top, i6, m, f, D0, C, Xpp, D, ell, N, TT, T2, a, w, eT, eP, η, X', θ, hx, hε, heD, heL, hcHH,
    hHost, hId, hWin, hBN, hSz, hθ, hCost, hSize, hS0, hS1, hTop⟩ := h
  subst hx hε
  obtain ⟨⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22,
    w23, w24, w25, w26, w27, wC⟩, wEta⟩ := hWin
  have wC' := wC
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17⟩ := wC'
  have hx0 : 0 < D0.x := by linarith
  have hb0 : 0 < D0.b := by linarith
  have ha0 : 0 ≤ D0.a := le_trans (by positivity) w5
  have hf : 0 < f := Fin.pos (eP.symm ⟨0, by simp [PhiSet, InPhi]⟩)
  have hw : ∀ u0 j ρ, 0 < D0.w u0 j ρ := by
    intro u0 j ρ
    rw [hId.2.1 u0 j ρ]
    exact hSz.2.2.2.2.2.2.1.1 u0 j _ (Finset.mem_filter.1 (eP ρ).2).2
  obtain ⟨D1, ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15⟩, z1, z2, z3, hLed⟩ :=
    exists_data_completion D0 C Xpp hx0 hb0 ha0 w17 w10 w15 w22 w19 hf (fun t => (w21 t).1) hw
      ⟨c3, c5, c7, c9, c11, c13⟩ hS0 hS1 hTop
  have hnT : D1.nT = D0.nT := rfl
  refine ⟨H, i1, i2, i3, fun _ => Unit, inferInstance, inferInstance, Top, i6, m, f, D1, C, Xpp, D, ell, N,
    TT, T2, a, w, eT, eP, η, X', θ, s1, s2, heD, heL, hcHH, hHost, ?_, hLed, ?_, ?_, ?_, hθ, ?_, ?_⟩
  · obtain ⟨j1, j2, j3, j4, j5⟩ := hId
    exact ⟨by rw [s13]; exact j1, by rw [s14]; exact j2, by rw [s11]; exact j3, by rw [s12]; exact j4,
      by rw [s15]; exact j5⟩
  · refine ⟨?_, ?_⟩
    · unfold ErrWindows0
      rw [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s13, z1, z2, z3, hnT]
      exact ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22,
        w23, w24, by norm_num, le_refl _, le_refl _, wC⟩
    · rw [s1, s2, s3, s4, z2, z3, hnT]
      have h1 : 0 ≤ K * D0.x ^ D0.ε * (D0.nT * D0.a) := by
        have hK : 0 ≤ K := le_trans c1 c2
        have : 0 ≤ D0.nT := by linarith
        positivity
      simpa using h1
  · unfold BNBounds
    rw [s1, s2, s4, s6, s9, s10]
    exact hBN
  · rw [s4, s5]; exact hSz
  · rw [s4]; exact hCost
  · rw [s3, s4, s6]; exact hSize

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

def wE (m : ℕ) (b : ℝ) : H → Fin m → E0 × H → ℝ := fun u0 _ ρ => if IsThickAt univ u0 ρ then b else 1

def DE (x ε b : ℝ) (m N : ℕ) : Data H (fun _ => Unit) (univ : Finset H) m (fM H) where
  x := x
  ε := ε
  a := x * b
  b := b
  b' := 1
  k := x * m
  L := Real.log b
  La := Real.log b
  B0 := (2 * (Fintype.card H : ℝ)) * m * b * x ^ ε
  Nc := ((univ : Finset H).card : ℝ) * (x * m) * b * x ^ ε
    / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * x ^ (-ε)))
  gam := Real.eulerMascheroniConstant
  LpL := 0
  v := 1
  lg := 0
  logGam := 0
  aT := fun _ => x * b
  w := fun u0 j ρ => wE m b u0 j (ePM ρ)
  d := fun _ _ => 1
  T := fun _ _ => 1
  muN := fun _ _ => 0
  muMaxN := fun _ _ => 0
  h := fun _ _ => 0
  muM := fun _ _ => 0
  muMaxM := fun _ _ => 0
  EeJ := fun _ _ _ => 0
  muCC := fun _ => 0
  muMinCC := fun _ => 0
  Fo := fun _ => 0
  Ga := fun _ => 0
  Ta := fun _ => 0
  ASK := fun u0 => ∑ t ∈ (univ : Finset H), ∑ j : Fin m, ASK DA N (x * b) t (wE m b u0 j)
  IO := fun _ => 0
  HH := fun _ => 1
  del := fun _ => 0
  η := fun _ => 0
  e := fun _ => 0
  delBar := 0
  etaBar := 0
  eBar := 0

/- English proof (translation)
Unfold `wE`. Use `split_ifs`. Conclude with `Or.inl rfl`. Conclude with `Or.inr rfl`.
-/
lemma wE_cases (m : ℕ) (b : ℝ) (u0 : H) (j : Fin m) (ρ : E0 × H) : wE m b u0 j ρ = b ∨ wE m b u0 j ρ = 1 := by
  unfold wE; split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => simp`. Consider the case `succ N ih`. Rewrite using `[Finset.sum_Icc_succ_top (by omega)]`. Rewrite using `[← ih]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma geo7 (a : ℝ) (N : ℕ) : ∑ i ∈ Icc 1 N, a / (7 : ℝ) ^ i + a / (6 * 7 ^ N) = a / 6 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    rw [← ih]
    field_simp
    ring

/- English proof (translation)
Establish `hd : (((DA (H` using `H)).d : ℕ) : ℝ) = 7 := by show (((7 : ℕ) : ℕ) : ℝ) = 7`. Evaluate the numerical expressions. Establish `h2 : askD (DA (H` using `H)) N a t w ≤ a / 6 := by`. Unfold `askD`. Rewrite using `[hd]`.

Use `le_trans (Finset.sum_le_sum (g := fun i => a / (7 : ℝ) ^ i) fun i _ => ?_) ?_` and prove the remaining obligations. Use `le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := {(sgc0 : E0 × H)}) ?_ (fun _ _ _ => le_max_right _ _)) ?_` and prove the remaining obligations. Introduce `g hg`. Take `⟨-, hg1, hg2⟩` from `Finset.mem_filter.1 hg`. Establish `e : g - i • (DA (H` using `H)).frob (DA (H := H)).d = g := by show g - i • (0 : E0 × H) = g`.

Simplify using the standard rewrite rules. Rewrite `hg1` using `[e]`. Break down `(hostFacts_DA.inertia_d g).1 hg1 with h | h` into its components or cases. Conclude with `absurd (by rw [h]; simp [InPhi]) hg2`. Conclude with `Finset.mem_singleton.2 h`.

Rewrite using `[Finset.sum_singleton]`. Conclude with `max_le (by linarith [hw (partner t sgc0)]) (by positivity)`. Use `geo7 a N` as an intermediate fact. Establish `h4 : 0 ≤ a / (6 * 7 ^ N)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h0 : 0 ≤ askD (DA (H` using `H)) N a t w := by`. Unfold `askD`. Conclude with `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _`. Unfold `ASK`. Rewrite using `[Finset.sum_eq_zero, hd, zero_add]`.

Establish `hl : Real.log 7 ≤ 7 - 1` using `Real.log_le_sub_one_of_pos (by norm_num)`. Establish `hl0 : 0 ≤ Real.log 7` using `Real.log_nonneg (by norm_num)`. Use the polynomial consequences of the given equalities and inequalities. Introduce `p hp`. Take `⟨-, hp2⟩` from `Finset.mem_filter.1 hp`.

Conclude with `absurd (by show InPhi (0 : E0 × H); simp [InPhi]) hp2.2.2.2.2`.
-/
lemma askDA_le (N : ℕ) (a : ℝ) (t : H) (w : E0 × H → ℝ) (ha : 0 ≤ a) (hw : ∀ ρ, 0 ≤ w ρ) :
    ASK (DA (H := H)) N a t w ≤ a := by
  classical
  have hd : (((DA (H := H)).d : ℕ) : ℝ) = 7 := by
    show (((7 : ℕ) : ℕ) : ℝ) = 7
    norm_num
  have h2 : askD (DA (H := H)) N a t w ≤ a / 6 := by
    unfold askD
    rw [hd]
    refine le_trans (Finset.sum_le_sum (g := fun i => a / (7 : ℝ) ^ i) fun i _ => ?_) ?_
    · refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := {(sgc0 : E0 × H)}) ?_
        (fun _ _ _ => le_max_right _ _)) ?_
      · intro g hg
        obtain ⟨-, hg1, hg2⟩ := Finset.mem_filter.1 hg
        have e : g - i • (DA (H := H)).frob (DA (H := H)).d = g := by
          show g - i • (0 : E0 × H) = g
          simp
        rw [e] at hg1
        rcases (hostFacts_DA.inertia_d g).1 hg1 with h | h
        · exact absurd (by rw [h]; simp [InPhi]) hg2
        · exact Finset.mem_singleton.2 h
      · rw [Finset.sum_singleton]
        exact max_le (by linarith [hw (partner t sgc0)]) (by positivity)
    · have := geo7 a N
      have h4 : 0 ≤ a / (6 * 7 ^ N) := by positivity
      linarith
  have h0 : 0 ≤ askD (DA (H := H)) N a t w := by
    unfold askD
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _
  unfold ASK
  rw [Finset.sum_eq_zero, hd, zero_add]
  · have hl : Real.log 7 ≤ 7 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have hl0 : 0 ≤ Real.log 7 := Real.log_nonneg (by norm_num)
    nlinarith
  · intro p hp
    obtain ⟨-, hp2⟩ := Finset.mem_filter.1 hp
    exact absurd (by show InPhi (0 : E0 × H); simp [InPhi]) hp2.2.2.2.2

set_option maxHeartbeats 1600000 in
/- English proof (translation)
Establish `hx0 : 0 < x` using `by linarith`. Establish `hx1 : 1 ≤ x` using `by linarith`. Establish `hn0 : (0 : ℝ) < n` using `by linarith`. Establish `hn1 : (1 : ℝ) ≤ n` using `by linarith`. Establish `hbx : x ≤ b`.

Rewrite using `[hb]`. Establish `: 1 ≤ 12 * (n : ℝ) * (x + 1)` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `hb1 : 1 ≤ b` using `by linarith`. Establish `hb0 : 0 < b` using `by linarith`.

Establish `hm0 : (0 : ℝ) < m` using `lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hm1`. Establish `hm1' : (1 : ℝ) ≤ m`. Establish `: 0 < m` using `by exact_mod_cast hm0`. Conclude with `this` after adjusting the coercions. Establish `hlb : 0 ≤ Real.log b` using `Real.log_nonneg hb1`.

Establish `hxe : 0 < x ^ ε` using `Real.rpow_pos_of_pos hx0 _`. Establish `hxe' : 0 < x ^ (-ε)` using `Real.rpow_pos_of_pos hx0 _`. Establish `hnT : (DE (H` using `H) x ε b m N).nT = n := by`. Unfold `Data.nT`. Rewrite using `[Fintype.card_coe, Finset.card_univ, hcard]`.

Establish `hcu : (univ : Finset H).card = n` using `by rw [Finset.card_univ, hcard]`. Establish `hf : fPl H = 2 * (n : ℝ)` using `by rw [fPl_eq, hcard]`. Establish `hlogw : ∀ (u0 : H) (j : Fin m) (ρ : E0 × H), 0 ≤ Real.log (wE m b u0 j ρ) ∧ Real.log (wE m b u0 j ρ) ≤ Real.log b`. Introduce `u0 j ρ`. Apply the tactic sequence `rcases wE_cases m b u0 j ρ with h | h <;> rw [h]`.

Conclude with `⟨hlb, le_refl _⟩`. Simplify using `using hlb`. Use `⟨H, inferInstance, inferInstance, inferInstance, (univ : Finset H), inferInstance, m, fM H, DE x ε b m N, CM, 0, DA, fun _ => 0, N, univ, univ, fun _ => x * b, wE m b, Equiv.refl _, ePM, 0, x * b, 1 / (2 * fPl H * (x + 1) * x), rfl, rfl, le_refl _, le_refl _, le_refl _, hostFacts …` and prove the remaining obligations. Use `⟨hx1, hε0, hε1, hb1, le_refl _, by rw [hnT]; exact hn1, hm2, le_refl _, by norm_num, ?_, ?_, ?_, hlb, hL, hlb, hL, zero_le_one, ?_, le_refl _, ?_, fun _ => ⟨?_, ?_⟩, ?_, ?_, fun _ => ?_, by norm_num [DE], le_refl _, le_refl _, ?_⟩` and prove the remaining obligations. Use `show 1 ≤ x * m`.

Use the polynomial consequences of the given equalities and inequalities. Use `show x * m ≤ x ^ (2 : ℝ)`. Rewrite using `[Real.rpow_two]`. Use the polynomial consequences of the given equalities and inequalities. Use `show x * m ≤ x * b`.

Use the polynomial consequences of the given equalities and inequalities. Use `show x * m * 1 ≤ x * b`. Use the polynomial consequences of the given equalities and inequalities. Use `show 0 ≤ x * b`. Check the signs of the components of the expression.

Use `show 0 ≤ x * b`. Check the signs of the components of the expression. Use `show x * b ≤ 2 * (x * b)`. Use polynomial arithmetic with `[mul_pos hx0 hb0]`. Use `show 0 ≤ (2 * (Fintype.card H : ℝ)) * m * b * x ^ ε`.

Check the signs of the components of the expression. Use `show 0 ≤ ((univ : Finset H).card : ℝ) * (x * m) * b * x ^ ε / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * x ^ (-ε)))`. Check the signs of the components of the expression. Establish `hl2 : 0 ≤ Real.log 2` using `Real.log_nonneg (by norm_num)`. Simplify using `only [Fintype.card_unit, Nat.cast_one, Real.log_one]`.

Use `mul_nonneg ?_ hl2` and prove the remaining obligations. Use `show 0 ≤ x * m - 3`. Use the polynomial consequences of the given equalities and inequalities. Apply the tactic sequence `refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [CM]`. Rewrite using `[hnT]`.

Use `show ((0 : ℝ) + 4 * Real.sqrt 0) * (x ^ CM.cHH * b) ≤ 1 * x ^ ε * ((n : ℝ) * (x * b))`. Rewrite using `[Real.sqrt_zero]`. Establish `: 0 ≤ 1 * x ^ ε * ((n : ℝ) * (x * b))` using `by positivity`. Simplify using `using this`. Use `⟨le_refl _, by positivity, zero_lt_one, ?_, by rw [hf]; positivity, fun t _ => ?_, ⟨fun u0 j ρ _ => ?_, fun u0 j ρ h => ?_, fun u0 j ρ _ h => ?_⟩, fun u0 j t ρ _ _ => ?_⟩` and prove the remaining obligations.

Use `show (1 : ℝ) * (x * b) ≤ x * b`. Combine the linear equalities and inequalities to obtain the conclusion. Use `show |x * b / b - x| ≤ 1`. Rewrite using `[mul_div_assoc, div_self hb0.ne']`. Simplify using the standard rewrite rules.

Apply the tactic sequence `rcases wE_cases m b u0 j ρ with h | h <;> rw [h] <;> positivity`. Establish `: wE m b u0 j ρ = b` using `by unfold wE; rw [if_pos h]`. Rewrite using `[this]`. Conclude with `⟨le_refl _, by show b ≤ b + 0 + 1; linarith⟩`. Establish `: wE m b u0 j ρ = 1` using `by unfold wE; rw [if_neg h]`.

Rewrite using `[this]`. Use `show (1 : ℝ) ≤ 2 * 1`. Evaluate the numerical expressions. Apply the tactic sequence `rcases wE_cases m b u0 j ρ with h | h <;> rw [h]`. Rewrite using `[mul_div_assoc, div_self hb0.ne']`.

Use the polynomial consequences of the given equalities and inequalities. Simplify using `using hN`. Rewrite using `[hf]`. Check the signs of the components of the expression. Use `show 2 * fPl H * (x + 1) * (1 / (2 * fPl H * (x + 1) * x)) ≤ 1 / x`.

Rewrite using `[hf]`. Apply `le_of_eq` to reduce the goal to its premises. Clear the denominators using the available nonvanishing facts. Use `show 6 * fPl H * (x + 1) * (0 + 1) ≤ b / x`. Rewrite using `[hf, hb]`.

Apply `le_of_eq` to reduce the goal to its premises. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `show x * b ≤ 2 * x * b`. Use polynomial arithmetic with `[mul_pos hx0 hb0]`.

Establish `: x ^ (-(ε / 8)) ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)`. Rewrite using `[hcu, hcard]`. Use `show x ^ (-(ε / 8)) * (n : ℝ) / 2 ≤ (n : ℝ)`. Use the polynomial consequences of the given equalities and inequalities. Establish `: x ^ (-ε) ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)`.

Rewrite using `[hcu, hcard]`. Use `show x ^ (-ε) ≤ (n : ℝ) / (n : ℝ)`. Rewrite using `[div_self hn0.ne']`. Conclude with `this`. Conclude with `hm1`.

Rewrite using `[hcard]`. Conclude with `hk`. Introduce `u0`. Use `Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (Finset.sum_nonneg fun ρ _ => ?_)` and prove the remaining obligations. Conclude with `(hlogw u0 j (ePM ρ)).1`.

Introduce `u0`. Establish `hfp : (0 : ℝ) < (fM H : ℝ)` using `by exact_mod_cast fM_pos`. Establish `h1 : ∀ j : Fin m, (1 / (fM H : ℝ)) * ∑ ρ : Fin (fM H), Real.log ((DE (H` using `H) x ε b m N).w u0 j ρ) ≤ Real.log b := by`. Introduce `j`. Establish `h2 : ∑ ρ : Fin (fM H), Real.log ((DE (H` using `H) x ε b m N).w u0 j ρ) ≤ ∑ _ρ : Fin (fM H), Real.log b := Finset.sum_le_sum fun ρ _ => (hlogw u0 j (ePM ρ)).2`.

Rewrite `h2` using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `h3` using `Finset.sum_le_sum (s := (univ : Finset (Fin m))) fun j _ => h1 j`. Rewrite `h3` using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Use `show _ ≤ CM.cCount * (m : ℝ) * Real.log b`.

Simplify `h3` using `[CM]`. Introduce `u0`. Establish `hfp : (0 : ℝ) < (fM H : ℝ)` using `by exact_mod_cast fM_pos`. Establish `h1 : ∀ j : Fin m, (1 / (fM H : ℝ)) * ∑ ρ : Fin (fM H), Real.log ((DE (H` using `H) x ε b m N).w u0 j ρ) ≤ Real.log b := by`. Introduce `j`.

Establish `h2 : ∑ ρ : Fin (fM H), Real.log ((DE (H` using `H) x ε b m N).w u0 j ρ) ≤ ∑ _ρ : Fin (fM H), Real.log b := Finset.sum_le_sum fun ρ _ => (hlogw u0 j (ePM ρ)).2`. Rewrite `h2` using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hxb : 0 < x * b` using `by positivity`. Establish `hA : (DE (H` using `H) x ε b m N).ASK u0 ≤ ∑ _t ∈ (univ : Finset H), ∑ _j : Fin m, x * b := by`.

Use `Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun j _ => askDA_le N (x * b) t _ hxb.le fun ρ => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases wE_cases m b u0 j ρ with h | h <;> rw [h] <;> positivity`. Establish `hM : ∑ _j : Fin m, ∑ _t : (univ : Finset H), x * b ≤ (DE (H` using `H) x ε b m N).Main u0 := by`. Unfold `Data.Main`. Use `Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun t _ => ?_` and prove the remaining obligations.

Use `show x * b ≤ x * b * (Real.log (x * b) - 1 - Real.eulerMascheroniConstant + 0 - (1 / (fM H : ℝ)) * ∑ ρ : Fin (fM H), Real.log ((DE (H := H) x ε b m N).w u0 j ρ))`. Establish `hg` using `Real.eulerMascheroniConstant_lt_two_thirds`. Establish `hlm : Real.log (x * b) = Real.log x + Real.log b` using `Real.log_mul hx0.ne' hb0.ne'`. Use `h1 j` as an intermediate fact. Establish `h5 : 1 ≤ Real.log (x * b) - 1 - Real.eulerMascheroniConstant + 0 - (1 / (fM H : ℝ)) * ∑ ρ : Fin (fM H), Real.log ((DE (H` using `H) x ε b m N).w u0 j ρ) := by linarith`.

Combine the equalities or inequalities in the displayed calculation. Establish `hE : ∑ _t ∈ (univ : Finset H), ∑ _j : Fin m, x * b = ∑ _j : Fin m, ∑ _t : (univ : Finset H), x * b`. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_coe, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `e1 : 0 ≤ CM.cDiv * (DE (H` using `H) x ε b m N).nT * (DE (H := H) x ε b m N).a * (DE (H := H) x ε b m N).La := by`.

Rewrite using `[hnT]`. Establish `q1 : CM.cDiv = 1` using `rfl`. Establish `q2 : (DE (H` using `H) x ε b m N).a = x * b := rfl`. Establish `q3 : (DE (H` using `H) x ε b m N).La = Real.log b := rfl`. Rewrite using `[q1, q2, q3]`.

Conclude with `mul_nonneg (by positivity) hlb`. Establish `e2 : 0 ≤ CM.cDiv * (m : ℝ) * ((DE (H` using `H) x ε b m N).B0 + (DE (H := H) x ε b m N).Nc) * (DE (H := H) x ε b m N).x ^ (CM.eDiv * (DE (H := H) x ε b m N).ε) := by`. Establish `q1 : CM.cDiv = 1` using `rfl`. Establish `q2 : (DE (H` using `H) x ε b m N).B0 = (2 * (Fintype.card H : ℝ)) * m * b * x ^ ε := rfl`. Establish `q3 : (DE (H` using `H) x ε b m N).Nc = ((univ : Finset H).card : ℝ) * (x * m) * b * x ^ ε / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * x ^ (-ε))) := rfl`.

Establish `q4 : (DE (H` using `H) x ε b m N).x = x := rfl`. Rewrite using `[q1, q2, q3, q4]`. Check the signs of the components of the expression. Establish `e3 : 0 ≤ (DE (H` using `H) x ε b m N).LoP CM := by`. Unfold `Data.LoP`.

Rewrite using `[hnT]`. Establish `q1 : CM.cLoss = 1` using `rfl`. Establish `q2 : (DE (H` using `H) x ε b m N).b = b := rfl`. Establish `q4 : (DE (H` using `H) x ε b m N).x = x := rfl`. Rewrite using `[q1, q2, q4]`.

Check the signs of the components of the expression. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma sizesOf (x ε b : ℝ) (m N n : ℕ) (hcard : Fintype.card H = n)
    (hx : 3 ≤ x) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : x ≤ n) (hb : b = 12 * n * (x + 1) * x)
    (hm1 : x ^ ((1 : ℝ) / 2 - ε) ≤ m) (hm2 : (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2)) (hmx : (m : ℝ) ≤ x)
    (hk : x * m ≤ (n : ℝ) ^ 2 * x ^ ((1 : ℝ) / 2 - ε)) (hL : Real.log b ≤ 2 * x ^ ε) (hN : x * b ≤ N)
    (hl3 : 3 ≤ Real.log x) :
    SizesAt 1 1 2 ε x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hbx : x ≤ b := by
    rw [hb]
    have : 1 ≤ 12 * (n : ℝ) * (x + 1) := by nlinarith
    nlinarith
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hm1
  have hm1' : (1 : ℝ) ≤ m := by
    have : 0 < m := by exact_mod_cast hm0
    exact_mod_cast this
  have hlb : 0 ≤ Real.log b := Real.log_nonneg hb1
  have hxe : 0 < x ^ ε := Real.rpow_pos_of_pos hx0 _
  have hxe' : 0 < x ^ (-ε) := Real.rpow_pos_of_pos hx0 _
  have hnT : (DE (H := H) x ε b m N).nT = n := by
    unfold Data.nT
    rw [Fintype.card_coe, Finset.card_univ, hcard]
  have hcu : (univ : Finset H).card = n := by rw [Finset.card_univ, hcard]
  have hf : fPl H = 2 * (n : ℝ) := by rw [fPl_eq, hcard]
  have hlogw : ∀ (u0 : H) (j : Fin m) (ρ : E0 × H), 0 ≤ Real.log (wE m b u0 j ρ) ∧ Real.log (wE m b u0 j ρ) ≤ Real.log b := by
    intro u0 j ρ
    rcases wE_cases m b u0 j ρ with h | h <;> rw [h]
    · exact ⟨hlb, le_refl _⟩
    · simpa using hlb
  refine ⟨H, inferInstance, inferInstance, inferInstance, (univ : Finset H), inferInstance, m, fM H,
    DE x ε b m N, CM, 0, DA, fun _ => 0, N, univ, univ, fun _ => x * b, wE m b, Equiv.refl _, ePM,
    0, x * b, 1 / (2 * fPl H * (x + 1) * x), rfl, rfl, le_refl _, le_refl _, le_refl _, hostFacts_DA,
    ⟨fun _ => rfl, fun _ _ _ => rfl, rfl, by simp [DE], fun _ => rfl⟩, ⟨?_, ?_⟩, ⟨le_refl _, le_refl _⟩, ?_, ?_, ⟨?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  ·
    refine ⟨hx1, hε0, hε1, hb1, le_refl _, by rw [hnT]; exact hn1, hm2, le_refl _, by norm_num, ?_, ?_, ?_, hlb, hL, hlb, hL,
      zero_le_one, ?_, le_refl _, ?_, fun _ => ⟨?_, ?_⟩, ?_, ?_, fun _ => ?_, by norm_num [DE], le_refl _, le_refl _, ?_⟩
    · show 1 ≤ x * m
      nlinarith
    · show x * m ≤ x ^ (2 : ℝ)
      rw [Real.rpow_two]
      nlinarith
    · show x * m ≤ x * b
      nlinarith
    · show x * m * 1 ≤ x * b
      nlinarith
    · show 0 ≤ x * b
      positivity
    · show 0 ≤ x * b
      positivity
    · show x * b ≤ 2 * (x * b)
      nlinarith [mul_pos hx0 hb0]
    · show 0 ≤ (2 * (Fintype.card H : ℝ)) * m * b * x ^ ε
      positivity
    · show 0 ≤ ((univ : Finset H).card : ℝ) * (x * m) * b * x ^ ε
        / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * x ^ (-ε)))
      positivity
    · have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      simp only [Fintype.card_unit, Nat.cast_one, Real.log_one]
      refine mul_nonneg ?_ hl2
      show 0 ≤ x * m - 3
      nlinarith
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [CM]
  ·
    rw [hnT]
    show ((0 : ℝ) + 4 * Real.sqrt 0) * (x ^ CM.cHH * b) ≤ 1 * x ^ ε * ((n : ℝ) * (x * b))
    rw [Real.sqrt_zero]
    have : 0 ≤ 1 * x ^ ε * ((n : ℝ) * (x * b)) := by positivity
    simpa using this
  ·
    refine ⟨le_refl _, by positivity, zero_lt_one, ?_, by rw [hf]; positivity, fun t _ => ?_,
      ⟨fun u0 j ρ _ => ?_, fun u0 j ρ h => ?_, fun u0 j ρ _ h => ?_⟩, fun u0 j t ρ _ _ => ?_⟩
    · show (1 : ℝ) * (x * b) ≤ x * b
      linarith
    · show |x * b / b - x| ≤ 1
      rw [mul_div_assoc, div_self hb0.ne']
      simp
    · rcases wE_cases m b u0 j ρ with h | h <;> rw [h] <;> positivity
    · have : wE m b u0 j ρ = b := by unfold wE; rw [if_pos h]
      rw [this]
      exact ⟨le_refl _, by show b ≤ b + 0 + 1; linarith⟩
    · have : wE m b u0 j ρ = 1 := by unfold wE; rw [if_neg h]
      rw [this]
      show (1 : ℝ) ≤ 2 * 1
      norm_num
    · rcases wE_cases m b u0 j ρ with h | h <;> rw [h]
      · rw [mul_div_assoc, div_self hb0.ne']
        nlinarith
      · simpa using hN
  · rw [hf]; positivity
  ·
    show 2 * fPl H * (x + 1) * (1 / (2 * fPl H * (x + 1) * x)) ≤ 1 / x
    rw [hf]
    apply le_of_eq
    field_simp
  ·
    show 6 * fPl H * (x + 1) * (0 + 1) ≤ b / x
    rw [hf, hb]
    apply le_of_eq
    field_simp
    ring
  · show x * b ≤ 2 * x * b
    nlinarith [mul_pos hx0 hb0]
  · have : x ^ (-(ε / 8)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    rw [hcu, hcard]
    show x ^ (-(ε / 8)) * (n : ℝ) / 2 ≤ (n : ℝ)
    nlinarith
  · have : x ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    rw [hcu, hcard]
    show x ^ (-ε) ≤ (n : ℝ) / (n : ℝ)
    rw [div_self hn0.ne']
    exact this
  · exact hm1
  · rw [hcard]
    exact hk
  · intro u0
    refine Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (Finset.sum_nonneg fun ρ _ => ?_)
    exact (hlogw u0 j (ePM ρ)).1
  · intro u0
    have hfp : (0 : ℝ) < (fM H : ℝ) := by exact_mod_cast fM_pos
    have h1 : ∀ j : Fin m, (1 / (fM H : ℝ)) * ∑ ρ : Fin (fM H), Real.log ((DE (H := H) x ε b m N).w u0 j ρ) ≤ Real.log b := by
      intro j
      have h2 : ∑ ρ : Fin (fM H), Real.log ((DE (H := H) x ε b m N).w u0 j ρ) ≤ ∑ _ρ : Fin (fM H), Real.log b :=
        Finset.sum_le_sum fun ρ _ => (hlogw u0 j (ePM ρ)).2
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
      calc (1 / (fM H : ℝ)) * ∑ ρ : Fin (fM H), Real.log ((DE (H := H) x ε b m N).w u0 j ρ)
            ≤ (1 / (fM H : ℝ)) * ((fM H : ℝ) * Real.log b) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = Real.log b := by field_simp
    have h3 := Finset.sum_le_sum (s := (univ : Finset (Fin m))) fun j _ => h1 j
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
    show _ ≤ CM.cCount * (m : ℝ) * Real.log b
    simpa [CM] using h3
  ·
    intro u0
    have hfp : (0 : ℝ) < (fM H : ℝ) := by exact_mod_cast fM_pos
    have h1 : ∀ j : Fin m, (1 / (fM H : ℝ)) * ∑ ρ : Fin (fM H), Real.log ((DE (H := H) x ε b m N).w u0 j ρ) ≤ Real.log b := by
      intro j
      have h2 : ∑ ρ : Fin (fM H), Real.log ((DE (H := H) x ε b m N).w u0 j ρ) ≤ ∑ _ρ : Fin (fM H), Real.log b :=
        Finset.sum_le_sum fun ρ _ => (hlogw u0 j (ePM ρ)).2
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
      calc (1 / (fM H : ℝ)) * ∑ ρ : Fin (fM H), Real.log ((DE (H := H) x ε b m N).w u0 j ρ)
            ≤ (1 / (fM H : ℝ)) * ((fM H : ℝ) * Real.log b) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = Real.log b := by field_simp
    have hxb : 0 < x * b := by positivity
    have hA : (DE (H := H) x ε b m N).ASK u0 ≤ ∑ _t ∈ (univ : Finset H), ∑ _j : Fin m, x * b := by
      refine Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun j _ => askDA_le N (x * b) t _ hxb.le fun ρ => ?_
      rcases wE_cases m b u0 j ρ with h | h <;> rw [h] <;> positivity
    have hM : ∑ _j : Fin m, ∑ _t : (univ : Finset H), x * b ≤ (DE (H := H) x ε b m N).Main u0 := by
      unfold Data.Main
      refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun t _ => ?_
      show x * b ≤ x * b * (Real.log (x * b) - 1 - Real.eulerMascheroniConstant + 0
        - (1 / (fM H : ℝ)) * ∑ ρ : Fin (fM H), Real.log ((DE (H := H) x ε b m N).w u0 j ρ))
      have hg := Real.eulerMascheroniConstant_lt_two_thirds
      have hlm : Real.log (x * b) = Real.log x + Real.log b := Real.log_mul hx0.ne' hb0.ne'
      have := h1 j
      have h5 : 1 ≤ Real.log (x * b) - 1 - Real.eulerMascheroniConstant + 0
        - (1 / (fM H : ℝ)) * ∑ ρ : Fin (fM H), Real.log ((DE (H := H) x ε b m N).w u0 j ρ) := by linarith
      calc x * b = x * b * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left h5 hxb.le
    have hE : ∑ _t ∈ (univ : Finset H), ∑ _j : Fin m, x * b = ∑ _j : Fin m, ∑ _t : (univ : Finset H), x * b := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_coe, nsmul_eq_mul]
      ring
    have e1 : 0 ≤ CM.cDiv * (DE (H := H) x ε b m N).nT * (DE (H := H) x ε b m N).a * (DE (H := H) x ε b m N).La := by
      rw [hnT]
      have q1 : CM.cDiv = 1 := rfl
      have q2 : (DE (H := H) x ε b m N).a = x * b := rfl
      have q3 : (DE (H := H) x ε b m N).La = Real.log b := rfl
      rw [q1, q2, q3]
      exact mul_nonneg (by positivity) hlb
    have e2 : 0 ≤ CM.cDiv * (m : ℝ) * ((DE (H := H) x ε b m N).B0 + (DE (H := H) x ε b m N).Nc)
        * (DE (H := H) x ε b m N).x ^ (CM.eDiv * (DE (H := H) x ε b m N).ε) := by
      have q1 : CM.cDiv = 1 := rfl
      have q2 : (DE (H := H) x ε b m N).B0 = (2 * (Fintype.card H : ℝ)) * m * b * x ^ ε := rfl
      have q3 : (DE (H := H) x ε b m N).Nc = ((univ : Finset H).card : ℝ) * (x * m) * b * x ^ ε
          / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * x ^ (-ε))) := rfl
      have q4 : (DE (H := H) x ε b m N).x = x := rfl
      rw [q1, q2, q3, q4]
      positivity
    have e3 : 0 ≤ (DE (H := H) x ε b m N).LoP CM := by
      unfold Data.LoP
      rw [hnT]
      have q1 : CM.cLoss = 1 := rfl
      have q2 : (DE (H := H) x ε b m N).b = b := rfl
      have q4 : (DE (H := H) x ε b m N).x = x := rfl
      rw [q1, q2, q4]
      positivity
    linarith

end

/- English proof (translation)
Introduce `ε hε0 hε2`. Take `⟨x₁, hx₁⟩` from `x_large_eventually 1 1 2 0 0 ε hε0`. Take `⟨x₂, hx₂⟩` from `Formalism.LFunctionChainParameters.LErr.large_x_eventually (ε / 2) 0 0 0 (by positivity)`. Use `⟨max (max x₁ x₂) 48, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hXL` using `hx₁ x (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx)`.

Take `⟨hlog, hbig⟩` from `hx₂ x (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx)`. Establish `hx48 : 48 ≤ x` using `le_trans (le_max_right _ _) hx`. Use `⟨?_, hXL⟩` and prove the remaining obligations. Establish `hx0 : 0 < x` using `by linarith`. Establish `hx1 : 1 ≤ x` using `by linarith`.

Take `⟨-, h26, -, -⟩` from `hXL`. Use `set n : ℕ := ⌈x⌉₊ with hn`. Use `set u : ℝ := x ^ ((1 : ℝ) / 2 - ε) with hu`. Use `set m : ℕ := ⌈u⌉₊ with hm`. Establish `hnx : x ≤ n` using `Nat.le_ceil x`.

Establish `hnx1 : (n : ℝ) ≤ x + 1` using `(Nat.ceil_lt_add_one hx0.le).le`. Establish `hu1 : 1 ≤ u` using `Real.one_le_rpow hx1 (by linarith)`. Establish `hmu : u ≤ m` using `Nat.le_ceil u`. Establish `hmu1 : (m : ℝ) ≤ u + 1` using `(Nat.ceil_lt_add_one (by linarith)).le`. Establish `h2 : (2 : ℝ) ≤ x ^ (3 * ε / 2)`.

Establish `: x ^ (3 * ε / 8) ≤ x ^ (3 * ε / 2)` using `Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsplit : x ^ ((1 : ℝ) / 2 + ε / 2) = u * x ^ (3 * ε / 2)`. Rewrite using `[hu, ← Real.rpow_add hx0]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `hm2 : (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2)`. Rewrite using `[hsplit]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hmx : (m : ℝ) ≤ x`.

Establish `: x ^ ((1 : ℝ) / 2 + ε / 2) ≤ x ^ (1 : ℝ)` using `Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)`. Rewrite `this` using `[Real.rpow_one]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hk : x * m ≤ (n : ℝ) ^ 2 * u`. Establish `h3 : x * m ≤ x * (2 * u)` using `mul_le_mul_of_nonneg_left (by linarith) hx0.le`.

Establish `h4 : x * 2 ≤ (n : ℝ) ^ 2` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Use `set b : ℝ := 12 * n * (x + 1) * x with hb`. Establish `hn0 : (0 : ℝ) < n` using `by linarith`. Establish `hb0 : 0 < b` using `by rw [hb]; positivity`.

Establish `hb4 : b ≤ x ^ 4`. Establish `e1 : b ≤ 12 * (x + 1) * (x + 1) * x`. Rewrite using `[hb]`. Establish `: 12 * (n : ℝ) * (x + 1) ≤ 12 * (x + 1) * (x + 1)` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.

Establish `e2 : 12 * (x + 1) * (x + 1) * x ≤ 48 * x ^ 3` using `by nlinarith [mul_pos hx0 hx0]`. Establish `e3 : 48 * x ^ 3 ≤ x ^ 4`. Establish `: 0 ≤ x ^ 3` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hL : Real.log b ≤ 2 * x ^ ε`. Establish `e1 : Real.log b ≤ 4 * Real.log x`. Use `Real.log_le_log hb0 hb4` as an intermediate fact. Rewrite `this` using `[Real.log_pow]`. Simplify using `using this`.

Establish `e2 : x ^ ε = x ^ (ε / 2) * x ^ (ε / 2)`. Rewrite using `[← Real.rpow_add hx0]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `e3 : (200 : ℝ) ≤ x ^ (ε / 2)`.

Establish `: KBig 0 0 0 = 200` using `by norm_num [KBig]`. Rewrite `hbig` using `[this]`. Conclude with `hbig`. Rewrite using `[e2]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `: NeZero n` using `⟨by`. Introduce `h0`. Rewrite `hn0` using `[h0]`. Simplify using `at hn0⟩`. Conclude with `sizesOf (H := ZMod n) x ε b m ⌈x * b⌉₊ n (ZMod.card n) (by linarith) hε0 (by linarith) hnx hb hmu hm2 hmx hk hL (Nat.le_ceil _) (by`.

Rewrite using `[Real.le_log_iff_exp_le hx0]`. Establish `h1 : Real.exp 3 = Real.exp 1 ^ 3`. Rewrite using `[← Real.exp_nat_mul]`. Evaluate the numerical expressions. Establish `h2` using `Real.exp_one_lt_d9`.

Establish `h3 : Real.exp 1 ^ 3 ≤ 2.7182818286 ^ 3` using `pow_le_pow_left₀ (Real.exp_pos 1).le h2.le 3`. Rewrite using `[h1]`. Establish `h4 : (2.7182818286 : ℝ) ^ 3 ≤ 48` using `by norm_num`. Use the proof step `linarith)`.
-/
theorem sizesEv : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    SizesAt 1 1 2 ε x ∧ XLarge 1 1 2 0 0 ε x := by
  intro ε hε0 hε2
  obtain ⟨x₁, hx₁⟩ := x_large_eventually 1 1 2 0 0 ε hε0
  obtain ⟨x₂, hx₂⟩ := Formalism.LFunctionChainParameters.LErr.large_x_eventually (ε / 2) 0 0 0 (by positivity)
  refine ⟨max (max x₁ x₂) 48, fun x hx => ?_⟩
  have hXL := hx₁ x (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx)
  obtain ⟨hlog, hbig⟩ := hx₂ x (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx)
  have hx48 : 48 ≤ x := le_trans (le_max_right _ _) hx
  refine ⟨?_, hXL⟩
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  obtain ⟨-, h26, -, -⟩ := hXL
  set n : ℕ := ⌈x⌉₊ with hn
  set u : ℝ := x ^ ((1 : ℝ) / 2 - ε) with hu
  set m : ℕ := ⌈u⌉₊ with hm
  have hnx : x ≤ n := Nat.le_ceil x
  have hnx1 : (n : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one hx0.le).le
  have hu1 : 1 ≤ u := Real.one_le_rpow hx1 (by linarith)
  have hmu : u ≤ m := Nat.le_ceil u
  have hmu1 : (m : ℝ) ≤ u + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have h2 : (2 : ℝ) ≤ x ^ (3 * ε / 2) := by
    have : x ^ (3 * ε / 8) ≤ x ^ (3 * ε / 2) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    linarith
  have hsplit : x ^ ((1 : ℝ) / 2 + ε / 2) = u * x ^ (3 * ε / 2) := by
    rw [hu, ← Real.rpow_add hx0]
    congr 1
    ring
  have hm2 : (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2) := by
    rw [hsplit]
    nlinarith
  have hmx : (m : ℝ) ≤ x := by
    have : x ^ ((1 : ℝ) / 2 + ε / 2) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    rw [Real.rpow_one] at this
    linarith
  have hk : x * m ≤ (n : ℝ) ^ 2 * u := by
    have h3 : x * m ≤ x * (2 * u) := mul_le_mul_of_nonneg_left (by linarith) hx0.le
    have h4 : x * 2 ≤ (n : ℝ) ^ 2 := by nlinarith
    nlinarith
  set b : ℝ := 12 * n * (x + 1) * x with hb
  have hn0 : (0 : ℝ) < n := by linarith
  have hb0 : 0 < b := by rw [hb]; positivity
  have hb4 : b ≤ x ^ 4 := by
    have e1 : b ≤ 12 * (x + 1) * (x + 1) * x := by
      rw [hb]
      have : 12 * (n : ℝ) * (x + 1) ≤ 12 * (x + 1) * (x + 1) := by nlinarith
      nlinarith
    have e2 : 12 * (x + 1) * (x + 1) * x ≤ 48 * x ^ 3 := by nlinarith [mul_pos hx0 hx0]
    have e3 : 48 * x ^ 3 ≤ x ^ 4 := by
      have : 0 ≤ x ^ 3 := by positivity
      nlinarith
    linarith
  have hL : Real.log b ≤ 2 * x ^ ε := by
    have e1 : Real.log b ≤ 4 * Real.log x := by
      have := Real.log_le_log hb0 hb4
      rw [Real.log_pow] at this
      simpa using this
    have e2 : x ^ ε = x ^ (ε / 2) * x ^ (ε / 2) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    have e3 : (200 : ℝ) ≤ x ^ (ε / 2) := by
      have : KBig 0 0 0 = 200 := by norm_num [KBig]
      rw [this] at hbig
      exact hbig
    rw [e2]
    nlinarith
  have : NeZero n := ⟨by
    intro h0
    rw [h0] at hn0
    simp at hn0⟩
  exact sizesOf (H := ZMod n) x ε b m ⌈x * b⌉₊ n (ZMod.card n) (by linarith) hε0 (by linarith) hnx hb hmu hm2 hmx hk hL
    (Nat.le_ceil _) (by
      rw [Real.le_log_iff_exp_le hx0]
      have h1 : Real.exp 3 = Real.exp 1 ^ 3 := by
        rw [← Real.exp_nat_mul]
        norm_num
      have h2 := Real.exp_one_lt_d9
      have h3 : Real.exp 1 ^ 3 ≤ 2.7182818286 ^ 3 := pow_le_pow_left₀ (Real.exp_pos 1).le h2.le 3
      rw [h1]
      have h4 : (2.7182818286 : ℝ) ^ 3 ≤ 48 := by norm_num
      linarith)

/- English proof (translation)
Introduce `ε h0 h1`. Take `⟨x₀, hx₀⟩` from `sizesEv ε h0 h1`. Conclude with `⟨x₀, fun x hx => ⟨coreOfSizes (hx₀ x hx).1, (hx₀ x hx).2⟩⟩`.
-/
theorem coreNoAnalyticEv : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ChainCoreNoAnalytic 1 1 1 1 2 ε x ∧ XLarge 1 1 2 0 0 ε x := by
  intro ε h0 h1
  obtain ⟨x₀, hx₀⟩ := sizesEv ε h0 h1
  exact ⟨x₀, fun x hx => ⟨coreOfSizes (hx₀ x hx).1, (hx₀ x hx).2⟩⟩

end ModelEv

/- English proof (translation)
Introduce `ε h0 h1`. Take `⟨x₀, hx₀⟩` from `ModelEv.coreNoAnalyticEv ε h0 h1`. Conclude with `⟨x₀, fun x hx => (hx₀ x hx).1⟩`.
-/
theorem chain_sizes_model_eventually : ChainSizesModelEv := by
  intro ε h0 h1
  obtain ⟨x₀, hx₀⟩ := ModelEv.coreNoAnalyticEv ε h0 h1
  exact ⟨x₀, fun x hx => (hx₀ x hx).1⟩

namespace ModelText

/- English proof (translation)
Establish `hc : 0 < (|c| + 1)⁻¹` using `by positivity`. Establish `hb` using `(isLittleO_log_rpow_atTop hδ).bound hc`. Use `filter_upwards [hb, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1`. Rewrite `hx` using `[Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _), Real.norm_of_nonneg (Real.log_nonneg hx1)]`. Establish `hxpos : 0 < x` using `by linarith`.

Establish `h1 : (|c| + 1) * Real.log x ≤ x ^ δ`. Establish `: (|c| + 1) * Real.log x ≤ (|c| + 1) * ((|c| + 1)⁻¹ * x ^ δ)` using `by gcongr`. Rewrite `this` using `[mul_inv_cancel_left₀ (by positivity)]`. Then use the resulting hypothesis. Rewrite using `[Real.rpow_def_of_pos hxpos]`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises.

Establish `hlog0` using `Real.log_nonneg hx1`. Establish `: Real.log x * c ≤ Real.log x * |c|` using `by gcongr; exact le_abs_self c`. Use polynomial arithmetic with `[abs_nonneg c]`.
-/
lemma ev_rpow_le_exp (c δ : ℝ) (hδ : 0 < δ) : ∀ᶠ x : ℝ in Filter.atTop, x ^ c ≤ Real.exp (x ^ δ) := by
  have hc : 0 < (|c| + 1)⁻¹ := by positivity
  have hb := (isLittleO_log_rpow_atTop hδ).bound hc
  filter_upwards [hb, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _), Real.norm_of_nonneg (Real.log_nonneg hx1)] at hx
  have hxpos : 0 < x := by linarith
  have h1 : (|c| + 1) * Real.log x ≤ x ^ δ := by
    have : (|c| + 1) * Real.log x ≤ (|c| + 1) * ((|c| + 1)⁻¹ * x ^ δ) := by gcongr
    rwa [mul_inv_cancel_left₀ (by positivity)] at this
  rw [Real.rpow_def_of_pos hxpos]
  apply Real.exp_le_exp.2
  have hlog0 := Real.log_nonneg hx1
  have : Real.log x * c ≤ Real.log x * |c| := by gcongr; exact le_abs_self c
  nlinarith [abs_nonneg c]

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

def kTx (x ε : ℝ) : ℝ := x ^ ((9 : ℝ) / 2 + 10 * ε)

def etaTx (x ε : ℝ) : ℝ := Real.exp (x ^ (ε / 4))

def thTx (x ε : ℝ) : ℝ := Real.exp (-(x ^ (ε / 8)))

def wF (x ε : ℝ) (m : ℕ) (TT T2 : Finset H) : H → Fin m → E0 × H → ℝ := fun u0 _ ρ =>
  if IsThickAt T2 u0 ρ then bTx x ε + etaTx x ε
  else if ρ ∈ TT.image topPl then 2 * bpTx x ε else wppTx x ε (Fintype.card H)

def NF (H : Type) [Fintype H] (x ε : ℝ) : ℕ := ⌈XppTx x ε (Fintype.card H)⌉₊

def textData (x ε : ℝ) (m : ℕ) (TT T2 : Finset H) : Data H (fun _ => Unit) TT m (Model.fM H) where
  x := x
  ε := ε
  a := aTx x ε
  b := bTx x ε
  b' := bpTx x ε
  k := kTx x ε
  L := x ^ ε
  La := Real.log (aTx x ε) + x ^ (ε / 3)
  B0 := (2 * (Fintype.card H : ℝ)) * m * bTx x ε * x ^ ε
  Nc := (T2.card : ℝ) * kTx x ε * bTx x ε * x ^ ε / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * x ^ (-ε)))
  gam := Real.eulerMascheroniConstant
  LpL := 0
  v := 1
  lg := 0
  logGam := 0
  aT := fun _ => aTx x ε
  w := fun u0 j ρ => wF x ε m TT T2 u0 j (Model.ePM ρ)
  d := fun _ _ => 1
  T := fun _ _ => 1
  muN := fun _ _ => 0
  muMaxN := fun _ _ => 0
  h := fun _ _ => 0
  muM := fun _ _ => 0
  muMaxM := fun _ _ => 0
  EeJ := fun _ _ _ => 0
  muCC := fun _ => 0
  muMinCC := fun _ => 0
  Fo := fun _ => 0
  Ga := fun _ => 0
  Ta := fun _ => 0
  ASK := fun u0 => ∑ t ∈ TT, ∑ j : Fin m, ASK Model.DA (NF H x ε) (aTx x ε) t (wF x ε m TT T2 u0 j)
  IO := fun _ => 0
  HH := fun _ => 1
  del := fun _ => 0
  η := fun _ => 0
  e := fun _ => 0
  delBar := 0
  etaBar := x ^ (-1 : ℝ)
  eBar := 0

def CF : Consts := ⟨1, 1, 1, 1, 2, 1, 1, 1, 1, 1⟩

def AllSizes (x ε : ℝ) (m : ℕ) (TT T2 : Finset H) : Prop :=
  HostFacts (Model.DA (H := H)) ∧
  Ident (textData x ε m TT T2) Model.DA (NF H x ε) (fun _ => 0) TT (fun _ => aTx x ε) (wF x ε m TT T2)
    (Equiv.refl _) Model.ePM ∧
  ErrWindows (textData x ε m TT T2) CF (XppTx x ε (Fintype.card H)) 15 2 ∧
  BNBounds (textData x ε m TT T2) T2 ∧
  GrowthInequalitySizes TT T2 (fun _ => aTx x ε) (wF x ε m TT T2) (NF H x ε) x (bTx x ε) (bpTx x ε) (etaTx x ε) (XpTx x ε)
    (thTx x ε) ∧
  CostWindows x (fPl H) (bTx x ε) (etaTx x ε) (thTx x ε) ∧
  RestSize ε x (Fintype.card H) TT.card T2.card m (bTx x ε) (kTx x ε) (aTx x ε) ∧
  (∀ u0, 0 ≤ ∑ j : Fin m, (1 / (Model.fM H : ℝ)) * ∑ ρ : Fin (Model.fM H), Real.log ((textData x ε m TT T2).w u0 j ρ)) ∧
  (∀ u0, ∑ j : Fin m, (1 / (Model.fM H : ℝ)) * ∑ ρ : Fin (Model.fM H), Real.log ((textData x ε m TT T2).w u0 j ρ)
    ≤ CF.cCount * (m : ℝ) * (textData x ε m TT T2).L)

/- English proof (translation)
Take `⟨hx1, hb1, hlogb, hLa, hka, hbp0, hkbp, hX0, hXa⟩` from `hT`. Establish `hx0 : 0 < x` using `by linarith`. Establish `hb0 : 0 < bTx x ε` using `by linarith`. Establish `ha : aTx x ε = x * bTx x ε` using `rfl`. Establish `ha0 : 0 < aTx x ε` using `by rw [ha]; positivity`.

Establish `hab : bTx x ε ≤ aTx x ε` using `by rw [ha]; exact le_mul_of_one_le_left hb0.le hx1`. Establish `hXp0 : 0 < XpTx x ε` using `Real.exp_pos _`. Establish `hbp : 0 < bpTx x ε` using `div_pos ha0 hXp0`. Establish `hn0 : (0 : ℝ) < (Fintype.card H : ℝ)` using `by exact_mod_cast Fintype.card_pos`. Establish `hn1 : (1 : ℝ) ≤ (Fintype.card H : ℝ)` using `by exact_mod_cast Fintype.card_pos`.

Establish `hxe1 : 1 ≤ x ^ ε` using `Real.one_le_rpow hx1 hε0.le`. Establish `hk_x : x ≤ kTx x ε`. Use `Real.rpow_le_rpow_of_exponent_le hx1 (by linarith : (1 : ℝ) ≤ (9 : ℝ) / 2 + 10 * ε)` as an intermediate fact. Rewrite `this` using `[Real.rpow_one]`. Then use the resulting hypothesis. Establish `hk0 : 0 < kTx x ε` using `by linarith`.

Establish `heta0 : 0 < etaTx x ε` using `Real.exp_pos _`. Establish `hetab : etaTx x ε ≤ bTx x ε` using `Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))`. Establish `hbpb : bpTx x ε ≤ bTx x ε`. Establish `h1 : x * bpTx x ε ≤ x * bTx x ε` using `le_trans (mul_le_mul_of_nonneg_right hk_x hbp.le) hkbp`. Conclude with `le_of_mul_le_mul_left h1 hx0`.

Establish `hwpp0 : 0 < wppTx x ε (Fintype.card H)` using `by linarith`. Establish `hwppbp : wppTx x ε (Fintype.card H) ≤ bpTx x ε`. Unfold `wppTx`. Conclude with `div_le_self hbp.le (by nlinarith)`. Establish `hnT : (textData x ε m TT T2).nT = (TT.card : ℝ)`.

Unfold `Data.nT`. Rewrite using `[Fintype.card_coe]`. Establish `hTTpos : (0 : ℝ) < TT.card` using `lt_of_lt_of_le (by positivity) hTT`. Establish `hTT1 : (1 : ℝ) ≤ TT.card`. Establish `: 0 < TT.card` using `by exact_mod_cast hTTpos`.

Conclude with `this` after adjusting the coercions. Establish `hm_hi : (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2)`. Establish `e : x ^ ((1 : ℝ) / 2 + ε / 2) = x ^ (9 * ε / 16) * x ^ ((1 : ℝ) / 2 - ε / 16)`. Rewrite using `[← Real.rpow_add hx0]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `hmhi.trans (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hx0.le _))`. Establish `hxm : x * m ≤ kTx x ε`. Establish `h1 : x * m ≤ x ^ (1 : ℝ) * x ^ ((1 : ℝ) / 2 + ε / 2)`.

Rewrite using `[Real.rpow_one]`. Conclude with `mul_le_mul_of_nonneg_left hm_hi hx0.le`. Rewrite `h1` using `[← Real.rpow_add hx0]`. Conclude with `h1.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))`. Establish `hw : ∀ u0 j ρ, wppTx x ε (Fintype.card H) ≤ wF x ε m TT T2 u0 j ρ ∧ wF x ε m TT T2 u0 j ρ ≤ 2 * bTx x ε`.

Introduce `u0 j ρ`. Unfold `wF`. Use `split_ifs`. Apply the tactic sequence `constructor <;> linarith`. Apply the tactic sequence `constructor <;> linarith`.

Apply the tactic sequence `constructor <;> linarith`. Establish `hlogw : ∀ u0 j ρ, 0 ≤ Real.log (wF x ε m TT T2 u0 j ρ) ∧ Real.log (wF x ε m TT T2 u0 j ρ) ≤ 2 * x ^ ε`. Introduce `u0 j ρ`. Take `⟨h1, h2'⟩` from `hw u0 j ρ`. Use `⟨Real.log_nonneg (by linarith), ?_⟩` and prove the remaining obligations.

Establish `h3` using `Real.log_le_log (by linarith) h2'`. Rewrite `h3` using `[Real.log_mul (by norm_num) hb0.ne', hlogb]`. Establish `h4 : Real.log 2 ≤ 2 - 1` using `Real.log_le_sub_one_of_pos (by norm_num)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hf : (0 : ℝ) < (Model.fM H : ℝ)` using `by exact_mod_cast Model.fM_pos`.

Use `⟨Model.hostFacts_DA, ⟨fun _ => rfl, fun _ _ _ => rfl, rfl, by simp [textData], fun _ => rfl⟩, ⟨?_, ?_⟩, ⟨le_refl _, le_refl _⟩, ?_, ⟨?_, ?_⟩, ⟨?_, hTT, ?_, ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Use `⟨hx1, hε0, hε1, hb1, le_refl _, by rw [hnT]; exact hTT1, hm_hi, hxm, by norm_num, by show (1 : ℝ) ≤ kTx x ε linarith, ?_, hka, Real.rpow_nonneg hx0.le _, ?_, ?_, hLa, hbp0, hkbp, hX0, hXa, fun _ => ⟨ha0.le, ?_⟩, ?_, ?_, fun _ => ?_, by show (0 : ℝ) ≤ 1 / 2; norm_num, Real.rpow_no …` and prove the remaining obligations. Conclude with `Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)`. Use `show x ^ ε ≤ 2 * x ^ ε`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `show 0 ≤ Real.log (aTx x ε) + x ^ (ε / 3)`. Use `Real.log_nonneg (by linarith : (1 : ℝ) ≤ aTx x ε)` as an intermediate fact. Use `Real.rpow_nonneg hx0.le (ε / 3)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `show aTx x ε ≤ 2 * aTx x ε`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `show 0 ≤ (2 * (Fintype.card H : ℝ)) * m * bTx x ε * x ^ ε`. Check the signs of the components of the expression. Use `show 0 ≤ (T2.card : ℝ) * kTx x ε * bTx x ε * x ^ ε / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * x ^ (-ε)))`. Check the signs of the components of the expression.

Simplify using `only [Fintype.card_unit, Nat.cast_one, Real.log_one]`. Conclude with `mul_nonneg (by show 0 ≤ kTx x ε - 3; linarith) (Real.log_nonneg (by norm_num))`. Apply the tactic sequence `refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [CF]`. Rewrite using `[hnT]`. Use `show (x ^ (-1 : ℝ) + 4 * Real.sqrt 0) * (x ^ (1 : ℝ) * bTx x ε) ≤ 2 * x ^ ε * ((TT.card : ℝ) * aTx x ε)`.

Rewrite using `[Real.sqrt_zero, mul_zero, add_zero, ← mul_assoc, ← Real.rpow_add hx0]`. Evaluate the numerical expressions. Establish `h1 : aTx x ε ≤ (TT.card : ℝ) * aTx x ε` using `le_mul_of_one_le_left ha0.le hTT1`. Establish `h3 : (TT.card : ℝ) * aTx x ε ≤ 2 * x ^ ε * ((TT.card : ℝ) * aTx x ε)` using `le_mul_of_one_le_left (by positivity) (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `⟨heta0.le, hXp0, hbp, ?_, (Real.exp_pos _).le, fun t _ => ?_, ⟨fun u0 j ρ _ => ?_, fun u0 j ρ h => ?_, fun u0 j ρ _ h => ?_⟩, fun u0 j t ρ _ _ => ?_⟩` and prove the remaining obligations. Establish `: bpTx x ε * XpTx x ε = aTx x ε` using `div_mul_cancel₀ _ hXp0.ne'`. Rewrite using `[this, ha]`. Establish `: aTx x ε / bTx x ε = x` using `by rw [ha]; field_simp`. Rewrite using `[this]`.

Simplify using the standard rewrite rules. Combine the linear relations using `[(hw u0 j ρ).1]`. Establish `: wF x ε m TT T2 u0 j ρ = bTx x ε + etaTx x ε` using `by unfold wF; rw [if_pos h]`. Rewrite using `[this]`. Apply the tactic sequence `constructor <;> linarith`.

Unfold `wF`. Rewrite using `[if_neg h]`. Use `split_ifs`. Conclude with `le_refl _`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1 : aTx x ε / wF x ε m TT T2 u0 j ρ ≤ aTx x ε / wppTx x ε (Fintype.card H)` using `div_le_div_of_nonneg_left ha0.le hwpp0 (hw u0 j ρ).1`. Conclude with `h1.trans (Nat.le_ceil _)`. Rewrite using `[Model.fPl_eq]`. Conclude with `hc1`. Rewrite using `[Model.fPl_eq]`.

Conclude with `hc2`. Rewrite using `[ha]`. Use polynomial arithmetic with `[mul_pos hx0 hb0]`. Rewrite using `[le_div_iff₀ hn0]`. Conclude with `hT2`.

Conclude with `(Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)).trans hmlo`. Establish `h1 : (x ^ (2 + 8 * ε)) ^ 2 ≤ (Fintype.card H : ℝ) ^ 2` using `pow_le_pow_left₀ (Real.rpow_nonneg hx0.le _) hnlo 2`. Establish `h3 : kTx x ε ≤ (x ^ (2 + 8 * ε)) ^ 2 * x ^ ((1 : ℝ) / 2 - ε)`. Rewrite using `[sq, ← Real.rpow_add hx0, ← Real.rpow_add hx0]`. Conclude with `Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)`.

Conclude with `h3.trans (mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hx0.le _))`. Introduce `u0`. Use `Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (Finset.sum_nonneg fun ρ _ => ?_)` and prove the remaining obligations. Conclude with `(hlogw u0 j (Model.ePM ρ)).1`. Introduce `u0`.

Establish `h1 : ∀ j : Fin m, (1 / (Model.fM H : ℝ)) * ∑ ρ : Fin (Model.fM H), Real.log ((textData x ε m TT T2).w u0 j ρ) ≤ 2 * x ^ ε`. Introduce `j`. Establish `h2' : ∑ ρ : Fin (Model.fM H), Real.log ((textData x ε m TT T2).w u0 j ρ) ≤ ∑ _ρ : Fin (Model.fM H), 2 * x ^ ε` using `Finset.sum_le_sum fun ρ _ => (hlogw u0 j (Model.ePM ρ)).2`. Rewrite `h2'` using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation.

Establish `h3` using `Finset.sum_le_sum (s := (univ : Finset (Fin m))) fun j _ => h1 j`. Rewrite `h3` using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Use `show _ ≤ (2 : ℝ) * (m : ℝ) * x ^ ε`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem famAt (x ε : ℝ) (m : ℕ) (TT T2 : Finset H)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hx : 3 ≤ x)
    (hT : 1 ≤ x ∧ 1 ≤ bTx x ε ∧ Real.log (bTx x ε) = x ^ ε ∧ Real.log (aTx x ε) + x ^ (ε / 3) ≤ 2 * x ^ ε ∧
      kTx x ε ≤ aTx x ε ∧ 0 ≤ bpTx x ε ∧ kTx x ε * bpTx x ε ≤ aTx x ε ∧
      0 ≤ XppTx x ε (Fintype.card H) ∧ XppTx x ε (Fintype.card H) ≤ aTx x ε)
    (hnlo : x ^ (2 + 8 * ε) ≤ (Fintype.card H : ℝ))
    (hmlo : x ^ ((1 : ℝ) / 2 - ε / 16) ≤ m) (hmhi : (m : ℝ) ≤ 2 * x ^ ((1 : ℝ) / 2 - ε / 16))
    (h2 : 2 ≤ x ^ (9 * ε / 16))
    (hTT : x ^ (-(ε / 8)) * (Fintype.card H : ℝ) / 2 ≤ TT.card)
    (hT2 : x ^ (-ε) * (Fintype.card H : ℝ) ≤ T2.card)
    (hc1 : 2 * (2 * (Fintype.card H : ℝ)) * (x + 1) * thTx x ε ≤ 1 / x)
    (hc2 : 6 * (2 * (Fintype.card H : ℝ)) * (x + 1) * (etaTx x ε + 1) ≤ bTx x ε / x)
    (hw1 : 1 ≤ wppTx x ε (Fintype.card H)) : AllSizes x ε m TT T2 := by
  obtain ⟨hx1, hb1, hlogb, hLa, hka, hbp0, hkbp, hX0, hXa⟩ := hT
  have hx0 : 0 < x := by linarith
  have hb0 : 0 < bTx x ε := by linarith
  have ha : aTx x ε = x * bTx x ε := rfl
  have ha0 : 0 < aTx x ε := by rw [ha]; positivity
  have hab : bTx x ε ≤ aTx x ε := by rw [ha]; exact le_mul_of_one_le_left hb0.le hx1
  have hXp0 : 0 < XpTx x ε := Real.exp_pos _
  have hbp : 0 < bpTx x ε := div_pos ha0 hXp0
  have hn0 : (0 : ℝ) < (Fintype.card H : ℝ) := by exact_mod_cast Fintype.card_pos
  have hn1 : (1 : ℝ) ≤ (Fintype.card H : ℝ) := by exact_mod_cast Fintype.card_pos
  have hxe1 : 1 ≤ x ^ ε := Real.one_le_rpow hx1 hε0.le
  have hk_x : x ≤ kTx x ε := by
    have := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith : (1 : ℝ) ≤ (9 : ℝ) / 2 + 10 * ε)
    rwa [Real.rpow_one] at this
  have hk0 : 0 < kTx x ε := by linarith
  have heta0 : 0 < etaTx x ε := Real.exp_pos _
  have hetab : etaTx x ε ≤ bTx x ε :=
    Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
  have hbpb : bpTx x ε ≤ bTx x ε := by
    have h1 : x * bpTx x ε ≤ x * bTx x ε := le_trans (mul_le_mul_of_nonneg_right hk_x hbp.le) hkbp
    exact le_of_mul_le_mul_left h1 hx0
  have hwpp0 : 0 < wppTx x ε (Fintype.card H) := by linarith
  have hwppbp : wppTx x ε (Fintype.card H) ≤ bpTx x ε := by
    unfold wppTx
    exact div_le_self hbp.le (by nlinarith)
  have hnT : (textData x ε m TT T2).nT = (TT.card : ℝ) := by
    unfold Data.nT
    rw [Fintype.card_coe]
  have hTTpos : (0 : ℝ) < TT.card := lt_of_lt_of_le (by positivity) hTT
  have hTT1 : (1 : ℝ) ≤ TT.card := by
    have : 0 < TT.card := by exact_mod_cast hTTpos
    exact_mod_cast this
  have hm_hi : (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2) := by
    have e : x ^ ((1 : ℝ) / 2 + ε / 2) = x ^ (9 * ε / 16) * x ^ ((1 : ℝ) / 2 - ε / 16) := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    rw [e]
    exact hmhi.trans (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hx0.le _))
  have hxm : x * m ≤ kTx x ε := by
    have h1 : x * m ≤ x ^ (1 : ℝ) * x ^ ((1 : ℝ) / 2 + ε / 2) := by
      rw [Real.rpow_one]; exact mul_le_mul_of_nonneg_left hm_hi hx0.le
    rw [← Real.rpow_add hx0] at h1
    exact h1.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))

  have hw : ∀ u0 j ρ, wppTx x ε (Fintype.card H) ≤ wF x ε m TT T2 u0 j ρ ∧ wF x ε m TT T2 u0 j ρ ≤ 2 * bTx x ε := by
    intro u0 j ρ
    unfold wF
    split_ifs
    · constructor <;> linarith
    · constructor <;> linarith
    · constructor <;> linarith
  have hlogw : ∀ u0 j ρ, 0 ≤ Real.log (wF x ε m TT T2 u0 j ρ) ∧ Real.log (wF x ε m TT T2 u0 j ρ) ≤ 2 * x ^ ε := by
    intro u0 j ρ
    obtain ⟨h1, h2'⟩ := hw u0 j ρ
    refine ⟨Real.log_nonneg (by linarith), ?_⟩
    have h3 := Real.log_le_log (by linarith) h2'
    rw [Real.log_mul (by norm_num) hb0.ne', hlogb] at h3
    have h4 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hf : (0 : ℝ) < (Model.fM H : ℝ) := by exact_mod_cast Model.fM_pos
  refine ⟨Model.hostFacts_DA, ⟨fun _ => rfl, fun _ _ _ => rfl, rfl, by simp [textData], fun _ => rfl⟩, ⟨?_, ?_⟩,
    ⟨le_refl _, le_refl _⟩, ?_, ⟨?_, ?_⟩, ⟨?_, hTT, ?_, ?_, ?_⟩, ?_, ?_⟩
  ·
    refine ⟨hx1, hε0, hε1, hb1, le_refl _, by rw [hnT]; exact hTT1, hm_hi, hxm, by norm_num, by
      show (1 : ℝ) ≤ kTx x ε
      linarith, ?_, hka, Real.rpow_nonneg hx0.le _, ?_, ?_, hLa, hbp0, hkbp, hX0, hXa, fun _ => ⟨ha0.le, ?_⟩, ?_, ?_,
      fun _ => ?_, by show (0 : ℝ) ≤ 1 / 2; norm_num, Real.rpow_nonneg hx0.le _, le_refl _, ?_⟩
    · exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    · show x ^ ε ≤ 2 * x ^ ε
      linarith
    · show 0 ≤ Real.log (aTx x ε) + x ^ (ε / 3)
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ aTx x ε)
      have := Real.rpow_nonneg hx0.le (ε / 3)
      linarith
    · show aTx x ε ≤ 2 * aTx x ε
      linarith
    · show 0 ≤ (2 * (Fintype.card H : ℝ)) * m * bTx x ε * x ^ ε
      positivity
    · show 0 ≤ (T2.card : ℝ) * kTx x ε * bTx x ε * x ^ ε / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * x ^ (-ε)))
      positivity
    · simp only [Fintype.card_unit, Nat.cast_one, Real.log_one]
      exact mul_nonneg (by show 0 ≤ kTx x ε - 3; linarith) (Real.log_nonneg (by norm_num))
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [CF]
  ·
    rw [hnT]
    show (x ^ (-1 : ℝ) + 4 * Real.sqrt 0) * (x ^ (1 : ℝ) * bTx x ε) ≤ 2 * x ^ ε * ((TT.card : ℝ) * aTx x ε)
    rw [Real.sqrt_zero, mul_zero, add_zero, ← mul_assoc, ← Real.rpow_add hx0]
    norm_num
    have h1 : aTx x ε ≤ (TT.card : ℝ) * aTx x ε := le_mul_of_one_le_left ha0.le hTT1
    have h3 : (TT.card : ℝ) * aTx x ε ≤ 2 * x ^ ε * ((TT.card : ℝ) * aTx x ε) :=
      le_mul_of_one_le_left (by positivity) (by linarith)
    linarith
  ·
    refine ⟨heta0.le, hXp0, hbp, ?_, (Real.exp_pos _).le, fun t _ => ?_,
      ⟨fun u0 j ρ _ => ?_, fun u0 j ρ h => ?_, fun u0 j ρ _ h => ?_⟩, fun u0 j t ρ _ _ => ?_⟩
    · have : bpTx x ε * XpTx x ε = aTx x ε := div_mul_cancel₀ _ hXp0.ne'
      rw [this, ha]
    · have : aTx x ε / bTx x ε = x := by rw [ha]; field_simp
      rw [this]; simp
    · linarith [(hw u0 j ρ).1]
    · have : wF x ε m TT T2 u0 j ρ = bTx x ε + etaTx x ε := by unfold wF; rw [if_pos h]
      rw [this]
      constructor <;> linarith
    · unfold wF
      rw [if_neg h]
      split_ifs
      · exact le_refl _
      · linarith
    · have h1 : aTx x ε / wF x ε m TT T2 u0 j ρ ≤ aTx x ε / wppTx x ε (Fintype.card H) :=
        div_le_div_of_nonneg_left ha0.le hwpp0 (hw u0 j ρ).1
      exact h1.trans (Nat.le_ceil _)
  · rw [Model.fPl_eq]; exact hc1
  · rw [Model.fPl_eq]; exact hc2
  · rw [ha]; nlinarith [mul_pos hx0 hb0]
  · rw [le_div_iff₀ hn0]; exact hT2
  · exact (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)).trans hmlo
  · have h1 : (x ^ (2 + 8 * ε)) ^ 2 ≤ (Fintype.card H : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Real.rpow_nonneg hx0.le _) hnlo 2
    have h3 : kTx x ε ≤ (x ^ (2 + 8 * ε)) ^ 2 * x ^ ((1 : ℝ) / 2 - ε) := by
      rw [sq, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    exact h3.trans (mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hx0.le _))
  · intro u0
    refine Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (Finset.sum_nonneg fun ρ _ => ?_)
    exact (hlogw u0 j (Model.ePM ρ)).1
  · intro u0
    have h1 : ∀ j : Fin m, (1 / (Model.fM H : ℝ)) * ∑ ρ : Fin (Model.fM H), Real.log ((textData x ε m TT T2).w u0 j ρ)
        ≤ 2 * x ^ ε := by
      intro j
      have h2' : ∑ ρ : Fin (Model.fM H), Real.log ((textData x ε m TT T2).w u0 j ρ)
          ≤ ∑ _ρ : Fin (Model.fM H), 2 * x ^ ε :=
        Finset.sum_le_sum fun ρ _ => (hlogw u0 j (Model.ePM ρ)).2
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2'
      calc (1 / (Model.fM H : ℝ)) * ∑ ρ : Fin (Model.fM H), Real.log ((textData x ε m TT T2).w u0 j ρ)
          ≤ (1 / (Model.fM H : ℝ)) * ((Model.fM H : ℝ) * (2 * x ^ ε)) :=
            mul_le_mul_of_nonneg_left h2' (by positivity)
        _ = 2 * x ^ ε := by field_simp
    have h3 := Finset.sum_le_sum (s := (univ : Finset (Fin m))) fun j _ => h1 j
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
    show _ ≤ (2 : ℝ) * (m : ℝ) * x ^ ε
    linarith

end

/- English proof (translation)
Rewrite using `[show (18 : ℝ) = 15 + 1 + 1 + 1 by norm_num, Real.rpow_add hxpos, Real.rpow_add hxpos, Real.rpow_add hxpos, Real.rpow_one]`.
-/
lemma h18 {x : ℝ} (hxpos : 0 < x) : x ^ (18 : ℝ) = x ^ (15 : ℝ) * x * x * x := by
  rw [show (18 : ℝ) = 15 + 1 + 1 + 1 by norm_num, Real.rpow_add hxpos, Real.rpow_add hxpos, Real.rpow_add hxpos,
    Real.rpow_one]

/- English proof (translation)
Establish `hxpos : 0 < x` using `by linarith`. Establish `hp15 : 0 < x ^ (15 : ℝ)` using `Real.rpow_pos_of_pos hxpos _`. Unfold `thTx`. Rewrite using `[Real.exp_neg, le_div_iff₀ hxpos]`. Establish `hE : 0 < Real.exp (x ^ (ε / 8))` using `Real.exp_pos _`.

Establish `h1 : 2 * (2 * n) * (x + 1) * x ≤ Real.exp (x ^ (ε / 8))`. Use `le_trans ?_ f1` and prove the remaining obligations. Rewrite using `[h18 hxpos]`. Establish `h2 : 2 * (2 * n) * (x + 1) * x ≤ 2 * (2 * x ^ (15 : ℝ)) * (x + 1) * x` using `by gcongr`. Establish `h3 : 2 * (2 * x ^ (15 : ℝ)) * (x + 1) * x ≤ x ^ (15 : ℝ) * x * x * x`.

Establish `h4 : 4 * (x + 1) ≤ x * x` using `by nlinarith`. Establish `h5 : 0 < x ^ (15 : ℝ) * x` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.
-/
lemma cost1 {x ε n : ℝ} (h48 : 48 ≤ x) (_hn0 : 0 < n) (hn15 : n ≤ x ^ (15 : ℝ))
    (f1 : x ^ (18 : ℝ) ≤ Real.exp (x ^ (ε / 8))) : 2 * (2 * n) * (x + 1) * thTx x ε ≤ 1 / x := by
  have hxpos : 0 < x := by linarith
  have hp15 : 0 < x ^ (15 : ℝ) := Real.rpow_pos_of_pos hxpos _
  unfold thTx
  rw [Real.exp_neg, le_div_iff₀ hxpos]
  have hE : 0 < Real.exp (x ^ (ε / 8)) := Real.exp_pos _
  have h1 : 2 * (2 * n) * (x + 1) * x ≤ Real.exp (x ^ (ε / 8)) := by
    refine le_trans ?_ f1
    rw [h18 hxpos]
    have h2 : 2 * (2 * n) * (x + 1) * x ≤ 2 * (2 * x ^ (15 : ℝ)) * (x + 1) * x := by gcongr
    have h3 : 2 * (2 * x ^ (15 : ℝ)) * (x + 1) * x ≤ x ^ (15 : ℝ) * x * x * x := by
      have h4 : 4 * (x + 1) ≤ x * x := by nlinarith
      have h5 : 0 < x ^ (15 : ℝ) * x := by positivity
      calc 2 * (2 * x ^ (15 : ℝ)) * (x + 1) * x = (x ^ (15 : ℝ) * x) * (4 * (x + 1)) := by ring
        _ ≤ (x ^ (15 : ℝ) * x) * (x * x) := by gcongr
        _ = x ^ (15 : ℝ) * x * x * x := by ring
    linarith
  calc 2 * (2 * n) * (x + 1) * (Real.exp (x ^ (ε / 8)))⁻¹ * x
      = (2 * (2 * n) * (x + 1) * x) * (Real.exp (x ^ (ε / 8)))⁻¹ := by ring
    _ ≤ Real.exp (x ^ (ε / 8)) * (Real.exp (x ^ (ε / 8)))⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ hE.ne'

/- English proof (translation)
Establish `hxpos : 0 < x` using `by linarith`. Establish `hp15 : 0 < x ^ (15 : ℝ)` using `Real.rpow_pos_of_pos hxpos _`. Rewrite using `[le_div_iff₀ hxpos]`. Unfold `etaTx bTx`. Take `⟨E, hE⟩ : ∃ E, E = Real.exp (x ^ (ε / 4))` from `⟨_, rfl⟩`.

Establish `hE1 : 1 ≤ E` using `by rw [hE]; exact Real.one_le_exp (Real.rpow_nonneg hxpos.le _)`. Establish `hEE : E * E ≤ Real.exp (x ^ ε)`. Rewrite using `[hE, ← Real.exp_add]`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Establish `h : x ^ ε = x ^ (3 * ε / 4) * x ^ (ε / 4)`.

Rewrite using `[← Real.rpow_add hxpos]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h]`. Use `Real.rpow_nonneg hxpos.le (ε / 4)` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Rewrite `f2`, the goal using `[← hE]`. Establish `h1 : 6 * (2 * n) * (x + 1) * x * 2 ≤ E`. Use `le_trans ?_ f2` and prove the remaining obligations. Rewrite using `[h18 hxpos]`.

Establish `h2 : 6 * (2 * n) * (x + 1) * x * 2 ≤ 6 * (2 * x ^ (15 : ℝ)) * (x + 1) * x * 2` using `by gcongr`. Establish `h3 : 6 * (2 * x ^ (15 : ℝ)) * (x + 1) * x * 2 ≤ x ^ (15 : ℝ) * x * x * x`. Establish `h4 : 24 * (x + 1) ≤ x * x` using `by nlinarith`. Establish `h5 : 0 < x ^ (15 : ℝ) * x` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.
-/
lemma cost2 {x ε n : ℝ} (h48 : 48 ≤ x) (hn0 : 0 < n) (hn15 : n ≤ x ^ (15 : ℝ))
    (f2 : x ^ (18 : ℝ) ≤ Real.exp (x ^ (ε / 4))) (f5 : 2 ≤ x ^ (3 * ε / 4)) :
    6 * (2 * n) * (x + 1) * (etaTx x ε + 1) ≤ bTx x ε / x := by
  have hxpos : 0 < x := by linarith
  have hp15 : 0 < x ^ (15 : ℝ) := Real.rpow_pos_of_pos hxpos _
  rw [le_div_iff₀ hxpos]
  unfold etaTx bTx
  obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (x ^ (ε / 4)) := ⟨_, rfl⟩
  have hE1 : 1 ≤ E := by rw [hE]; exact Real.one_le_exp (Real.rpow_nonneg hxpos.le _)
  have hEE : E * E ≤ Real.exp (x ^ ε) := by
    rw [hE, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h : x ^ ε = x ^ (3 * ε / 4) * x ^ (ε / 4) := by
      rw [← Real.rpow_add hxpos]; congr 1; ring
    rw [h]
    have := Real.rpow_nonneg hxpos.le (ε / 4)
    nlinarith
  rw [← hE] at f2 ⊢
  have h1 : 6 * (2 * n) * (x + 1) * x * 2 ≤ E := by
    refine le_trans ?_ f2
    rw [h18 hxpos]
    have h2 : 6 * (2 * n) * (x + 1) * x * 2 ≤ 6 * (2 * x ^ (15 : ℝ)) * (x + 1) * x * 2 := by gcongr
    have h3 : 6 * (2 * x ^ (15 : ℝ)) * (x + 1) * x * 2 ≤ x ^ (15 : ℝ) * x * x * x := by
      have h4 : 24 * (x + 1) ≤ x * x := by nlinarith
      have h5 : 0 < x ^ (15 : ℝ) * x := by positivity
      calc 6 * (2 * x ^ (15 : ℝ)) * (x + 1) * x * 2 = (x ^ (15 : ℝ) * x) * (24 * (x + 1)) := by ring
        _ ≤ (x ^ (15 : ℝ) * x) * (x * x) := by gcongr
        _ = x ^ (15 : ℝ) * x * x * x := by ring
    linarith
  calc 6 * (2 * n) * (x + 1) * (E + 1) * x ≤ 6 * (2 * n) * (x + 1) * (2 * E) * x := by
        gcongr; linarith
    _ = (6 * (2 * n) * (x + 1) * x * 2) * E := by ring
    _ ≤ E * E := by gcongr
    _ ≤ Real.exp (x ^ ε) := hEE

/- English proof (translation)
Establish `hxpos : 0 < x` using `by linarith`. Unfold `wppTx bpTx aTx bTx XpTx`. Take `⟨X, hX⟩ : ∃ X, X = Real.exp (x ^ (ε / 3))` from `⟨_, rfl⟩`. Establish `hX0 : 0 < X` using `by rw [hX]; exact Real.exp_pos _`. Establish `hXX : X * X ≤ Real.exp (x ^ ε)`.

Rewrite using `[hX, ← Real.exp_add]`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Establish `h : x ^ ε = x ^ (2 * ε / 3) * x ^ (ε / 3)`. Rewrite using `[← Real.rpow_add hxpos]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h]`. Use `Real.rpow_nonneg hxpos.le (ε / 3)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Rewrite `f3`, the goal using `[← hX]`.

Establish `hnX : n ≤ X` using `hn15.trans f3`. Rewrite using `[le_div_iff₀ (by positivity), le_div_iff₀ hX0]`. Establish `h : n * X ≤ Real.exp (x ^ ε)` using `(mul_le_mul_of_nonneg_right hnX hX0.le).trans hXX`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma wpp1 {x ε n : ℝ} (h48 : 48 ≤ x) (hn0 : 0 < n) (hn15 : n ≤ x ^ (15 : ℝ))
    (f3 : x ^ (15 : ℝ) ≤ Real.exp (x ^ (ε / 3))) (f6 : 2 ≤ x ^ (2 * ε / 3)) : 1 ≤ wppTx x ε n := by
  have hxpos : 0 < x := by linarith
  unfold wppTx bpTx aTx bTx XpTx
  obtain ⟨X, hX⟩ : ∃ X, X = Real.exp (x ^ (ε / 3)) := ⟨_, rfl⟩
  have hX0 : 0 < X := by rw [hX]; exact Real.exp_pos _
  have hXX : X * X ≤ Real.exp (x ^ ε) := by
    rw [hX, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h : x ^ ε = x ^ (2 * ε / 3) * x ^ (ε / 3) := by
      rw [← Real.rpow_add hxpos]; congr 1; ring
    rw [h]
    have := Real.rpow_nonneg hxpos.le (ε / 3)
    nlinarith
  rw [← hX] at f3 ⊢
  have hnX : n ≤ X := hn15.trans f3
  rw [le_div_iff₀ (by positivity), le_div_iff₀ hX0]
  have h : n * X ≤ Real.exp (x ^ ε) := (mul_le_mul_of_nonneg_right hnX hX0.le).trans hXX
  calc 1 * (x * n) * X = x * (n * X) := by ring
    _ ≤ x * Real.exp (x ^ ε) := by gcongr

def FamAt (ε x : ℝ) : Prop :=
  ∃ (n : ℕ) (_ : NeZero n) (m : ℕ) (TT T2 : Finset (ZMod n)),
    x ^ (2 + 8 * ε) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x ^ (2 + 8 * ε) ∧
    x ^ ((1 : ℝ) / 2 - ε / 16) ≤ m ∧ (m : ℝ) ≤ 2 * x ^ ((1 : ℝ) / 2 - ε / 16) ∧
    (TT.card : ℝ) < x ^ (-(ε / 8)) * n / 2 + 1 ∧ (T2.card : ℝ) < x ^ (-ε) * n + 1 ∧
    AllSizes x ε m TT T2

/- English proof (translation)
Take `⟨x1, hx1⟩` from `text_sizes_windows ε 15 hε0`. Establish `e1` using `ev_rpow_le_exp 18 (ε / 8) (by positivity)`. Establish `e2` using `ev_rpow_le_exp 18 (ε / 4) (by positivity)`. Establish `e3` using `ev_rpow_le_exp 15 (ε / 3) (by positivity)`. Establish `e4 : ∀ᶠ x : ℝ in Filter.atTop, (2 : ℝ) ≤ x ^ (9 * ε / 16)` using `(tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _`.

Establish `e5 : ∀ᶠ x : ℝ in Filter.atTop, (2 : ℝ) ≤ x ^ (3 * ε / 4)` using `(tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _`. Establish `e6 : ∀ᶠ x : ℝ in Filter.atTop, (2 : ℝ) ≤ x ^ (2 * ε / 3)` using `(tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _`. Take `⟨x0, hx0⟩` from `Filter.eventually_atTop.1 (((((((e1.and e2).and e3).and e4).and e5).and e6).and (Filter.eventually_ge_atTop (48 : ℝ))).and (Filter.eventually_ge_atTop x1))`. Use `⟨x0, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨⟨⟨⟨⟨⟨⟨f1, f2⟩, f3⟩, f4⟩, f5⟩, f6⟩, h48⟩, hxx1⟩` from `hx0 x hx`.

Establish `hxpos : 0 < x` using `by linarith`. Establish `hx1' : 1 ≤ x` using `by linarith`. Use `set y : ℝ := x ^ (2 + 8 * ε) with hy`. Establish `hy1 : 1 ≤ y` using `Real.one_le_rpow hx1' (by linarith)`. Use `set n : ℕ := ⌈y⌉₊ with hn`.

Establish `hnpos : 0 < n` using `Nat.ceil_pos.2 (by linarith)`. Establish `: NeZero n` using `⟨hnpos.ne'⟩`. Establish `hnlo : y ≤ (n : ℝ)` using `Nat.le_ceil y`. Establish `hnhi : (n : ℝ) ≤ 2 * y`. Use `(Nat.ceil_lt_add_one (by linarith : 0 ≤ y)).le` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn0 : (0 : ℝ) < n` using `by exact_mod_cast hnpos`. Establish `hn15 : (n : ℝ) ≤ x ^ (15 : ℝ)`. Establish `h1 : 2 * y ≤ x ^ (1 : ℝ) * y` using `by rw [Real.rpow_one]; nlinarith`. Rewrite `h1` using `[hy, ← Real.rpow_add hxpos]`.

Conclude with `hnhi.trans (h1.trans (Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)))`. Use `set z : ℝ := x ^ ((1 : ℝ) / 2 - ε / 16) with hz`. Establish `hz1 : 1 ≤ z` using `Real.one_le_rpow hx1' (by linarith)`. Use `set m : ℕ := ⌈z⌉₊ with hm`. Establish `hmlo : z ≤ (m : ℝ)` using `Nat.le_ceil z`.

Establish `hmhi : (m : ℝ) ≤ 2 * z`. Use `(Nat.ceil_lt_add_one (by linarith : 0 ≤ z)).le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcard : Fintype.card (ZMod n) = n` using `ZMod.card n`. Establish `hd1 : x ^ (-(ε / 8)) ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos hx1' (by linarith)`.

Establish `hd1' : 0 < x ^ (-(ε / 8))` using `Real.rpow_pos_of_pos hxpos _`. Establish `hd2 : x ^ (-ε) ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos hx1' (by linarith)`. Establish `hd2' : 0 < x ^ (-ε)` using `Real.rpow_pos_of_pos hxpos _`. Take `⟨TT, -, hTTc⟩` from `Finset.exists_subset_card_eq (s := (univ : Finset (ZMod n))) (n := ⌈x ^ (-(ε / 8)) * n / 2⌉₊) (by`. Rewrite using `[Finset.card_univ, hcard]`.

Conclude with `Nat.ceil_le.2 (by nlinarith))`. Take `⟨T2, -, hT2c⟩` from `Finset.exists_subset_card_eq (s := (univ : Finset (ZMod n))) (n := ⌈x ^ (-ε) * n⌉₊) (by`. Rewrite using `[Finset.card_univ, hcard]`. Conclude with `Nat.ceil_le.2 (by nlinarith))`. Establish `hk15 : kTx x ε ≤ x ^ (15 : ℝ)` using `Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)`.

Establish `hk0 : 0 < kTx x ε` using `Real.rpow_pos_of_pos hxpos _`. Establish `hT` using `hx1 x (kTx x ε) n (x ^ (ε / 3)) hxx1 hk0 hk15 hn0 hn15 (le_refl _)`. Use `⟨n, inferInstance, m, TT, T2, hnlo, hnhi, hmlo, hmhi, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hTTc]; exact Nat.ceil_lt_add_one (by positivity)`. Rewrite using `[hT2c]; exact Nat.ceil_lt_add_one (by positivity)`.

Use `famAt x ε m TT T2 hε0 hε1 (by linarith) ?_ ?_ hmlo hmhi f4 ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[hcard]`. Conclude with `hT`. Rewrite using `[hcard]`. Conclude with `hnlo`.

Rewrite using `[hcard, hTTc]`. Conclude with `Nat.le_ceil _`. Rewrite using `[hcard, hT2c]`. Conclude with `Nat.le_ceil _`. Rewrite using `[hcard]`.

Conclude with `cost1 h48 hn0 hn15 f1`. Rewrite using `[hcard]`. Conclude with `cost2 h48 hn0 hn15 f2 f5`. Rewrite using `[hcard]`. Conclude with `wpp1 h48 hn0 hn15 f3 f6`.
-/
theorem family (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) : ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → FamAt ε x := by
  obtain ⟨x1, hx1⟩ := text_sizes_windows ε 15 hε0
  have e1 := ev_rpow_le_exp 18 (ε / 8) (by positivity)
  have e2 := ev_rpow_le_exp 18 (ε / 4) (by positivity)
  have e3 := ev_rpow_le_exp 15 (ε / 3) (by positivity)
  have e4 : ∀ᶠ x : ℝ in Filter.atTop, (2 : ℝ) ≤ x ^ (9 * ε / 16) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  have e5 : ∀ᶠ x : ℝ in Filter.atTop, (2 : ℝ) ≤ x ^ (3 * ε / 4) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  have e6 : ∀ᶠ x : ℝ in Filter.atTop, (2 : ℝ) ≤ x ^ (2 * ε / 3) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1
    (((((((e1.and e2).and e3).and e4).and e5).and e6).and (Filter.eventually_ge_atTop (48 : ℝ))).and
      (Filter.eventually_ge_atTop x1))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨⟨f1, f2⟩, f3⟩, f4⟩, f5⟩, f6⟩, h48⟩, hxx1⟩ := hx0 x hx
  have hxpos : 0 < x := by linarith
  have hx1' : 1 ≤ x := by linarith

  set y : ℝ := x ^ (2 + 8 * ε) with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow hx1' (by linarith)
  set n : ℕ := ⌈y⌉₊ with hn
  have hnpos : 0 < n := Nat.ceil_pos.2 (by linarith)
  have : NeZero n := ⟨hnpos.ne'⟩
  have hnlo : y ≤ (n : ℝ) := Nat.le_ceil y
  have hnhi : (n : ℝ) ≤ 2 * y := by
    have := (Nat.ceil_lt_add_one (by linarith : 0 ≤ y)).le
    linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hn15 : (n : ℝ) ≤ x ^ (15 : ℝ) := by
    have h1 : 2 * y ≤ x ^ (1 : ℝ) * y := by rw [Real.rpow_one]; nlinarith
    rw [hy, ← Real.rpow_add hxpos] at h1
    exact hnhi.trans (h1.trans (Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)))

  set z : ℝ := x ^ ((1 : ℝ) / 2 - ε / 16) with hz
  have hz1 : 1 ≤ z := Real.one_le_rpow hx1' (by linarith)
  set m : ℕ := ⌈z⌉₊ with hm
  have hmlo : z ≤ (m : ℝ) := Nat.le_ceil z
  have hmhi : (m : ℝ) ≤ 2 * z := by
    have := (Nat.ceil_lt_add_one (by linarith : 0 ≤ z)).le
    linarith
  have hcard : Fintype.card (ZMod n) = n := ZMod.card n

  have hd1 : x ^ (-(ε / 8)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1' (by linarith)
  have hd1' : 0 < x ^ (-(ε / 8)) := Real.rpow_pos_of_pos hxpos _
  have hd2 : x ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1' (by linarith)
  have hd2' : 0 < x ^ (-ε) := Real.rpow_pos_of_pos hxpos _
  obtain ⟨TT, -, hTTc⟩ := Finset.exists_subset_card_eq (s := (univ : Finset (ZMod n)))
    (n := ⌈x ^ (-(ε / 8)) * n / 2⌉₊) (by
      rw [Finset.card_univ, hcard]
      exact Nat.ceil_le.2 (by nlinarith))
  obtain ⟨T2, -, hT2c⟩ := Finset.exists_subset_card_eq (s := (univ : Finset (ZMod n)))
    (n := ⌈x ^ (-ε) * n⌉₊) (by
      rw [Finset.card_univ, hcard]
      exact Nat.ceil_le.2 (by nlinarith))
  have hk15 : kTx x ε ≤ x ^ (15 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
  have hk0 : 0 < kTx x ε := Real.rpow_pos_of_pos hxpos _
  have hT := hx1 x (kTx x ε) n (x ^ (ε / 3)) hxx1 hk0 hk15 hn0 hn15 (le_refl _)
  refine ⟨n, inferInstance, m, TT, T2, hnlo, hnhi, hmlo, hmhi, ?_, ?_, ?_⟩
  · rw [hTTc]; exact Nat.ceil_lt_add_one (by positivity)
  · rw [hT2c]; exact Nat.ceil_lt_add_one (by positivity)
  · refine famAt x ε m TT T2 hε0 hε1 (by linarith) ?_ ?_ hmlo hmhi f4 ?_ ?_ ?_ ?_ ?_
    · rw [hcard]; exact hT
    · rw [hcard]; exact hnlo
    · rw [hcard, hTTc]; exact Nat.le_ceil _
    · rw [hcard, hT2c]; exact Nat.le_ceil _
    · rw [hcard]; exact cost1 h48 hn0 hn15 f1
    · rw [hcard]; exact cost2 h48 hn0 hn15 f2 f5
    · rw [hcard]; exact wpp1 h48 hn0 hn15 f3 f6

end ModelText

/- English proof (translation)
Introduce `ε h0 h1`. Take `⟨x₀, hx₀⟩` from `ModelText.family ε h0 h1`. Use `⟨x₀, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨n, i, m, TT, T2, s1, s2, s3, s4, s5, s6, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩` from `hx₀ x hx`. Establish `hc : (Fintype.card (ZMod n) : ℝ) = (n : ℝ)` using `by rw [ZMod.card]`.

Use `⟨n, i, TT, inferInstance, m, Model.fM (ZMod n), ModelText.textData x ε m TT T2, ModelText.CF, XppTx x ε (Fintype.card (ZMod n)), Model.DA, fun _ => 0, ModelText.NF (ZMod n) x ε, TT, T2, fun _ => aTx x ε, ModelText.wF x ε m TT T2, Equiv.refl _, Model.ePM, ModelText.etaTx x ε, XpTx …` and prove the remaining obligations. Rewrite using `[hc]`. Both sides reduce to the same expression. Rewrite using `[← hc]`. Both sides reduce to the same expression.

Rewrite using `[← hc]`. Both sides reduce to the same expression.
-/
theorem chain_sizes_eventually : ChainSizesTextEv := by
  intro ε h0 h1
  obtain ⟨x₀, hx₀⟩ := ModelText.family ε h0 h1
  refine ⟨x₀, fun x hx => ?_⟩
  obtain ⟨n, i, m, TT, T2, s1, s2, s3, s4, s5, s6, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := hx₀ x hx
  have hc : (Fintype.card (ZMod n) : ℝ) = (n : ℝ) := by rw [ZMod.card]
  refine ⟨n, i, TT, inferInstance, m, Model.fM (ZMod n), ModelText.textData x ε m TT T2, ModelText.CF,
    XppTx x ε (Fintype.card (ZMod n)), Model.DA, fun _ => 0, ModelText.NF (ZMod n) x ε, TT, T2, fun _ => aTx x ε,
    ModelText.wF x ε m TT T2, Equiv.refl _, Model.ePM, ModelText.etaTx x ε, XpTx x ε, ModelText.thTx x ε,
    rfl, rfl, ⟨s1, s2, s3, s4, s5, s6⟩,
    ⟨rfl, rfl, rfl, rfl, ?_, rfl, (Real.log_exp _).symm, rfl, rfl, rfl, rfl⟩, ⟨?_, ?_⟩,
    ⟨le_refl _, le_refl _, le_refl _⟩, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩
  · rw [hc]; rfl
  · rw [← hc]; rfl
  · rw [← hc]; rfl

end Formalism.LFunctionChainParameters.LChain

section Check2
open Formalism.LFunctionChainParameters.LChain
end Check2
