import Formalism.SizeWindowBrackets.TranslateWordBoundHypotheses
import Formalism.SizeWindowBrackets.ChainSlopeWindows.LevelOfCongruence
import Formalism.SizeWindowBrackets.ChainSlopeWindows.SubThreeMulLogTwoLe
import Formalism.LogVandermondeBounds.HookGammaAmgmMultinomialBounds

open Real

namespace Formalism.LFunctionChainParameters.SectionsFourToSixTransfer

open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LatticeToWeightTransfer

/- English proof (translation)
Unfold `Data.nT`. Conclude with `Nat.cast_nonneg _`.
-/
lemma nT_nonneg {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ}
    (D : Data U0 W Top m f) : 0 ≤ D.nT := by
  unfold Data.nT; exact Nat.cast_nonneg _

/- English proof (translation)
Establish `hk0 : 0 < k` using `by linarith`. Establish `hLa : 0 ≤ La` using `le_trans hL hLLa`. Establish `hna : 0 ≤ nT * a` using `mul_nonneg hn ha`. Establish `hbS : 0 ≤ b' + Sc` using `add_nonneg hb' hSc`. Establish `hmk' : 0 ≤ mR / k` using `div_nonneg hm hk0.le`.

Establish `hT' : logT ≤ cU * (mR * La)`. Use `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLLa hm) hcU` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcmL : 0 ≤ cU * (mR * La)` using `mul_nonneg hcU (mul_nonneg hm hLa)`. Establish `hfkb : 0 ≤ fR * k * (b' + Sc)` using `mul_nonneg (mul_nonneg hf hk0.le) hbS`.

Establish `hfb : 0 ≤ fR * (b' + Sc)` using `mul_nonneg hf hbS`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul_of_nonneg_left hlk (mul_nonneg hcZ hna)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1` using `mul_le_mul_of_nonneg_left hlk hfkb`. Establish `h2` using `mul_le_mul_of_nonneg_right hw1 hLa`. Use `mul_le_mul_of_nonneg_left (le_trans h1 h2) hcZ` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfS : 0 ≤ fR * Sc` using `mul_nonneg hf hSc`.

Establish `h1` using `mul_le_mul_of_nonneg_left hT' hfS`. Establish `h2 : fR * Sc * k ≤ nT * a`. Use `mul_nonneg (mul_nonneg hf hk0.le) hb'` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : fR * Sc * (cU * (mR * La)) = cU * ((fR * Sc * k) * (La * (mR / k)))`.

Clear the denominators using the available nonvanishing facts. Establish `h4 : (fR * Sc * k) * (La * (mR / k)) ≤ nT * a * (La * (mR / k))` using `mul_le_mul_of_nonneg_right h2 (mul_nonneg hLa hmk')`. Establish `h5` using `mul_le_mul_of_nonneg_left h4 hcU`. Establish `h6 : fR * Sc * logT ≤ cU * (nT * a * (La * (mR / k)))` using `by linarith`. Use `mul_le_mul_of_nonneg_left h6 hcZ` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfk : 0 ≤ fR * k ^ 2` using `mul_nonneg hf (sq_nonneg _)`. Establish `h1` using `mul_le_mul_of_nonneg_left hLZ hfk`. Establish `h2` using `mul_le_mul_of_nonneg_right hw2 (mul_nonneg hcL hLa)`. Use `mul_le_mul_of_nonneg_left (le_trans h1 h2) hcZ` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Use `mul_le_mul_of_nonneg_left hlkv (mul_nonneg hcZ hna)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `mul_le_mul_of_nonneg_left hlkv hfkb`. Establish `h2` using `mul_le_mul_of_nonneg_right hw1 hLa`.

Use `mul_le_mul_of_nonneg_left (le_trans h1 h2) hcZ` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `mul_le_mul_of_nonneg_left hT' hfb`. Establish `h2 : fR * (b' + Sc) * mR ≤ nT * a`. Use `mul_le_mul_of_nonneg_left hmk hfb` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3` using `mul_le_mul_of_nonneg_right h2 (mul_nonneg hcU hLa)`. Establish `h4 : fR * (b' + Sc) * logT ≤ cU * (nT * a * La)` using `by linarith`. Use `mul_le_mul_of_nonneg_left h4 hcZ` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma zTerms_real {cZ cL cU a k mR b' Sc L La lk lkv LZ fR nT sA logT : ℝ}
    (hcZ : 0 ≤ cZ) (hcL : 0 ≤ cL) (hcU : 0 ≤ cU) (ha : 0 ≤ a) (hk : 1 ≤ k) (hmk : mR ≤ k)
    (hb' : 0 ≤ b') (hSc : 0 ≤ Sc) (hL : 0 ≤ L) (hLLa : L ≤ La) (hlk : lk ≤ La) (hlkv : lkv ≤ La)
    (hLZ : LZ ≤ cL * La) (hw1 : fR * k * (b' + Sc) ≤ nT * a) (hw2 : fR * k ^ 2 ≤ nT * a)
    (hn : 0 ≤ nT) (hf : 0 ≤ fR) (hm : 0 ≤ mR) (hs0 : 0 ≤ sA) (hs1 : sA ≤ nT * (2 * a / k))
    (hT : logT ≤ cU * mR * L) :
    sA * logT ≤ 2 * cU * (nT * a * La * (mR / k)) ∧
    cZ * nT * a * lk ≤ cZ * (nT * a * La) ∧
    cZ * fR * k * (b' + Sc) * lk ≤ cZ * (nT * a * La) ∧
    cZ * fR * Sc * logT ≤ cZ * cU * (nT * a * La * (mR / k)) ∧
    cZ * fR * k ^ 2 * LZ ≤ cZ * cL * (nT * a * La) ∧
    cZ * nT * a * lkv ≤ cZ * (nT * a * La) ∧
    cZ * fR * (b' + Sc) * (k * lkv) ≤ cZ * (nT * a * La) ∧
    cZ * fR * (b' + Sc) * logT ≤ cZ * cU * (nT * a * La) := by
  have hk0 : 0 < k := by linarith
  have hLa : 0 ≤ La := le_trans hL hLLa
  have hna : 0 ≤ nT * a := mul_nonneg hn ha
  have hbS : 0 ≤ b' + Sc := add_nonneg hb' hSc
  have hmk' : 0 ≤ mR / k := div_nonneg hm hk0.le
  have hT' : logT ≤ cU * (mR * La) := by
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLLa hm) hcU
    linarith
  have hcmL : 0 ≤ cU * (mR * La) := mul_nonneg hcU (mul_nonneg hm hLa)
  have hfkb : 0 ≤ fR * k * (b' + Sc) := mul_nonneg (mul_nonneg hf hk0.le) hbS
  have hfb : 0 ≤ fR * (b' + Sc) := mul_nonneg hf hbS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc sA * logT ≤ sA * (cU * (mR * La)) := mul_le_mul_of_nonneg_left hT' hs0
      _ ≤ nT * (2 * a / k) * (cU * (mR * La)) := mul_le_mul_of_nonneg_right hs1 hcmL
      _ = 2 * cU * (nT * a * La * (mR / k)) := by ring
  · have := mul_le_mul_of_nonneg_left hlk (mul_nonneg hcZ hna)
    linarith
  · have h1 := mul_le_mul_of_nonneg_left hlk hfkb
    have h2 := mul_le_mul_of_nonneg_right hw1 hLa
    have := mul_le_mul_of_nonneg_left (le_trans h1 h2) hcZ
    linarith
  · have hfS : 0 ≤ fR * Sc := mul_nonneg hf hSc
    have h1 := mul_le_mul_of_nonneg_left hT' hfS
    have h2 : fR * Sc * k ≤ nT * a := by
      have := mul_nonneg (mul_nonneg hf hk0.le) hb'
      linarith
    have h3 : fR * Sc * (cU * (mR * La)) = cU * ((fR * Sc * k) * (La * (mR / k))) := by
      field_simp
    have h4 : (fR * Sc * k) * (La * (mR / k)) ≤ nT * a * (La * (mR / k)) :=
      mul_le_mul_of_nonneg_right h2 (mul_nonneg hLa hmk')
    have h5 := mul_le_mul_of_nonneg_left h4 hcU
    have h6 : fR * Sc * logT ≤ cU * (nT * a * (La * (mR / k))) := by linarith
    have := mul_le_mul_of_nonneg_left h6 hcZ
    linarith
  · have hfk : 0 ≤ fR * k ^ 2 := mul_nonneg hf (sq_nonneg _)
    have h1 := mul_le_mul_of_nonneg_left hLZ hfk
    have h2 := mul_le_mul_of_nonneg_right hw2 (mul_nonneg hcL hLa)
    have := mul_le_mul_of_nonneg_left (le_trans h1 h2) hcZ
    linarith
  · have := mul_le_mul_of_nonneg_left hlkv (mul_nonneg hcZ hna)
    linarith
  · have h1 := mul_le_mul_of_nonneg_left hlkv hfkb
    have h2 := mul_le_mul_of_nonneg_right hw1 hLa
    have := mul_le_mul_of_nonneg_left (le_trans h1 h2) hcZ
    linarith
  · have h1 := mul_le_mul_of_nonneg_left hT' hfb
    have h2 : fR * (b' + Sc) * mR ≤ nT * a := by
      have := mul_le_mul_of_nonneg_left hmk hfb
      linarith
    have h3 := mul_le_mul_of_nonneg_right h2 (mul_nonneg hcU hLa)
    have h4 : fR * (b' + Sc) * logT ≤ cU * (nT * a * La) := by linarith
    have := mul_le_mul_of_nonneg_left h4 hcZ
    linarith

/- English proof (translation)
Introduce `U0 W Top _ m f D cZ cL cU Sc LZ logT hW hT`. Take `⟨hcZ, hcL, hcU, ha, hk, hmk, hb', hSc, haT, hL, hLLa, hlk, hlkv, hLZ, hw1, hw2⟩` from `hW`. Establish `hk0 : 0 < D.k` using `by linarith`. Establish `hn` using `nT_nonneg D`. Establish `hs0 : 0 ≤ ∑ t, D.aT t / D.k` using `Finset.sum_nonneg (fun t _ => div_nonneg (haT t).1 hk0.le)`.

Establish `hs1 : ∑ t, D.aT t / D.k ≤ D.nT * (2 * D.a / D.k)`. Establish `: ∑ t, D.aT t / D.k ≤ ∑ _t : Top, 2 * D.a / D.k` using `Finset.sum_le_sum (fun t _ => div_le_div_of_nonneg_right (haT t).2 hk0.le)`. Simplify `this` using `[Data.nT, Finset.sum_const, nsmul_eq_mul]`. Unfold `unitZ`. Conclude with `zTerms_real hcZ hcL hcU ha hk hmk hb' hSc hL hLLa hlk hlkv hLZ hw1 hw2 hn (Nat.cast_nonneg _) (Nat.cast_nonneg _) hs0 hs1 hT`.
-/
theorem z_terms : ZTerms := by
  intro U0 W Top _ m f D cZ cL cU Sc LZ logT hW hT
  obtain ⟨hcZ, hcL, hcU, ha, hk, hmk, hb', hSc, haT, hL, hLLa, hlk, hlkv, hLZ, hw1, hw2⟩ := hW
  have hk0 : 0 < D.k := by linarith
  have hn := nT_nonneg D
  have hs0 : 0 ≤ ∑ t, D.aT t / D.k := Finset.sum_nonneg (fun t _ => div_nonneg (haT t).1 hk0.le)
  have hs1 : ∑ t, D.aT t / D.k ≤ D.nT * (2 * D.a / D.k) := by
    have : ∑ t, D.aT t / D.k ≤ ∑ _t : Top, 2 * D.a / D.k :=
      Finset.sum_le_sum (fun t _ => div_le_div_of_nonneg_right (haT t).2 hk0.le)
    simpa [Data.nT, Finset.sum_const, nsmul_eq_mul] using this
  unfold unitZ
  exact zTerms_real hcZ hcL hcU ha hk hmk hb' hSc hL hLLa hlk hlkv hLZ hw1 hw2 hn
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hs0 hs1 hT

/- English proof (translation)
Introduce `U0 W Top _ m f D C cZ cL cU Sc LZ hW hT hZ hC u0 u`. Take `⟨t1, t2, t3, t4, t5, t6, t7, t8⟩` from `z_terms D cZ cL cU Sc LZ _ hW (hT u0 u)`. Take `⟨hcZ, hcL, hcU, ha, hk, hmk, hb', hSc, haT, hL, hLLa, hlk, hlkv, hLZ, hw1, hw2⟩` from `hW`. Establish `hk0 : 0 < D.k` using `by linarith`. Establish `hU : 0 ≤ unitZ D` using `mul_nonneg (mul_nonneg (nT_nonneg D) ha) (le_trans hL hLLa)`.

Establish `hmk' : 0 ≤ (m : ℝ) / D.k` using `div_nonneg (Nat.cast_nonneg _) hk0.le`. Establish `hUm : 0 ≤ unitZ D * ((m : ℝ) / D.k)` using `mul_nonneg hU hmk'`. Take `⟨z1, z2⟩` from `hZ u0 u`. Establish `e1 : C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k) = C.cSlope * unitZ D + C.cSlope * (unitZ D * ((m : ℝ) / D.k))` using `by unfold unitZ; ring`. Establish `e2 : C.cSlope * D.nT * D.a * D.La = C.cSlope * unitZ D` using `by unfold unitZ; ring`.

Establish `hC1` using `mul_le_mul_of_nonneg_right hC hU`. Establish `hC2` using `mul_le_mul_of_nonneg_right hC hUm`. Unfold `cSlopeZ at hC1 hC2`. Establish `p1 : 0 ≤ cZ * cU * unitZ D` using `mul_nonneg (mul_nonneg hcZ hcU) hU`. Establish `p2 : 0 ≤ cU * unitZ D` using `mul_nonneg hcU hU`.

Establish `p3 : 0 ≤ cZ * unitZ D` using `mul_nonneg hcZ hU`. Establish `p4 : 0 ≤ cZ * cL * unitZ D` using `mul_nonneg (mul_nonneg hcZ hcL) hU`. Establish `q3 : 0 ≤ cZ * (unitZ D * ((m : ℝ) / D.k))` using `mul_nonneg hcZ hUm`. Establish `q4 : 0 ≤ cZ * cL * (unitZ D * ((m : ℝ) / D.k))` using `mul_nonneg (mul_nonneg hcZ hcL) hUm`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[e1]`. Unfold `ZiiR at z1`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[e2]`. Unfold `ZiiiR at z2`.

Establish `e3 : cZ * (f : ℝ) * (D.b' + Sc) * (D.k * Real.log (D.k * D.v) + Real.log (D.T u0 u)) = cZ * (f : ℝ) * (D.b' + Sc) * (D.k * Real.log (D.k * D.v)) + cZ * (f : ℝ) * (D.b' + Sc) * Real.log (D.T u0 u)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem z_to_slopes : ZToSlopes := by
  intro U0 W Top _ m f D C cZ cL cU Sc LZ hW hT hZ hC u0 u
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := z_terms D cZ cL cU Sc LZ _ hW (hT u0 u)
  obtain ⟨hcZ, hcL, hcU, ha, hk, hmk, hb', hSc, haT, hL, hLLa, hlk, hlkv, hLZ, hw1, hw2⟩ := hW
  have hk0 : 0 < D.k := by linarith
  have hU : 0 ≤ unitZ D := mul_nonneg (mul_nonneg (nT_nonneg D) ha) (le_trans hL hLLa)
  have hmk' : 0 ≤ (m : ℝ) / D.k := div_nonneg (Nat.cast_nonneg _) hk0.le
  have hUm : 0 ≤ unitZ D * ((m : ℝ) / D.k) := mul_nonneg hU hmk'
  obtain ⟨z1, z2⟩ := hZ u0 u
  have e1 : C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)
      = C.cSlope * unitZ D + C.cSlope * (unitZ D * ((m : ℝ) / D.k)) := by unfold unitZ; ring
  have e2 : C.cSlope * D.nT * D.a * D.La = C.cSlope * unitZ D := by unfold unitZ; ring
  have hC1 := mul_le_mul_of_nonneg_right hC hU
  have hC2 := mul_le_mul_of_nonneg_right hC hUm
  unfold cSlopeZ at hC1 hC2
  have p1 : 0 ≤ cZ * cU * unitZ D := mul_nonneg (mul_nonneg hcZ hcU) hU
  have p2 : 0 ≤ cU * unitZ D := mul_nonneg hcU hU
  have p3 : 0 ≤ cZ * unitZ D := mul_nonneg hcZ hU
  have p4 : 0 ≤ cZ * cL * unitZ D := mul_nonneg (mul_nonneg hcZ hcL) hU
  have q3 : 0 ≤ cZ * (unitZ D * ((m : ℝ) / D.k)) := mul_nonneg hcZ hUm
  have q4 : 0 ≤ cZ * cL * (unitZ D * ((m : ℝ) / D.k)) := mul_nonneg (mul_nonneg hcZ hcL) hUm
  constructor
  · rw [e1]
    unfold ZiiR at z1
    linarith
  · rw [e2]
    unfold ZiiiR at z2
    have e3 : cZ * (f : ℝ) * (D.b' + Sc) * (D.k * Real.log (D.k * D.v) + Real.log (D.T u0 u))
        = cZ * (f : ℝ) * (D.b' + Sc) * (D.k * Real.log (D.k * D.v))
          + cZ * (f : ℝ) * (D.b' + Sc) * Real.log (D.T u0 u) := by ring
    linarith

/- English proof (translation)
Establish `hG0 : 0 < Gam` using `by linarith`. Establish `hp : 0 < Gam ^ (-(2 / y))` using `Real.rpow_pos_of_pos hG0 _`. Establish `hS : 0 < X * Gam ^ (-(2 / y))` using `mul_pos hX hp`. Establish `hT : 0 < T` using `lt_of_lt_of_le hS h1`. Establish `hy1 : 0 < 1 + 1 / y` using `by positivity`.

Establish `e : Real.log (X * Gam ^ (-(2 / y))) = Real.log X - 2 * Real.log Gam / y`. Rewrite using `[Real.log_mul hX.ne' hp.ne', Real.log_rpow hG0]`. Expand and normalize the polynomial expressions, which then agree. Prove the components needed by the constructor for the conclusion. Rewrite using `[← e]`.

Conclude with `Real.log_le_log hS h1`. Establish `h3` using `Real.log_le_log hT h2`. Rewrite `h3` using `[Real.log_mul hS.ne' hy1.ne', e]`. Establish `h4` using `Real.log_le_sub_one_of_pos hy1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma logT_bounds {X Gam y T : ℝ} (hX : 0 < X) (hG : 1 ≤ Gam) (hy : 0 < y)
    (h1 : X * Gam ^ (-(2 / y)) ≤ T) (h2 : T ≤ X * Gam ^ (-(2 / y)) * (1 + 1 / y)) :
    Real.log X - 2 * Real.log Gam / y ≤ Real.log T ∧
    Real.log T ≤ Real.log X - 2 * Real.log Gam / y + 1 / y := by
  have hG0 : 0 < Gam := by linarith
  have hp : 0 < Gam ^ (-(2 / y)) := Real.rpow_pos_of_pos hG0 _
  have hS : 0 < X * Gam ^ (-(2 / y)) := mul_pos hX hp
  have hT : 0 < T := lt_of_lt_of_le hS h1
  have hy1 : 0 < 1 + 1 / y := by positivity
  have e : Real.log (X * Gam ^ (-(2 / y))) = Real.log X - 2 * Real.log Gam / y := by
    rw [Real.log_mul hX.ne' hp.ne', Real.log_rpow hG0]; ring
  constructor
  · rw [← e]; exact Real.log_le_log hS h1
  · have h3 := Real.log_le_log hT h2
    rw [Real.log_mul hS.ne' hy1.ne', e] at h3
    have h4 := Real.log_le_sub_one_of_pos hy1
    linarith

section
variable {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ}

/- English proof (translation)
Take `⟨_, hf, hk, _⟩` from `hW`. Establish `hf1 : (1 : ℝ) ≤ (f : ℝ)` using `by exact_mod_cast hf`. Establish `h1 : 1 ≤ (f : ℝ) * D.k` using `by nlinarith`. Conclude with `⟨by linarith, by rw [div_le_one (by linarith)]; exact h1⟩`.
-/
lemma fk_pos {D : Data U0 W Top m f} {c5 Gam : ℝ} (hW : CountWindows D c5 Gam) :
    0 < (f : ℝ) * D.k ∧ 1 / ((f : ℝ) * D.k) ≤ 1 := by
  obtain ⟨_, hf, hk, _⟩ := hW
  have hf1 : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have h1 : 1 ≤ (f : ℝ) * D.k := by nlinarith
  exact ⟨by linarith, by rw [div_le_one (by linarith)]; exact h1⟩

/- English proof (translation)
Take `⟨hX, h1, h2⟩` from `hLW u0 u`. Establish `hy` using `(fk_pos hW).1`. Take `⟨_, _, _, hG, hlG, _⟩` from `hW`. Rewrite using `[hlG]`. Conclude with `logT_bounds hX hG hy h1 h2`.
-/
lemma logT_of_window {D : Data U0 W Top m f} {c5 Gam : ℝ} {X : ∀ u0, W u0 → ℝ}
    (hW : CountWindows D c5 Gam) (hLW : LevelWindow D Gam X) (u0 : U0) (u : W u0) :
    Real.log (X u0 u) - 2 * D.logGam / ((f : ℝ) * D.k) ≤ Real.log (D.T u0 u) ∧
    Real.log (D.T u0 u) ≤ Real.log (X u0 u) - 2 * D.logGam / ((f : ℝ) * D.k) + 1 / ((f : ℝ) * D.k) := by
  obtain ⟨hX, h1, h2⟩ := hLW u0 u
  have hy := (fk_pos hW).1
  obtain ⟨_, _, _, hG, hlG, _⟩ := hW
  rw [hlG]
  exact logT_bounds hX hG hy h1 h2

end

/- English proof (translation)
Introduce `U0 W Top m f D c5 Gam X hW h5 hLW u0 u`. Take `⟨_, hu⟩` from `logT_of_window hW hLW u0 u`. Take `⟨hy, hy1⟩` from `fk_pos hW`. Take `⟨hc, hf, hk, hG, hlG, hG1, hL, hLLa, hLa, hmL, hlk⟩` from `hW`. Establish `hg : 0 ≤ 2 * D.logGam / ((f : ℝ) * D.k)`.

Rewrite using `[hlG]; exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hG)) hy.le`. Use `(h5 u0 u).2` as an intermediate fact. Establish `e : (c5 + 1) * (m : ℝ) * D.L = c5 * (m : ℝ) * D.L + (m : ℝ) * D.L` using `by ring`. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem proposition_to_log_t_upper : Prop5ToLogTUp := by
  intro U0 W Top m f D c5 Gam X hW h5 hLW u0 u
  obtain ⟨_, hu⟩ := logT_of_window hW hLW u0 u
  obtain ⟨hy, hy1⟩ := fk_pos hW
  obtain ⟨hc, hf, hk, hG, hlG, hG1, hL, hLLa, hLa, hmL, hlk⟩ := hW
  have hg : 0 ≤ 2 * D.logGam / ((f : ℝ) * D.k) := by
    rw [hlG]; exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hG)) hy.le
  have := (h5 u0 u).2
  have e : (c5 + 1) * (m : ℝ) * D.L = c5 * (m : ℝ) * D.L + (m : ℝ) * D.L := by ring
  rw [e]; linarith

/- English proof (translation)
Introduce `U0 W Top m f D C c5 Gam X hW h5 hV hLW hC u0 u`. Establish `hup` using `proposition_to_log_t_upper D c5 Gam X hW h5 hLW`. Take `⟨hl, hu⟩` from `logT_of_window hW hLW u0 u`. Take `⟨hy, hy1⟩` from `fk_pos hW`. Establish `hW'` using `hW`.

Take `⟨hc, hf, hk, hG, hlG, hG1, hL, hLLa, hLa, hmL, hlk⟩` from `hW`. Establish `hk0 : 0 < D.k` using `by linarith`. Establish `hq : 0 ≤ D.L + (m : ℝ) ^ 2 * D.L / D.k` using `add_nonneg hL (div_nonneg (mul_nonneg (sq_nonneg _) hL) hk0.le)`. Rewrite using `[hC]`. Use `⟨?_, hup u0 u, ?_⟩` and prove the remaining obligations.

Use `(h5 u0 u).1` as an intermediate fact. Unfold `mainCount at this`. Establish `e : (c5 + 1) * (D.L + (m : ℝ) ^ 2 * D.L / D.k) = c5 * (D.L + (m : ℝ) ^ 2 * D.L / D.k) + (D.L + (m : ℝ) ^ 2 * D.L / D.k)` using `by ring`. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `u'`. Take `⟨hl', hu'⟩` from `logT_of_window hW' hLW u0 u'`. Establish `hv` using `abs_le.mp (hV u0 u u')`. Establish `e : (c5 + 1) * Real.log D.k = c5 * Real.log D.k + Real.log D.k` using `by ring`. Rewrite using `[e]`.

Conclude with `abs_le.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩`.
-/
theorem proposition_to_count_general : Prop5ToCount := by
  intro U0 W Top m f D C c5 Gam X hW h5 hV hLW hC u0 u
  have hup := proposition_to_log_t_upper D c5 Gam X hW h5 hLW
  obtain ⟨hl, hu⟩ := logT_of_window hW hLW u0 u
  obtain ⟨hy, hy1⟩ := fk_pos hW
  have hW' := hW
  obtain ⟨hc, hf, hk, hG, hlG, hG1, hL, hLLa, hLa, hmL, hlk⟩ := hW
  have hk0 : 0 < D.k := by linarith
  have hq : 0 ≤ D.L + (m : ℝ) ^ 2 * D.L / D.k :=
    add_nonneg hL (div_nonneg (mul_nonneg (sq_nonneg _) hL) hk0.le)
  rw [hC]
  refine ⟨?_, hup u0 u, ?_⟩
  · have := (h5 u0 u).1
    unfold mainCount at this
    have e : (c5 + 1) * (D.L + (m : ℝ) ^ 2 * D.L / D.k)
        = c5 * (D.L + (m : ℝ) ^ 2 * D.L / D.k) + (D.L + (m : ℝ) ^ 2 * D.L / D.k) := by ring
    rw [e]; linarith
  · intro u'
    obtain ⟨hl', hu'⟩ := logT_of_window hW' hLW u0 u'
    have hv := abs_le.mp (hV u0 u u')
    have e : (c5 + 1) * Real.log D.k = c5 * Real.log D.k + Real.log D.k := by ring
    rw [e]
    exact abs_le.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩

/- English proof (translation)
Introduce `U0 W Top m f D C c5 Gam X hW h5 hV hLW hC`. Establish `hCount : D.Count { C with cCount` using `c5 + 1 } := proposition_to_count_general D { C with cCount := c5 + 1 } c5 Gam X hW h5 hV hLW rfl`. Take `⟨hc, hf, hk, hG, hlG, hG1, hL, hLLa, hLa, hmL, hlk⟩` from `hW`. Establish `hk0 : 0 < D.k` using `by linarith`. Establish `hq0 : 0 ≤ (m : ℝ) ^ 2 / D.k` using `div_nonneg (sq_nonneg _) hk0.le`.

Establish `e1 : (m : ℝ) ^ 2 * D.L / D.k = (m : ℝ) ^ 2 / D.k * D.L` using `by ring`. Establish `e2 : (m : ℝ) ^ 2 * D.La / D.k = (m : ℝ) ^ 2 / D.k * D.La` using `by ring`. Establish `e3 : 2 * D.logGam / ((f : ℝ) * D.k) = 2 * (D.logGam / ((f : ℝ) * D.k))` using `by ring`. Establish `hmL' : (m : ℝ) ^ 2 / D.k * D.L ≤ (m : ℝ) ^ 2 / D.k * D.La` using `mul_le_mul_of_nonneg_left hLLa hq0`. Establish `hmLa : 0 ≤ (m : ℝ) ^ 2 / D.k * D.La` using `mul_nonneg hq0 (by linarith)`.

Establish `hq : 0 ≤ D.La + (m : ℝ) ^ 2 / D.k * D.La` using `by linarith`. Establish `hsum : D.L + (m : ℝ) ^ 2 / D.k * D.L ≤ D.La + (m : ℝ) ^ 2 / D.k * D.La` using `by linarith`. Establish `hcs` using `mul_le_mul_of_nonneg_left hsum (by linarith : 0 ≤ c5 + 1)`. Introduce `u0 u`. Take `⟨h1, h2, h3⟩` from `hCount u0 u`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h1' : _ - (c5 + 1) * (D.L + (m : ℝ) ^ 2 * D.L / D.k) - 2 * D.logGam / ((f : ℝ) * D.k) ≤ _` using `h1`. Rewrite `h1'` using `[e1, e3]`. Rewrite using `[e2]`. Use `mul_le_mul_of_nonneg_right hC hq` as an intermediate fact.

Establish `e4 : (c5 + 3) * (D.La + (m : ℝ) ^ 2 / D.k * D.La) = (c5 + 1) * (D.La + (m : ℝ) ^ 2 / D.k * D.La) + 2 * (D.La + (m : ℝ) ^ 2 / D.k * D.La)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2' : _ ≤ (c5 + 1) * (m : ℝ) * D.L` using `h2`. Use `mul_le_mul_of_nonneg_right (by linarith : c5 + 1 ≤ C.cCount) (by linarith : 0 ≤ (m : ℝ) * D.L)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `u'`. Establish `h3' : _ ≤ (c5 + 1) * Real.log D.k` using `h3 u'`. Use `mul_le_mul_of_nonneg_right (by linarith : c5 + 1 ≤ C.cCount) (by linarith : 0 ≤ Real.log D.k)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem proposition_to_count : Prop5ToCount5 := by
  intro U0 W Top m f D C c5 Gam X hW h5 hV hLW hC
  have hCount : D.Count { C with cCount := c5 + 1 } :=
    proposition_to_count_general D { C with cCount := c5 + 1 } c5 Gam X hW h5 hV hLW rfl
  obtain ⟨hc, hf, hk, hG, hlG, hG1, hL, hLLa, hLa, hmL, hlk⟩ := hW
  have hk0 : 0 < D.k := by linarith
  have hq0 : 0 ≤ (m : ℝ) ^ 2 / D.k := div_nonneg (sq_nonneg _) hk0.le
  have e1 : (m : ℝ) ^ 2 * D.L / D.k = (m : ℝ) ^ 2 / D.k * D.L := by ring
  have e2 : (m : ℝ) ^ 2 * D.La / D.k = (m : ℝ) ^ 2 / D.k * D.La := by ring
  have e3 : 2 * D.logGam / ((f : ℝ) * D.k) = 2 * (D.logGam / ((f : ℝ) * D.k)) := by ring
  have hmL' : (m : ℝ) ^ 2 / D.k * D.L ≤ (m : ℝ) ^ 2 / D.k * D.La := mul_le_mul_of_nonneg_left hLLa hq0
  have hmLa : 0 ≤ (m : ℝ) ^ 2 / D.k * D.La := mul_nonneg hq0 (by linarith)
  have hq : 0 ≤ D.La + (m : ℝ) ^ 2 / D.k * D.La := by linarith
  have hsum : D.L + (m : ℝ) ^ 2 / D.k * D.L ≤ D.La + (m : ℝ) ^ 2 / D.k * D.La := by linarith
  have hcs := mul_le_mul_of_nonneg_left hsum (by linarith : 0 ≤ c5 + 1)
  intro u0 u
  obtain ⟨h1, h2, h3⟩ := hCount u0 u
  refine ⟨?_, ?_, ?_⟩
  · have h1' : _ - (c5 + 1) * (D.L + (m : ℝ) ^ 2 * D.L / D.k) - 2 * D.logGam / ((f : ℝ) * D.k) ≤ _ := h1
    rw [e1, e3] at h1'
    rw [e2]
    have := mul_le_mul_of_nonneg_right hC hq
    have e4 : (c5 + 3) * (D.La + (m : ℝ) ^ 2 / D.k * D.La)
        = (c5 + 1) * (D.La + (m : ℝ) ^ 2 / D.k * D.La) + 2 * (D.La + (m : ℝ) ^ 2 / D.k * D.La) := by ring
    linarith
  · have h2' : _ ≤ (c5 + 1) * (m : ℝ) * D.L := h2
    have := mul_le_mul_of_nonneg_right (by linarith : c5 + 1 ≤ C.cCount) (by linarith : 0 ≤ (m : ℝ) * D.L)
    linarith
  · intro u'
    have h3' : _ ≤ (c5 + 1) * Real.log D.k := h3 u'
    have := mul_le_mul_of_nonneg_right (by linarith : c5 + 1 ≤ C.cCount) (by linarith : 0 ≤ Real.log D.k)
    linarith

/- English proof (translation)
Introduce `U0 W Top m f D c5 Gam X hW h5 hLW hw hlg hmk hL1 hcm u0 u`. Take `⟨hl, _⟩` from `logT_of_window hW hLW u0 u`. Take `⟨hc, hf, hk, hG, hlG, hG1, hL, hLLa, hLa, hmL, hlk⟩` from `hW`. Establish `hk0 : 0 < D.k` using `by linarith`. Establish `hm : (0 : ℝ) ≤ (m : ℝ)` using `Nat.cast_nonneg _`.

Establish `h1` using `(h5 u0 u).1`. Establish `hs : 0 ≤ ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ * D.v / π)` using `Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity) (Finset.sum_nonneg (fun ρ _ => Real.log_nonneg (hw u0 j ρ))))`. Establish `hmc : 16 * ((m : ℝ) * D.L) ≤ mainCount D u0`. Unfold `mainCount`. Use `mul_le_mul_of_nonneg_left hlg hm` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hq : (m : ℝ) ^ 2 * D.L / D.k ≤ D.L`. Rewrite using `[div_le_iff₀ hk0]`. Use `mul_le_mul_of_nonneg_right hmk hL` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hq2` using `mul_le_mul_of_nonneg_left hq hc`. Establish `e3 : 2 * D.logGam / ((f : ℝ) * D.k) = 2 * (D.logGam / ((f : ℝ) * D.k))` using `by ring`. Establish `hcl : (2 * c5 + 2) * D.L ≤ 15 * (m : ℝ) * D.L` using `mul_le_mul_of_nonneg_right hcm hL`. Establish `hmL0 : 0 ≤ (m : ℝ) * D.L` using `mul_nonneg hm hL`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem level_lower_of_count : LevelLowerOfCount := by
  intro U0 W Top m f D c5 Gam X hW h5 hLW hw hlg hmk hL1 hcm u0 u
  obtain ⟨hl, _⟩ := logT_of_window hW hLW u0 u
  obtain ⟨hc, hf, hk, hG, hlG, hG1, hL, hLLa, hLa, hmL, hlk⟩ := hW
  have hk0 : 0 < D.k := by linarith
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  have h1 := (h5 u0 u).1
  have hs : 0 ≤ ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ * D.v / π) :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity)
      (Finset.sum_nonneg (fun ρ _ => Real.log_nonneg (hw u0 j ρ))))
  have hmc : 16 * ((m : ℝ) * D.L) ≤ mainCount D u0 := by
    unfold mainCount
    have := mul_le_mul_of_nonneg_left hlg hm
    linarith
  have hq : (m : ℝ) ^ 2 * D.L / D.k ≤ D.L := by
    rw [div_le_iff₀ hk0]
    have := mul_le_mul_of_nonneg_right hmk hL
    linarith
  have hq2 := mul_le_mul_of_nonneg_left hq hc
  have e3 : 2 * D.logGam / ((f : ℝ) * D.k) = 2 * (D.logGam / ((f : ℝ) * D.k)) := by ring
  have hcl : (2 * c5 + 2) * D.L ≤ 15 * (m : ℝ) * D.L := mul_le_mul_of_nonneg_right hcm hL
  have hmL0 : 0 ≤ (m : ℝ) * D.L := mul_nonneg hm hL
  nlinarith

/- English proof (translation)
Introduce `f m b T N hf hm hb hT hN hN2`. Establish `hf1 : (1 : ℝ) ≤ (f : ℝ)` using `by exact_mod_cast hf`. Establish `hb1 : 1 ≤ b` using `by linarith`. Establish `hb0 : 0 < b` using `by linarith`. Establish `hm3 : (3 : ℝ) ≤ (m : ℝ) / 2`.

Establish `: (6 : ℝ) ≤ (m : ℝ)` using `by exact_mod_cast hm`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hb3 : b ^ 3 ≤ T`. Establish `h` using `Real.rpow_le_rpow_of_exponent_le hb1 hm3`. Establish `e : b ^ (3 : ℝ) = b ^ 3`.

Rewrite using `[show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]`. Rewrite `h` using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4f : 4 * (f : ℝ) ≤ T` using `by nlinarith`. Establish `hT2 : 2 < T` using `by linarith`.

Establish `hT0 : 0 < T` using `by linarith`. Establish `hA : 4 * (f : ℝ) / T * b ^ 2 ≤ 1 / 2`. Establish `e : 4 * (f : ℝ) / T * b ^ 2 = 4 * (f : ℝ) * b ^ 2 / T` using `by ring`. Rewrite using `[e, div_le_iff₀ hT0]`. Establish `: 8 * (f : ℝ) * b ^ 2 ≤ b * b ^ 2` using `mul_le_mul_of_nonneg_right hb (sq_nonneg _)`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hB : (f : ℝ) * Real.log (T - 1) / (T - 2) ≤ 1 / 2`. Establish `hy : 0 < T - 1` using `by linarith`. Use `set s := Real.sqrt (T - 1) with hs`. Establish `hs2 : s ^ 2 = T - 1` using `Real.sq_sqrt hy.le`.

Establish `h8 : (8 * (f : ℝ)) ^ 3 ≤ b ^ 3` using `pow_le_pow_left₀ (by positivity) hb 3`. Establish `hs8 : 8 * (f : ℝ) ≤ s`. Apply `Real.le_sqrt_of_sq_le` to reduce the goal to its premises. Use polynomial arithmetic with `[mul_nonneg (sq_nonneg (f : ℝ)) (by linarith : (0 : ℝ) ≤ (f : ℝ) - 1)]`. Establish `hs0 : 0 < s` using `by linarith`.

Establish `hlog : Real.log (T - 1) ≤ 2 * s`. Establish `h1` using `Real.log_le_sub_one_of_pos hs0`. Establish `h2 : Real.log s = Real.log (T - 1) / 2` using `Real.log_sqrt hy.le`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[div_le_iff₀ (by linarith)]`.

Establish `h3 : (f : ℝ) * Real.log (T - 1) ≤ (f : ℝ) * (2 * s)` using `mul_le_mul_of_nonneg_left hlog (by linarith)`. Use the polynomial consequences of the given equalities and inequalities. Use `⟨hT2, h4f, ?_, by linarith⟩` and prove the remaining obligations. Rewrite using `[div_le_iff₀ hT0]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem level_sizes : LevelSizes := by
  intro f m b T N hf hm hb hT hN hN2
  have hf1 : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  have hm3 : (3 : ℝ) ≤ (m : ℝ) / 2 := by
    have : (6 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hb3 : b ^ 3 ≤ T := by
    have h := Real.rpow_le_rpow_of_exponent_le hb1 hm3
    have e : b ^ (3 : ℝ) = b ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [e] at h
    linarith
  have h4f : 4 * (f : ℝ) ≤ T := by nlinarith
  have hT2 : 2 < T := by linarith
  have hT0 : 0 < T := by linarith
  have hA : 4 * (f : ℝ) / T * b ^ 2 ≤ 1 / 2 := by
    have e : 4 * (f : ℝ) / T * b ^ 2 = 4 * (f : ℝ) * b ^ 2 / T := by ring
    rw [e, div_le_iff₀ hT0]
    have : 8 * (f : ℝ) * b ^ 2 ≤ b * b ^ 2 := mul_le_mul_of_nonneg_right hb (sq_nonneg _)
    nlinarith
  have hB : (f : ℝ) * Real.log (T - 1) / (T - 2) ≤ 1 / 2 := by
    have hy : 0 < T - 1 := by linarith
    set s := Real.sqrt (T - 1) with hs
    have hs2 : s ^ 2 = T - 1 := Real.sq_sqrt hy.le
    have h8 : (8 * (f : ℝ)) ^ 3 ≤ b ^ 3 := pow_le_pow_left₀ (by positivity) hb 3
    have hs8 : 8 * (f : ℝ) ≤ s := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [mul_nonneg (sq_nonneg (f : ℝ)) (by linarith : (0 : ℝ) ≤ (f : ℝ) - 1)]
    have hs0 : 0 < s := by linarith
    have hlog : Real.log (T - 1) ≤ 2 * s := by
      have h1 := Real.log_le_sub_one_of_pos hs0
      have h2 : Real.log s = Real.log (T - 1) / 2 := Real.log_sqrt hy.le
      linarith
    rw [div_le_iff₀ (by linarith)]
    have h3 : (f : ℝ) * Real.log (T - 1) ≤ (f : ℝ) * (2 * s) :=
      mul_le_mul_of_nonneg_left hlog (by linarith)
    nlinarith
  refine ⟨hT2, h4f, ?_, by linarith⟩
  rw [div_le_iff₀ hT0]; linarith

/- English proof (translation)
Introduce `mR b T hb hT`. Establish `hp : 0 < b ^ (mR / 2)` using `Real.rpow_pos_of_pos hb _`. Rewrite using `[← Real.log_le_log_iff hp hT, Real.log_rpow hb]`. Apply the tactic sequence `constructor <;> intro h <;> linarith`.
-/
theorem pow_of_log : PowOfLog := by
  intro mR b T hb hT
  have hp : 0 < b ^ (mR / 2) := Real.rpow_pos_of_pos hb _
  rw [← Real.log_le_log_iff hp hT, Real.log_rpow hb]
  constructor <;> intro h <;> linarith

/- English proof (translation)
Establish `hy : 0 < T - 1` using `by linarith`. Establish `h1 : 1 / (T - 1) ≤ 1` using `by rw [div_le_one hy]; linarith`. Establish `h` using `one_add_mul_le_pow (a := -(1 / (T - 1))) (by linarith) f`. Establish `e1 : 1 + (f : ℝ) * -(1 / (T - 1)) = 1 - (f : ℝ) / (T - 1)` using `by ring`. Establish `e2 : 1 + -(1 / (T - 1)) = 1 - 1 / (T - 1)` using `by ring`.

Rewrite `h` using `[e1, e2]`. Conclude with `h`.
-/
lemma bernoulli_level (f : ℕ) {T : ℝ} (hT : 2 ≤ T) :
    1 - (f : ℝ) / (T - 1) ≤ (1 - 1 / (T - 1)) ^ f := by
  have hy : 0 < T - 1 := by linarith
  have h1 : 1 / (T - 1) ≤ 1 := by rw [div_le_one hy]; linarith
  have h := one_add_mul_le_pow (a := -(1 / (T - 1))) (by linarith) f
  have e1 : 1 + (f : ℝ) * -(1 / (T - 1)) = 1 - (f : ℝ) / (T - 1) := by ring
  have e2 : 1 + -(1 / (T - 1)) = 1 - 1 / (T - 1) := by ring
  rw [e1, e2] at h
  exact h

/- English proof (translation)
Introduce `f T hT`. Establish `h` using `bernoulli_level f hT`. Establish `hy : 0 < T - 1` using `by linarith`. Establish `hT0 : 0 < T` using `by linarith`. Establish `hf : (0 : ℝ) ≤ (f : ℝ)` using `Nat.cast_nonneg _`.

Establish `h2 : (f : ℝ) / (T - 1) ≤ 2 * (f : ℝ) / T`. Rewrite using `[div_le_div_iff₀ hy hT0]`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem defect_bound_alt : DefectBound := by
  intro f T hT
  have h := bernoulli_level f hT
  have hy : 0 < T - 1 := by linarith
  have hT0 : 0 < T := by linarith
  have hf : (0 : ℝ) ≤ (f : ℝ) := Nat.cast_nonneg _
  have h2 : (f : ℝ) / (T - 1) ≤ 2 * (f : ℝ) / T := by
    rw [div_le_div_iff₀ hy hT0]; nlinarith
  linarith

/- English proof (translation)
Introduce `U0 W Top _ m f D aM VV Wt bt hW`. Take `⟨hk, hkb, ha, haM, hWt, hbt⟩` from `hW`. Establish `hm : (0 : ℝ) ≤ (m : ℝ)` using `Nat.cast_nonneg _`. Establish `hb' : 0 ≤ D.b'` using `by linarith`. Establish `hak : 0 ≤ D.a / D.k` using `div_nonneg ha hk.le`.

Establish `haMk : aM / D.k ≤ 2 * (D.a / D.k)`. Use `div_le_div_of_nonneg_right haM hk.le` as an intermediate fact. Establish `e : 2 * D.a / D.k = 2 * (D.a / D.k)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcard : ((VV.card : ℕ) : ℝ) ≤ D.nT`.

Unfold `Data.nT`. Conclude with `Finset.card_le_univ VV` after adjusting the coercions. Establish `h1 : ∑ t ∈ VV, ((aM / D.k + 2 * Wt t + D.k) + bt t) ≤ ∑ _t ∈ VV, 7 * (D.a / D.k + D.b')` using `Finset.sum_le_sum (fun t _ => by have := hWt t; have := hbt t; linarith)`. Rewrite `h1` using `[Finset.sum_const, nsmul_eq_mul, Finset.sum_add_distrib]`. Establish `h2 : ((VV.card : ℕ) : ℝ) * (7 * (D.a / D.k + D.b')) ≤ D.nT * (7 * (D.a / D.k + D.b'))` using `mul_le_mul_of_nonneg_right hcard (by linarith)`.

Establish `h3` using `mul_le_mul_of_nonneg_left (le_trans h1 h2) hm`. Unfold `lambdaIndex`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem index_to_lambda : IndexToLengthBound := by
  intro U0 W Top _ m f D aM VV Wt bt hW
  obtain ⟨hk, hkb, ha, haM, hWt, hbt⟩ := hW
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  have hb' : 0 ≤ D.b' := by linarith
  have hak : 0 ≤ D.a / D.k := div_nonneg ha hk.le
  have haMk : aM / D.k ≤ 2 * (D.a / D.k) := by
    have := div_le_div_of_nonneg_right haM hk.le
    have e : 2 * D.a / D.k = 2 * (D.a / D.k) := by ring
    linarith
  have hcard : ((VV.card : ℕ) : ℝ) ≤ D.nT := by
    unfold Data.nT
    exact_mod_cast Finset.card_le_univ VV
  have h1 : ∑ t ∈ VV, ((aM / D.k + 2 * Wt t + D.k) + bt t) ≤ ∑ _t ∈ VV, 7 * (D.a / D.k + D.b') :=
    Finset.sum_le_sum (fun t _ => by have := hWt t; have := hbt t; linarith)
  rw [Finset.sum_const, nsmul_eq_mul, Finset.sum_add_distrib] at h1
  have h2 : ((VV.card : ℕ) : ℝ) * (7 * (D.a / D.k + D.b')) ≤ D.nT * (7 * (D.a / D.k + D.b')) :=
    mul_le_mul_of_nonneg_right hcard (by linarith)
  have h3 := mul_le_mul_of_nonneg_left (le_trans h1 h2) hm
  unfold lambdaIndex
  linarith

/- English proof (translation)
Introduce `U0 W Top _ m f D C cZ cL Sc LZ c5 Gam X hZW hZ hCW h5 hV hLW hC1 hC2`. Conclude with `⟨z_to_slopes D C cZ cL (c5 + 1) Sc LZ hZW (proposition_to_log_t_upper D c5 Gam X hCW h5 hLW) hZ hC1, proposition_to_count D C c5 Gam X hCW h5 hV hLW hC2⟩`.
-/
theorem joint_four_five : SlopeCountJoint := by
  intro U0 W Top _ m f D C cZ cL Sc LZ c5 Gam X hZW hZ hCW h5 hV hLW hC1 hC2
  exact ⟨z_to_slopes D C cZ cL (c5 + 1) Sc LZ hZW (proposition_to_log_t_upper D c5 Gam X hCW h5 hLW) hZ hC1,
    proposition_to_count D C c5 Gam X hCW h5 hV hLW hC2⟩

/- English proof (translation)
Take `⟨x₀, h⟩` from `text_sizes_windows ε E hε`. Use `⟨max x₀ 8, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hx0 : x₀ ≤ x` using `le_trans (le_max_left _ _) hx`. Establish `hx8 : 8 ≤ x` using `le_trans (le_max_right _ _) hx`. Establish `hxp : 0 < x` using `by linarith`.

Establish `hb : 0 < bTx x ε` using `Real.exp_pos _`. Establish `ha : 0 < aTx x ε` using `mul_pos hxp hb`. Establish `hbp : 0 < bpTx x ε` using `div_pos ha (Real.exp_pos _)`. Establish `hl : Real.log (bTx x ε) = x ^ ε` using `Real.log_exp _`. Use `⟨hx8, hl, hb, ha, hbp, fun K hK hKE => ?_⟩` and prove the remaining obligations.

Take `⟨_, _, _, _, k1, _, k2, _, k3⟩` from `h x K K 0 hx0 hK hKE hK hKE (Real.rpow_nonneg hxp.le _)`. Use `⟨k1, k2, ?_⟩` and prove the remaining obligations. Establish `hxK : 0 < x * K` using `mul_pos hxp hK`. Establish `hw : 0 < wppTx x ε K` using `div_pos hbp hxK`. Unfold `XppTx at k3`.

Rewrite `k3` using `[div_le_iff₀ hw]`. Establish `h1 : 1 ≤ wppTx x ε K`. Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`. Use `mul_lt_mul_of_pos_left hlt ha` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Unfold `wppTx at h1`. Rewrite `h1` using `[le_div_iff₀ hxK, one_mul]`. Then use the resulting hypothesis.
-/
lemma text_key (ε E : ℝ) (hε : 0 < ε) : ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    8 ≤ x ∧ Real.log (bTx x ε) = x ^ ε ∧ 0 < bTx x ε ∧ 0 < aTx x ε ∧ 0 < bpTx x ε ∧
    ∀ K : ℝ, 0 < K → K ≤ x ^ E → K ≤ aTx x ε ∧ K * bpTx x ε ≤ aTx x ε ∧ x * K ≤ bpTx x ε := by
  obtain ⟨x₀, h⟩ := text_sizes_windows ε E hε
  refine ⟨max x₀ 8, fun x hx => ?_⟩
  have hx0 : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx8 : 8 ≤ x := le_trans (le_max_right _ _) hx
  have hxp : 0 < x := by linarith
  have hb : 0 < bTx x ε := Real.exp_pos _
  have ha : 0 < aTx x ε := mul_pos hxp hb
  have hbp : 0 < bpTx x ε := div_pos ha (Real.exp_pos _)
  have hl : Real.log (bTx x ε) = x ^ ε := Real.log_exp _
  refine ⟨hx8, hl, hb, ha, hbp, fun K hK hKE => ?_⟩
  obtain ⟨_, _, _, _, k1, _, k2, _, k3⟩ :=
    h x K K 0 hx0 hK hKE hK hKE (Real.rpow_nonneg hxp.le _)
  refine ⟨k1, k2, ?_⟩
  have hxK : 0 < x * K := mul_pos hxp hK
  have hw : 0 < wppTx x ε K := div_pos hbp hxK
  unfold XppTx at k3
  rw [div_le_iff₀ hw] at k3
  have h1 : 1 ≤ wppTx x ε K := by
    by_contra hlt
    rw [not_le] at hlt
    have := mul_lt_mul_of_pos_left hlt ha
    linarith
  unfold wppTx at h1
  rwa [le_div_iff₀ hxK, one_mul] at h1

/- English proof (translation)
Introduce `ε e cT c6 hε he hc6`. Take `⟨x₀, h⟩` from `text_key ε (e + 2) hε`. Use `⟨max x₀ (2 * |cT| / c6 + 1), fun x k nT hx hn0 hn hk hnk => ?_⟩` and prove the remaining obligations. Establish `hx0 : x₀ ≤ x` using `le_trans (le_max_left _ _) hx`. Establish `hx1 : 2 * |cT| / c6 + 1 ≤ x` using `le_trans (le_max_right _ _) hx`.

Take `⟨hx8, _, _, ha, hbp, hK⟩` from `h x hx0`. Establish `hxp : 0 < x` using `by linarith`. Establish `hKp : 0 < x ^ (e + 2)` using `Real.rpow_pos_of_pos hxp _`. Take `⟨_, k2, _⟩` from `hK _ hKp le_rfl`. Establish `hXp : 0 < XpTx x ε` using `Real.exp_pos _`.

Establish `hKX : x ^ (e + 2) ≤ XpTx x ε`. Unfold `bpTx at k2`. Rewrite `k2` using `[← mul_div_assoc, div_le_iff₀ hXp]`. Establish `: x ^ (e + 2) * aTx x ε ≤ XpTx x ε * aTx x ε` using `by linarith`. Conclude with `le_of_mul_le_mul_right this ha`.

Establish `hxe : 0 < x ^ e` using `Real.rpow_pos_of_pos hxp _`. Establish `eK : x ^ (e + 2) = x ^ e * x ^ 2`. Rewrite using `[Real.rpow_add hxp, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]`. Establish `q1 : nT * (x / k) ≤ 1 / x`. Rewrite using `[← mul_div_assoc, div_le_div_iff₀ hk hxp]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `q2 : nT * (x / XpTx x ε) ≤ 1 / x`. Rewrite using `[← mul_div_assoc, div_le_div_iff₀ hXp hxp]`. Establish `: nT * x * x ≤ x ^ e * x ^ 2`. Use `mul_le_mul_of_nonneg_right hn (sq_nonneg x)` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion. Establish `q0 : 0 ≤ nT * (x / k + x / XpTx x ε)` using `mul_nonneg hn0 (add_nonneg (div_nonneg hxp.le hk.le) (div_nonneg hxp.le hXp.le))`. Establish `q3 : nT * (x / k + x / XpTx x ε) ≤ 2 / x`. Establish `: 2 / x = 1 / x + 1 / x` using `by ring`.

Rewrite using `[this, mul_add]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1 : cT * nT * (x / k + x / XpTx x ε) ≤ |cT| * (2 / x)`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : |cT| * (2 / x) < c6`.

Rewrite using `[← mul_div_assoc, div_lt_iff₀ hxp]`. Establish `: 2 * |cT| / c6 < x` using `by linarith`. Rewrite `this` using `[div_lt_iff₀ hc6]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem small_terms_bound₂ : SmallText := by
  intro ε e cT c6 hε he hc6
  obtain ⟨x₀, h⟩ := text_key ε (e + 2) hε
  refine ⟨max x₀ (2 * |cT| / c6 + 1), fun x k nT hx hn0 hn hk hnk => ?_⟩
  have hx0 : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : 2 * |cT| / c6 + 1 ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨hx8, _, _, ha, hbp, hK⟩ := h x hx0
  have hxp : 0 < x := by linarith
  have hKp : 0 < x ^ (e + 2) := Real.rpow_pos_of_pos hxp _
  obtain ⟨_, k2, _⟩ := hK _ hKp le_rfl
  have hXp : 0 < XpTx x ε := Real.exp_pos _
  have hKX : x ^ (e + 2) ≤ XpTx x ε := by
    unfold bpTx at k2
    rw [← mul_div_assoc, div_le_iff₀ hXp] at k2
    have : x ^ (e + 2) * aTx x ε ≤ XpTx x ε * aTx x ε := by linarith
    exact le_of_mul_le_mul_right this ha
  have hxe : 0 < x ^ e := Real.rpow_pos_of_pos hxp _
  have eK : x ^ (e + 2) = x ^ e * x ^ 2 := by
    rw [Real.rpow_add hxp, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have q1 : nT * (x / k) ≤ 1 / x := by
    rw [← mul_div_assoc, div_le_div_iff₀ hk hxp]; nlinarith
  have q2 : nT * (x / XpTx x ε) ≤ 1 / x := by
    rw [← mul_div_assoc, div_le_div_iff₀ hXp hxp]
    have : nT * x * x ≤ x ^ e * x ^ 2 := by
      have := mul_le_mul_of_nonneg_right hn (sq_nonneg x)
      nlinarith
    linarith
  have q0 : 0 ≤ nT * (x / k + x / XpTx x ε) :=
    mul_nonneg hn0 (add_nonneg (div_nonneg hxp.le hk.le) (div_nonneg hxp.le hXp.le))
  have q3 : nT * (x / k + x / XpTx x ε) ≤ 2 / x := by
    have : 2 / x = 1 / x + 1 / x := by ring
    rw [this, mul_add]; linarith
  have h1 : cT * nT * (x / k + x / XpTx x ε) ≤ |cT| * (2 / x) := by
    calc cT * nT * (x / k + x / XpTx x ε) = cT * (nT * (x / k + x / XpTx x ε)) := by ring
      _ ≤ |cT| * (nT * (x / k + x / XpTx x ε)) := mul_le_mul_of_nonneg_right (le_abs_self _) q0
      _ ≤ |cT| * (2 / x) := mul_le_mul_of_nonneg_left q3 (abs_nonneg _)
  have h2 : |cT| * (2 / x) < c6 := by
    rw [← mul_div_assoc, div_lt_iff₀ hxp]
    have : 2 * |cT| / c6 < x := by linarith
    rw [div_lt_iff₀ hc6] at this
    linarith
  linarith

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `ε e hε he`. Take `⟨x₀, h⟩` from `text_key ε (4 * e + 2) hε`. Use `⟨x₀, ?_⟩` and prove the remaining obligations. Introduce `x k fR mR nT N Sc lrd v hx hk1 hk hf1 hf hm1 hm hN1 hN hn1 hSc0 hSc hv hlv hlrd`. Take `⟨hx8, hlb, hb, ha, hbp, hK⟩` from `h x hx`.

Establish `hxp : 0 < x` using `by linarith`. Establish `hx1 : 1 ≤ x` using `by linarith`. Establish `hx2 : 64 ≤ x ^ 2` using `by nlinarith`. Establish `hxx : x ≤ x ^ 2` using `by nlinarith`. Establish `h8x : 8 * x ≤ x ^ 2` using `by nlinarith`.

Use `set y := x ^ e with hy`. Establish `hy1 : 1 ≤ y` using `Real.one_le_rpow hx1 he`. Establish `hE : x ^ (4 * e + 2) = y ^ 4 * x ^ 2`. Rewrite using `[Real.rpow_add hxp, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hy, ← Real.rpow_natCast (x ^ e) 4, ← Real.rpow_mul hxp.le]`. Use `congr 2`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hK` using `[hE]`. Establish `hk0 : 0 < k` using `by linarith`. Establish `hf0 : 0 < fR` using `by linarith`.

Establish `hm0 : 0 < mR` using `by linarith`. Establish `hN0 : 0 < N` using `by linarith`. Establish `hy0 : 0 < y` using `by linarith`. Establish `y2 : y ^ 2 ≤ y ^ 4` using `pow_le_pow_right₀ hy1 (by norm_num)`. Establish `y3 : y ^ 3 ≤ y ^ 4` using `pow_le_pow_right₀ hy1 (by norm_num)`.

Establish `y1 : y ≤ y ^ 4` using `by simpa using pow_le_pow_right₀ hy1 (by norm_num : 1 ≤ 4)`. Establish `y4 : 0 < y ^ 4` using `by positivity`. Establish `big : ∀ {K c : ℝ}, K ≤ c * y ^ 4 → c ≤ x ^ 2 → K ≤ y ^ 4 * x ^ 2`. Introduce `K c h1 h2`. Use `mul_le_mul_of_nonneg_right h2 y4.le` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `p2 : fR * k ≤ y ^ 2`. Establish `: fR * k ≤ y * y` using `mul_le_mul hf hk hk0.le hy0.le`. Combine the linear relations using `[sq y]`. Establish `pm2 : mR * k ≤ y ^ 2`.

Establish `: mR * k ≤ y * y` using `mul_le_mul hm hk hk0.le hy0.le`. Combine the linear relations using `[sq y]`. Establish `pmN : mR * N ≤ y ^ 2`. Establish `: mR * N ≤ y * y` using `mul_le_mul hm hN hN0.le hy0.le`. Combine the linear relations using `[sq y]`.

Establish `p3 : fR * k ^ 2 ≤ y ^ 3`. Establish `: fR * k * k ≤ y ^ 2 * y` using `mul_le_mul p2 hk hk0.le (by positivity)`. Establish `e1 : fR * k ^ 2 = fR * k * k` using `by ring`. Establish `e2 : y ^ 3 = y ^ 2 * y` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `pmNk : mR * N * k ≤ y ^ 3`. Establish `: mR * N * k ≤ y ^ 2 * y` using `mul_le_mul pmN hk hk0.le (by positivity)`. Establish `e2 : y ^ 3 = y ^ 2 * y` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `p4 : fR * (mR * N * k) ≤ y ^ 4`.

Establish `: fR * (mR * N * k) ≤ y * y ^ 3` using `mul_le_mul hf pmNk (by positivity) hy0.le`. Establish `e2 : y ^ 4 = y * y ^ 3` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨A1, _, A3⟩` from `hK k hk0 (big (c := 1) (by linarith) (by linarith))`. Take `⟨_, B2, _⟩` from `hK (2 * (fR * k)) (by positivity) (big (c := 2) (by linarith) (by linarith))`.

Take `⟨C1, _, _⟩` from `hK (fR * k ^ 2) (by positivity) (big (c := 1) (by linarith) (by linarith))`. Take `⟨D1, _, _⟩` from `hK (fR * (mR * N * k)) (by positivity) (big (c := 1) (by linarith) (by linarith))`. Take `⟨_, E2, _⟩` from `hK (mR * k) (by positivity) (big (c := 1) (by linarith) (by linarith))`. Take `⟨F1, _, _⟩` from `hK (mR * N * k) (by positivity) (big (c := 1) (by linarith) (by linarith))`. Take `⟨G1, _, _⟩` from `hK (8 * x * fR) (by positivity) (by`.

Use `mul_le_mul h8x (le_trans hf y1) hf0.le (by positivity)` as an intermediate fact. Use the proof step `linarith)`. Take `⟨H1, _, _⟩` from `hK (x * (mR * N)) (by positivity) (by`. Use `mul_le_mul hxx (le_trans pmN y2) (by positivity) (by positivity)` as an intermediate fact. Use the proof step `linarith)`.

Take `⟨_, I2, _⟩` from `hK (x * mR) (by positivity) (by`. Use `mul_le_mul hxx (le_trans hm y1) hm0.le (by positivity)` as an intermediate fact. Use the proof step `linarith)`. Establish `hax : aTx x ε = x * bTx x ε` using `rfl`. Establish `hna : aTx x ε ≤ nT * aTx x ε` using `le_mul_of_one_le_left ha.le hn1`.

Establish `hak : 0 < aTx x ε / k` using `div_pos ha hk0`. Establish `hlk : Real.log k ≤ Real.log (aTx x ε)` using `Real.log_le_log hk0 A1`. Use `⟨by linarith, ?_, ?_, ?_, ?_, ?_, by linarith, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Real.log_mul hk0.ne' hv.ne']`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[Real.log_mul ha.ne' hv.ne']`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: Real.log (bTx x ε) ≤ Real.log (aTx x ε)` using `Real.log_le_log hb (by rw [hax]; exact le_mul_of_one_le_left hb.le hx1)`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hlb]`.

Conclude with `Real.one_le_rpow hx1 hε.le`. Establish `: fR * k * (bpTx x ε + Sc) ≤ fR * k * (bpTx x ε + bpTx x ε)` using `mul_le_mul_of_nonneg_left (by linarith) (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `le_trans (le_mul_of_one_le_left hk0.le hx1) A3`. Establish `: fR * mR * N ≤ aTx x ε / k` using `by rw [le_div_iff₀ hk0]; linarith`.

Conclude with `le_trans this (le_mul_of_one_le_left hak.le hn1)`. Rewrite using `[le_div_iff₀ hk0]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[le_div_iff₀ hk0]`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite `G1` using `[hax]`. Establish `: x * (8 * fR) ≤ x * bTx x ε` using `by linarith`. Conclude with `le_of_mul_le_mul_left this hxp`. Rewrite `H1` using `[hax]`. Conclude with `le_of_mul_le_mul_left H1 hxp`.

Rewrite `I2` using `[hax]`. Establish `: x * (mR * bpTx x ε) ≤ x * bTx x ε` using `by linarith`. Conclude with `le_of_mul_le_mul_left this hxp`.
-/
theorem analytic_bounds_eventual : ExponentialPowerWindows := by
  intro ε e hε he
  obtain ⟨x₀, h⟩ := text_key ε (4 * e + 2) hε
  refine ⟨x₀, ?_⟩
  intro x k fR mR nT N Sc lrd v hx hk1 hk hf1 hf hm1 hm hN1 hN hn1 hSc0 hSc hv hlv hlrd
  obtain ⟨hx8, hlb, hb, ha, hbp, hK⟩ := h x hx
  have hxp : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hx2 : 64 ≤ x ^ 2 := by nlinarith
  have hxx : x ≤ x ^ 2 := by nlinarith
  have h8x : 8 * x ≤ x ^ 2 := by nlinarith
  set y := x ^ e with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow hx1 he
  have hE : x ^ (4 * e + 2) = y ^ 4 * x ^ 2 := by
    rw [Real.rpow_add hxp, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hy,
      ← Real.rpow_natCast (x ^ e) 4, ← Real.rpow_mul hxp.le]
    congr 2
    push_cast; ring
  rw [hE] at hK
  have hk0 : 0 < k := by linarith
  have hf0 : 0 < fR := by linarith
  have hm0 : 0 < mR := by linarith
  have hN0 : 0 < N := by linarith
  have hy0 : 0 < y := by linarith
  have y2 : y ^ 2 ≤ y ^ 4 := pow_le_pow_right₀ hy1 (by norm_num)
  have y3 : y ^ 3 ≤ y ^ 4 := pow_le_pow_right₀ hy1 (by norm_num)
  have y1 : y ≤ y ^ 4 := by simpa using pow_le_pow_right₀ hy1 (by norm_num : 1 ≤ 4)
  have y4 : 0 < y ^ 4 := by positivity
  have big : ∀ {K c : ℝ}, K ≤ c * y ^ 4 → c ≤ x ^ 2 → K ≤ y ^ 4 * x ^ 2 := by
    intro K c h1 h2
    have := mul_le_mul_of_nonneg_right h2 y4.le
    linarith
  have p2 : fR * k ≤ y ^ 2 := by
    have : fR * k ≤ y * y := mul_le_mul hf hk hk0.le hy0.le
    linarith [sq y]
  have pm2 : mR * k ≤ y ^ 2 := by
    have : mR * k ≤ y * y := mul_le_mul hm hk hk0.le hy0.le
    linarith [sq y]
  have pmN : mR * N ≤ y ^ 2 := by
    have : mR * N ≤ y * y := mul_le_mul hm hN hN0.le hy0.le
    linarith [sq y]
  have p3 : fR * k ^ 2 ≤ y ^ 3 := by
    have : fR * k * k ≤ y ^ 2 * y := mul_le_mul p2 hk hk0.le (by positivity)
    have e1 : fR * k ^ 2 = fR * k * k := by ring
    have e2 : y ^ 3 = y ^ 2 * y := by ring
    linarith
  have pmNk : mR * N * k ≤ y ^ 3 := by
    have : mR * N * k ≤ y ^ 2 * y := mul_le_mul pmN hk hk0.le (by positivity)
    have e2 : y ^ 3 = y ^ 2 * y := by ring
    linarith
  have p4 : fR * (mR * N * k) ≤ y ^ 4 := by
    have : fR * (mR * N * k) ≤ y * y ^ 3 := mul_le_mul hf pmNk (by positivity) hy0.le
    have e2 : y ^ 4 = y * y ^ 3 := by ring
    linarith
  obtain ⟨A1, _, A3⟩ := hK k hk0 (big (c := 1) (by linarith) (by linarith))
  obtain ⟨_, B2, _⟩ := hK (2 * (fR * k)) (by positivity) (big (c := 2) (by linarith) (by linarith))
  obtain ⟨C1, _, _⟩ := hK (fR * k ^ 2) (by positivity) (big (c := 1) (by linarith) (by linarith))
  obtain ⟨D1, _, _⟩ := hK (fR * (mR * N * k)) (by positivity) (big (c := 1) (by linarith) (by linarith))
  obtain ⟨_, E2, _⟩ := hK (mR * k) (by positivity) (big (c := 1) (by linarith) (by linarith))
  obtain ⟨F1, _, _⟩ := hK (mR * N * k) (by positivity) (big (c := 1) (by linarith) (by linarith))
  obtain ⟨G1, _, _⟩ := hK (8 * x * fR) (by positivity) (by
    have := mul_le_mul h8x (le_trans hf y1) hf0.le (by positivity)
    linarith)
  obtain ⟨H1, _, _⟩ := hK (x * (mR * N)) (by positivity) (by
    have := mul_le_mul hxx (le_trans pmN y2) (by positivity) (by positivity)
    linarith)
  obtain ⟨_, I2, _⟩ := hK (x * mR) (by positivity) (by
    have := mul_le_mul hxx (le_trans hm y1) hm0.le (by positivity)
    linarith)
  have hax : aTx x ε = x * bTx x ε := rfl
  have hna : aTx x ε ≤ nT * aTx x ε := le_mul_of_one_le_left ha.le hn1
  have hak : 0 < aTx x ε / k := div_pos ha hk0
  have hlk : Real.log k ≤ Real.log (aTx x ε) := Real.log_le_log hk0 A1
  refine ⟨by linarith, ?_, ?_, ?_, ?_, ?_, by linarith, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Real.log_mul hk0.ne' hv.ne']; linarith
  · rw [Real.log_mul ha.ne' hv.ne']; linarith
  · have : Real.log (bTx x ε) ≤ Real.log (aTx x ε) := Real.log_le_log hb (by rw [hax]; exact le_mul_of_one_le_left hb.le hx1)
    linarith
  · rw [hlb]; exact Real.one_le_rpow hx1 hε.le
  · have : fR * k * (bpTx x ε + Sc) ≤ fR * k * (bpTx x ε + bpTx x ε) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  · exact le_trans (le_mul_of_one_le_left hk0.le hx1) A3
  · have : fR * mR * N ≤ aTx x ε / k := by rw [le_div_iff₀ hk0]; linarith
    exact le_trans this (le_mul_of_one_le_left hak.le hn1)
  · rw [le_div_iff₀ hk0]; linarith
  · rw [le_div_iff₀ hk0]; linarith
  · rw [hax] at G1
    have : x * (8 * fR) ≤ x * bTx x ε := by linarith
    exact le_of_mul_le_mul_left this hxp
  · rw [hax] at H1
    exact le_of_mul_le_mul_left H1 hxp
  · rw [hax] at I2
    have : x * (mR * bpTx x ε) ≤ x * bTx x ε := by linarith
    exact le_of_mul_le_mul_left this hxp

/- English proof (translation)
Introduce `U0 W Top m f D bN hW u0`. Take `⟨hf, hm1, hmk, hmx, hL, hv, hl0, hl1, hl2, hlg, hb⟩` from `hW`. Establish `hf0 : (0 : ℝ) < (f : ℝ)` using `by exact_mod_cast hf`. Establish `hm1' : (1 : ℝ) ≤ (m : ℝ)` using `by exact_mod_cast hm1`. Establish `hk0 : 0 < D.k` using `by linarith`.

Establish `hvp : 0 < D.v / π` using `div_pos hv Real.pi_pos`. Establish `h1 : ∀ j ρ, Real.log (D.w u0 j ρ * D.v / π) = Real.log (D.w u0 j ρ) + Real.log (D.v / π)`. Introduce `j ρ`. Rewrite using `[mul_div_assoc, Real.log_mul (hb u0 j ρ).2.1.ne' hvp.ne']`. Establish `h2 : (∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ * D.v / π)) = (1 / (f : ℝ)) * (∑ ρ : Fin f, ∑ j : Fin m, Real.log (D.w u0 j ρ)) + (m : ℝ) * Real.log (D.v / π)`.

Repeatedly rewrite using `[h1]`. Rewrite using `[← Finset.mul_sum, Finset.sum_comm]`. Simplify using `only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Establish `h3 : (∑ ρ : Fin f, ∑ j : Fin m, (Real.log (D.w u0 j ρ) - Real.log (bN u0 j ρ))) = (∑ ρ : Fin f, ∑ j : Fin m, Real.log (D.w u0 j ρ)) - ∑ ρ : Fin f, ∑ j : Fin m, Real.log (bN u0 j ρ)`.

Simplify using `only [Finset.sum_sub_distrib]`. Unfold `mainCount exactMain`. Rewrite using `[h2, h3]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exact_coefficient_difference : ExactCoeffDiff := by
  intro U0 W Top m f D bN hW u0
  obtain ⟨hf, hm1, hmk, hmx, hL, hv, hl0, hl1, hl2, hlg, hb⟩ := hW
  have hf0 : (0 : ℝ) < (f : ℝ) := by exact_mod_cast hf
  have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hk0 : 0 < D.k := by linarith
  have hvp : 0 < D.v / π := div_pos hv Real.pi_pos
  have h1 : ∀ j ρ, Real.log (D.w u0 j ρ * D.v / π) = Real.log (D.w u0 j ρ) + Real.log (D.v / π) := by
    intro j ρ
    rw [mul_div_assoc, Real.log_mul (hb u0 j ρ).2.1.ne' hvp.ne']
  have h2 : (∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ * D.v / π))
      = (1 / (f : ℝ)) * (∑ ρ : Fin f, ∑ j : Fin m, Real.log (D.w u0 j ρ)) + (m : ℝ) * Real.log (D.v / π) := by
    simp_rw [h1]
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  have h3 : (∑ ρ : Fin f, ∑ j : Fin m, (Real.log (D.w u0 j ρ) - Real.log (bN u0 j ρ)))
      = (∑ ρ : Fin f, ∑ j : Fin m, Real.log (D.w u0 j ρ))
        - ∑ ρ : Fin f, ∑ j : Fin m, Real.log (bN u0 j ρ) := by
    simp only [Finset.sum_sub_distrib]
  unfold mainCount exactMain
  rw [h2, h3]
  field_simp
  ring

/- English proof (translation)
Introduce `U0 W Top m f D bN hW u0`. Establish `hd` using `exact_coefficient_difference D bN hW u0`. Take `⟨hf, hm1, hmk, hmx, hL, hv, hl0, hl1, hl2, hlg, hb⟩` from `hW`. Establish `hf0 : (0 : ℝ) < (f : ℝ)` using `by exact_mod_cast hf`. Establish `hm1' : (1 : ℝ) ≤ (m : ℝ)` using `by exact_mod_cast hm1`.

Establish `hk0 : 0 < D.k` using `by linarith`. Establish `hx0 : 0 < D.x` using `by linarith`. Establish `hq0 : 0 ≤ (m : ℝ) * ((m : ℝ) - 1) / (2 * D.k)` using `div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)`. Establish `hr0 : 0 ≤ ((m : ℝ) - 1) / (2 * D.k)` using `div_nonneg (by linarith) (by linarith)`. Establish `hr1 : ((m : ℝ) - 1) / (2 * D.k) ≤ 1 / 2`.

Rewrite using `[div_le_iff₀ (by linarith)]; linarith`. Establish `t1 : (1 - (m : ℝ) * ((m : ℝ) - 1) / (2 * D.k)) * Real.log (D.v / π) ≤ D.L`. Use `mul_nonneg hq0 hl0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `t2 : (((m : ℝ) - 1) / (2 * D.k)) * Real.log (2 * D.v) ≤ 1 / 2 * D.L`.

Combine the equalities or inequalities in the displayed calculation. Establish `t3 : 0 ≤ ((m : ℝ) * ((m : ℝ) - 1) / (2 * D.k)) * D.lg` using `mul_nonneg hq0 hlg`. Establish `t4 : (1 / (f : ℝ)) * ∑ ρ : Fin f, ∑ j : Fin m, (Real.log (D.w u0 j ρ) - Real.log (bN u0 j ρ)) ≤ 1`. Establish `hterm : ∀ (ρ : Fin f) (j : Fin m), Real.log (D.w u0 j ρ) - Real.log (bN u0 j ρ) ≤ 1 / D.x`. Introduce `ρ j`.

Take `⟨b0, w0, wb, _⟩` from `hb u0 j ρ`. Establish `h1x : 0 < 1 + 1 / D.x` using `by positivity`. Use `Real.log_le_log w0 wb` as an intermediate fact. Rewrite `this` using `[Real.log_mul b0.ne' h1x.ne']`. Use `Real.log_le_sub_one_of_pos h1x` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hs : ∑ ρ : Fin f, ∑ j : Fin m, (Real.log (D.w u0 j ρ) - Real.log (bN u0 j ρ)) ≤ ∑ _ρ : Fin f, ∑ _j : Fin m, 1 / D.x` using `Finset.sum_le_sum (fun ρ _ => Finset.sum_le_sum (fun j _ => hterm ρ j))`. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs`. Establish `h5` using `mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 1 / (f : ℝ))`. Establish `e : 1 / (f : ℝ) * ((f : ℝ) * ((m : ℝ) * (1 / D.x))) = (m : ℝ) / D.x` using `by field_simp`.

Rewrite `h5` using `[e]`. Establish `: (m : ℝ) / D.x ≤ 1` using `by rw [div_le_one hx0]; exact hmx`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `t5 : (1 / D.k) * ((1 / (f : ℝ)) * ∑ ρ : Fin f, ∑ j : Fin m, Real.log (bN u0 j ρ)) ≤ 2 * D.L`. Establish `hs : ∑ ρ : Fin f, ∑ j : Fin m, Real.log (bN u0 j ρ) ≤ ∑ _ρ : Fin f, ∑ _j : Fin m, 2 * D.L` using `Finset.sum_le_sum (fun ρ _ => Finset.sum_le_sum (fun j _ => (hb u0 j ρ).2.2.2))`.

Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs`. Establish `h5` using `mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 1 / (f : ℝ))`. Establish `h6` using `mul_le_mul_of_nonneg_left h5 (by positivity : 0 ≤ 1 / D.k)`. Establish `e : 1 / D.k * (1 / (f : ℝ) * ((f : ℝ) * ((m : ℝ) * (2 * D.L)))) = (m : ℝ) / D.k * (2 * D.L)`. Clear the denominators using the available nonvanishing facts.

Rewrite `h6` using `[e]`. Establish `h7 : (m : ℝ) / D.k ≤ 1` using `by rw [div_le_one hk0]; exact hmk`. Establish `h8` using `mul_le_mul_of_nonneg_right h7 (by linarith : 0 ≤ 2 * D.L)`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exact_coefficient_price : ExactCoeffPrice := by
  intro U0 W Top m f D bN hW u0
  have hd := exact_coefficient_difference D bN hW u0
  obtain ⟨hf, hm1, hmk, hmx, hL, hv, hl0, hl1, hl2, hlg, hb⟩ := hW
  have hf0 : (0 : ℝ) < (f : ℝ) := by exact_mod_cast hf
  have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hk0 : 0 < D.k := by linarith
  have hx0 : 0 < D.x := by linarith
  have hq0 : 0 ≤ (m : ℝ) * ((m : ℝ) - 1) / (2 * D.k) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hr0 : 0 ≤ ((m : ℝ) - 1) / (2 * D.k) := div_nonneg (by linarith) (by linarith)
  have hr1 : ((m : ℝ) - 1) / (2 * D.k) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have t1 : (1 - (m : ℝ) * ((m : ℝ) - 1) / (2 * D.k)) * Real.log (D.v / π) ≤ D.L := by
    have := mul_nonneg hq0 hl0
    linarith
  have t2 : (((m : ℝ) - 1) / (2 * D.k)) * Real.log (2 * D.v) ≤ 1 / 2 * D.L := by
    calc (((m : ℝ) - 1) / (2 * D.k)) * Real.log (2 * D.v) ≤ (((m : ℝ) - 1) / (2 * D.k)) * D.L :=
          mul_le_mul_of_nonneg_left hl2 hr0
      _ ≤ 1 / 2 * D.L := mul_le_mul_of_nonneg_right hr1 (by linarith)
  have t3 : 0 ≤ ((m : ℝ) * ((m : ℝ) - 1) / (2 * D.k)) * D.lg := mul_nonneg hq0 hlg
  have t4 : (1 / (f : ℝ)) * ∑ ρ : Fin f, ∑ j : Fin m, (Real.log (D.w u0 j ρ) - Real.log (bN u0 j ρ)) ≤ 1 := by
    have hterm : ∀ (ρ : Fin f) (j : Fin m), Real.log (D.w u0 j ρ) - Real.log (bN u0 j ρ) ≤ 1 / D.x := by
      intro ρ j
      obtain ⟨b0, w0, wb, _⟩ := hb u0 j ρ
      have h1x : 0 < 1 + 1 / D.x := by positivity
      have := Real.log_le_log w0 wb
      rw [Real.log_mul b0.ne' h1x.ne'] at this
      have := Real.log_le_sub_one_of_pos h1x
      linarith
    have hs : ∑ ρ : Fin f, ∑ j : Fin m, (Real.log (D.w u0 j ρ) - Real.log (bN u0 j ρ))
        ≤ ∑ _ρ : Fin f, ∑ _j : Fin m, 1 / D.x :=
      Finset.sum_le_sum (fun ρ _ => Finset.sum_le_sum (fun j _ => hterm ρ j))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    have h5 := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 1 / (f : ℝ))
    have e : 1 / (f : ℝ) * ((f : ℝ) * ((m : ℝ) * (1 / D.x))) = (m : ℝ) / D.x := by field_simp
    rw [e] at h5
    have : (m : ℝ) / D.x ≤ 1 := by rw [div_le_one hx0]; exact hmx
    linarith
  have t5 : (1 / D.k) * ((1 / (f : ℝ)) * ∑ ρ : Fin f, ∑ j : Fin m, Real.log (bN u0 j ρ)) ≤ 2 * D.L := by
    have hs : ∑ ρ : Fin f, ∑ j : Fin m, Real.log (bN u0 j ρ) ≤ ∑ _ρ : Fin f, ∑ _j : Fin m, 2 * D.L :=
      Finset.sum_le_sum (fun ρ _ => Finset.sum_le_sum (fun j _ => (hb u0 j ρ).2.2.2))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    have h5 := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 1 / (f : ℝ))
    have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : 0 ≤ 1 / D.k)
    have e : 1 / D.k * (1 / (f : ℝ) * ((f : ℝ) * ((m : ℝ) * (2 * D.L)))) = (m : ℝ) / D.k * (2 * D.L) := by
      field_simp
    rw [e] at h6
    have h7 : (m : ℝ) / D.k ≤ 1 := by rw [div_le_one hk0]; exact hmk
    have h8 := mul_le_mul_of_nonneg_right h7 (by linarith : 0 ≤ 2 * D.L)
    linarith
  linarith

/- English proof (translation)
Introduce `U0 W Top m f D cE c5 X bN hW hE hU hc5 hc u0 u`. Establish `hp` using `exact_coefficient_price D bN hW u0`. Take `⟨hf, hm1, hmk, hmx, hL, hv, hl0, hl1, hl2, hlg, hb⟩` from `hW`. Establish `hm1' : (1 : ℝ) ≤ (m : ℝ)` using `by exact_mod_cast hm1`. Establish `hk0 : 0 < D.k` using `by linarith`.

Use `⟨?_, hU u0 u⟩` and prove the remaining obligations. Establish `h1` using `hE u0 u`. Establish `hq : 0 ≤ (m : ℝ) ^ 2 * D.L / D.k` using `div_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) hk0.le`. Establish `h2 : (cE + 6) * D.L ≤ c5 * D.L` using `mul_le_mul_of_nonneg_right hc (by linarith)`. Establish `h3` using `mul_nonneg hc5 hq`.

Establish `e : c5 * (D.L + (m : ℝ) ^ 2 * D.L / D.k) = c5 * D.L + c5 * ((m : ℝ) ^ 2 * D.L / D.k)` using `by ring`. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exact_coefficient_to_proposition : ExactCoeffToProp5 := by
  intro U0 W Top m f D cE c5 X bN hW hE hU hc5 hc u0 u
  have hp := exact_coefficient_price D bN hW u0
  obtain ⟨hf, hm1, hmk, hmx, hL, hv, hl0, hl1, hl2, hlg, hb⟩ := hW
  have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hk0 : 0 < D.k := by linarith
  refine ⟨?_, hU u0 u⟩
  have h1 := hE u0 u
  have hq : 0 ≤ (m : ℝ) ^ 2 * D.L / D.k := div_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) hk0.le
  have h2 : (cE + 6) * D.L ≤ c5 * D.L := mul_le_mul_of_nonneg_right hc (by linarith)
  have h3 := mul_nonneg hc5 hq
  have e : c5 * (D.L + (m : ℝ) ^ 2 * D.L / D.k) = c5 * D.L + c5 * ((m : ℝ) ^ 2 * D.L / D.k) := by ring
  rw [e]; linarith

namespace Model

noncomputable def gv : ℝ := Real.exp 1 ^ (-(2 / (((2 : ℕ) : ℝ) * Real.exp 2)))

noncomputable def Xv : ∀ _ : Unit, Fin 2 → ℝ := fun _ u => Real.exp (13 + ((u : ℕ) : ℝ))

noncomputable def D0 : Data Unit (fun _ => Fin 2) Unit 6 2 where
  x := 6
  ε := 1
  a := Real.exp 40
  b := Real.exp 4
  b' := Real.exp 2
  k := Real.exp 2
  L := 4
  La := 100
  B0 := 2 * 6 * Real.exp 4 * 4
  Nc := 0
  gam := 0
  LpL := 0
  v := π
  lg := 0
  logGam := 1
  aT := fun _ => Real.exp 40
  w := fun _ _ _ => 1
  d := fun _ _ => 1
  T := fun _ u => Xv () u * gv
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
  ASK := fun _ => 0
  IO := fun _ => 0
  HH := fun _ => 0
  del := fun _ => 0
  η := fun _ => 0
  e := fun _ => 0
  delBar := 0
  etaBar := 0
  eBar := 0

noncomputable def D1 : Data Unit (fun _ => Fin 2) Unit 6 2 :=
  { D0 with
    muM := fun u0 u => ZiiR D0 1 1 1 (Real.log (D0.T u0 u))
    muMaxM := fun u0 u => ZiiiR D0 1 1 1 (Real.log (D0.T u0 u)) }

/- English proof (translation)
Establish `h` using `Real.exp_one_gt_d9`. Establish `e : Real.exp 2 = Real.exp 1 * Real.exp 1` using `by rw [← Real.exp_add]; norm_num`. Rewrite using `[e]`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma h6 : (6 : ℝ) ≤ Real.exp 2 := by
  have h := Real.exp_one_gt_d9
  have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [e]; nlinarith

/- English proof (translation)
Rewrite using `[← Real.exp_add, ← Real.exp_add]`. Evaluate the numerical expressions.
-/
lemma exp_forty_eq : Real.exp 40 = Real.exp 2 * Real.exp 2 * Real.exp 36 := by
  rw [← Real.exp_add, ← Real.exp_add]; norm_num

/- English proof (translation)
Rewrite using `[exp_forty_eq]`. Clear the denominators using the available nonvanishing facts.
-/
lemma hak : Real.exp 40 / Real.exp 2 = Real.exp 2 * Real.exp 36 := by
  rw [exp_forty_eq]; field_simp

end Model

end Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
