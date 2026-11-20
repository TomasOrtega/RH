import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelDegreeRatioLowerBoundRearrangedStatement

namespace GlobalTheory.CovHSNum

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `T D PP kap b z ρ n Λ β ΛD ΛT J δ h d deg degM c hD1 hDT hPP hb hlogb hTPP hz hρ hz2 hzk hkap hn hΛ hβ hΛD hΛT hδ hd hlogn hlogβ hlogδ hlogΛ hlogΛD hlogΛT hJ hcmp hclaim hc hdeg`. Establish `hT8 : (8:ℝ) ≤ T` using `by exact_mod_cast (by omega : 8 ≤ T)`. Establish `hD1r : (1:ℝ) ≤ D` using `by exact_mod_cast hD1`. Establish `hDTr : (D:ℝ) + 1 ≤ T` using `by exact_mod_cast (by omega : D + 1 ≤ T)`. Establish `hTpos : (0:ℝ) < T` using `by linarith`.

Establish `hT0 : (T:ℝ) ≠ 0` using `hTpos.ne'`. Establish `hs0 : 0 ≤ Real.sqrt b` using `Real.sqrt_nonneg b`. Establish `hs2 : Real.sqrt b ^ 2 = b` using `Real.sq_sqrt (by linarith)`. Establish `hs1 : 1 ≤ Real.sqrt b`. Use `Real.sqrt_le_sqrt (show (1:ℝ) ≤ b from hb)` as an intermediate fact.

Rewrite `this` using `[Real.sqrt_one]`. Then use the resulting hypothesis. Establish `hsb : Real.sqrt b ≤ b` using `by nlinarith [mul_le_mul_of_nonneg_left hs1 hs0]`. Establish `hTPPb : (T:ℝ) * PP ≤ b` using `le_trans hTPP hsb`. Establish `hTPP0 : 0 ≤ (T:ℝ) * PP` using `by positivity`. Establish `hTPP2 : ((T:ℝ) * PP) ^ 2 ≤ b`.

Combine the equalities or inequalities in the displayed calculation. Establish `hTs : (T:ℝ) ≤ Real.sqrt b` using `le_trans (by nlinarith) hTPP`. Establish `hlogT : Real.log T ≤ PP / 2`. Use `Real.log_le_log hTpos hTs` as an intermediate fact. Rewrite `this` using `[Real.log_sqrt (by linarith)]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlogD : Real.log D ≤ Real.log T` using `Real.log_le_log (by linarith) (by linarith)`. Establish `hlogΛ0 : 0 ≤ Real.log Λ` using `Real.log_nonneg hΛ`. Establish `hlogβ0 : 0 ≤ Real.log β` using `Real.log_nonneg hβ`. Establish `hlogn0 : 0 ≤ Real.log n` using `Real.log_nonneg hn`.

Establish `hlog1 : Real.log (1 + Real.log Λ) ≤ Real.log Λ`. Use `Real.log_le_sub_one_of_pos (show 0 < 1 + Real.log Λ by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hprod : Real.log (n * D * δ * (1 + Real.log Λ)) = Real.log n + Real.log D + Real.log δ + Real.log (1 + Real.log Λ)`. Establish `h1 : (0:ℝ) < n` using `by linarith`.

Establish `h2 : (0:ℝ) < D` using `by linarith`. Establish `h3 : (0:ℝ) < δ` using `by linarith`. Establish `h4 : (0:ℝ) < 1 + Real.log Λ` using `by linarith`. Rewrite using `[Real.log_mul (mul_pos (mul_pos h1 h2) h3).ne' h4.ne', Real.log_mul (mul_pos h1 h2).ne' h3.ne', Real.log_mul h1.ne' h2.ne']`. Establish `hD2T0 : 0 ≤ (D:ℝ) ^ 2 / T` using `by positivity`.

Establish `hDρ : 0 ≤ (D:ℝ) * ρ` using `mul_nonneg (by positivity) hρ`. Establish `hz0 : 0 ≤ z` using `by rw [hz]; linarith`. Establish `hD2z : (D:ℝ) ^ 2 ≤ z * T / 7`. Establish `e : z * T / 7 = (D:ℝ) ^ 2 + D * ρ * T` using `by rw [hz]; field_simp`. Rewrite using `[e]`.

Use `mul_nonneg hDρ hTpos.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hD2T : (D:ℝ) ^ 2 ≤ T / 14` using `by nlinarith [mul_le_mul_of_nonneg_right hz2 hTpos.le]`. Establish `hq0 : 0 ≤ kap / T` using `div_nonneg hkap hTpos.le`. Take `⟨q, hq⟩ : ∃ q : ℝ, kap / T = q` from `⟨_, rfl⟩`.

Establish `hkq : kap = q * T` using `by rw [← hq]; field_simp`. Rewrite `hlogΛ`, `hJ`, `hq0` using `[hq]`. Rewrite `hzk`, `hlogΛD`, `hlogΛT` using `[hkq]`. Use `clear hq hkq hkap`. Establish `hl0 : Real.log Λ + 26 * Real.log (n * D * δ * (1 + Real.log Λ)) ≤ 27 * (PP * (q + 1)) + 65 * PP`.

Rewrite using `[hprod]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `key` using `GlobalTheory.T.hilbertSamuel_degree_ratio_lower_bound_rearranged T D n Λ β ΛD ΛT J δ h d deg z (27 * (PP * (q + 1)) + 65 * PP) (by omega) hD1 hn hΛ hβ hΛD hΛT hδ hd hz0 hz2 hcmp hl0 hclaim`. Establish `hPPq : 0 ≤ PP * q` using `mul_nonneg (by linarith) hq0`. Establish `F1 : (D:ℝ) ^ 2 * (PP * q) ≤ b / 7`.

Combine the linear relations using `[mul_le_mul_of_nonneg_right hD2z hPPq]`. Establish `F2 : (D:ℝ) ^ 2 * PP ≤ b / 14`. Combine the linear relations using `[mul_le_mul_of_nonneg_right hD2T (show (0:ℝ) ≤ PP by linarith)]`. Establish `hDD2 : (D:ℝ) ≤ (D:ℝ) ^ 2` using `by nlinarith`. Establish `hDPPq : (D:ℝ) * (PP * q) ≤ b / 7`.

Combine the linear relations using `[mul_le_mul_of_nonneg_right hDD2 hPPq]`. Establish `hDPP : (D:ℝ) * PP ≤ b`. Combine the linear relations using `[mul_le_mul_of_nonneg_right (show (D:ℝ) ≤ T by linarith) (show (0:ℝ) ≤ PP by linarith)]`. Establish `t1 : J ≤ 9 * b` using `by linarith`. Establish `hDlogT : (D:ℝ) ^ 2 * Real.log T ≤ (D:ℝ) ^ 2 * (PP / 2)` using `mul_le_mul_of_nonneg_left hlogT (sq_nonneg _)`.

Establish `t2 : 26 * (D:ℝ) ^ 2 * ((27 * (PP * (q + 1)) + 65 * PP) + Real.log T) ≤ 300 * b`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `t3 : ((T:ℝ) + D + 1) * Real.log β ≤ 2 * b`. Use `mul_le_mul (show (T:ℝ) + D + 1 ≤ 2 * T by linarith) hlogβ hlogβ0 (by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hG : Formalism.NormVectorIdentities.Items.hsG D n + 2 ≤ 5 * D * PP`. Unfold `Formalism.NormVectorIdentities.Items.hsG`. Establish `a1` using `mul_le_mul_of_nonneg_left hlogn (show (0:ℝ) ≤ D + 1 by linarith)`. Establish `a2` using `mul_le_mul_of_nonneg_left hPP (show (0:ℝ) ≤ D by linarith)`. Establish `a3` using `mul_le_mul_of_nonneg_right hD1r (show (0:ℝ) ≤ PP by linarith)`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hG0 : 0 ≤ Formalism.NormVectorIdentities.Items.hsG D n + 2`. Unfold `Formalism.NormVectorIdentities.Items.hsG`. Check the signs of the components of the expression. Establish `hTDPP : (T:ℝ) * D * PP ≤ b`.

Establish `e1 : (T:ℝ) * D * PP ≤ T * T * PP`. Use `mul_le_mul_of_nonneg_left (show (D:ℝ) ≤ T by linarith) hTPP0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e2 : (T:ℝ) * T * PP ≤ T * T * PP * PP`. Use `mul_le_mul_of_nonneg_left hPP (mul_nonneg hTPP0 hTpos.le)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear relations using `only [e1, e2, hTPP2]`. Establish `t4 : ((T:ℝ) + D ^ 2) * (Formalism.NormVectorIdentities.Items.hsG D n + 2) ≤ 10 * b`. Use `mul_le_mul (show (T:ℝ) + D ^ 2 ≤ 2 * T by linarith) hG hG0 (by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hl2 : Real.log 2 < 1`. Use `Real.log_two_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hl20 : 0 ≤ Real.log 2` using `Real.log_nonneg (by norm_num)`. Establish `p1` using `mul_le_mul_of_nonneg_left hlogΛD hz0`.

Establish `p2` using `mul_le_mul_of_nonneg_left hlogΛT hz0`. Establish `p3 : z * ((T:ℝ) * Real.log β) ≤ (1/2) * ((T:ℝ) * PP)` using `mul_le_mul hz2 (mul_le_mul_of_nonneg_left hlogβ hTpos.le) (mul_nonneg hTpos.le hlogβ0) (by norm_num)`. Establish `p4 : z * ((T:ℝ) * Real.log 2) ≤ (1/2) * ((T:ℝ) * 1)` using `mul_le_mul hz2 (mul_le_mul_of_nonneg_left hl2.le hTpos.le) (mul_nonneg hTpos.le hl20) (by norm_num)`. Establish `p5 : z * ((T:ℝ) * PP) ≤ (1/2) * ((T:ℝ) * PP)` using `mul_le_mul_of_nonneg_right hz2 hTPP0`. Establish `t5 : 2 * z * ((T:ℝ) * (Real.log 2 + (27 * (PP * (q + 1)) + 65 * PP) + Real.log β / 2) + Real.log ΛD + Real.log ΛT) ≤ 200 * b`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `set B : ℝ := (((T - 1).choose D : ℕ) : ℝ) * δ with hB`. Establish `hB0 : 0 ≤ B` using `by positivity`. Establish `hR : J + 26 * (D:ℝ) ^ 2 * ((27 * (PP * (q + 1)) + 65 * PP) + Real.log T) + ((T:ℝ) + D + 1) * Real.log β + ((T:ℝ) + D ^ 2) * (Formalism.NormVectorIdentities.Items.hsG D n + 2) + 2 * z * ((T:ℝ) * (Real.log 2 + (27 * (PP * (q + 1)) + 65 * PP) + Real.log β / 2) + Real.log ΛD + Real.l …` using `by linarith`. Establish `hd2 : d ≤ 2 * B` using `by linarith [mul_le_mul_of_nonneg_right hz2 hd.le]`.

Establish `hdc` using `mul_le_mul_of_nonneg_right hd2 hc`. Establish `hBR` using `mul_le_mul_of_nonneg_left hR hB0`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem deg_bound_of_claim_numbers : ∀ (T D : ℕ) (PP kap b z ρ n Λ β ΛD ΛT J δ h d deg degM c : ℝ), 1 ≤ D → 3 * D + 5 ≤ T → 1 ≤ PP → 1 ≤ b → Real.log b ≤ PP → (T : ℝ) * PP ≤ Real.sqrt b → z = 7 * ((D : ℝ) ^ 2 / T + D * ρ) → 0 ≤ ρ → z ≤ 1 / 2 → z * (PP * kap) ≤ b → 0 ≤ kap → 1 ≤ n → 1 ≤ Λ → 1 ≤ β → 1 ≤ ΛD → 1 ≤ ΛT → 1 ≤ δ → 0 < d → Real.log n ≤ PP → Real.log β ≤ PP → Real.log δ ≤ PP → Real.log Λ ≤ PP * (kap / T + 1) → Real.log ΛD ≤ PP * kap → Real.log ΛT ≤ PP * kap → J ≤ 4 * (D * PP * (kap / T + 1) + T * PP) + 2 * PP * (kap / T) * D → (1 - z) * d ≤ ((T - 1).choose D : ℕ) * δ → Formalism.NormVectorIdentities.Items.HSClaimS 26 T D n 1 Λ β ΛD ΛT J δ h d deg → 0 ≤ c → deg - d * c ≤ degM → ((T - 1).choose D : ℕ) * δ * ((T : ℝ) * h - 3 * ((D : ℝ) + 1) * |h| - 26 * (26 * (D : ℝ) ^ 2 + 2 * z * T) * Real.log (2 + |h|) - (4000 * b + 2 * c)) ≤ degM := by
  intro T D PP kap b z ρ n Λ β ΛD ΛT J δ h d deg degM c hD1 hDT hPP hb hlogb hTPP hz hρ hz2 hzk hkap hn hΛ hβ hΛD hΛT hδ hd hlogn hlogβ hlogδ hlogΛ hlogΛD hlogΛT hJ hcmp hclaim hc hdeg
  have hT8 : (8:ℝ) ≤ T := by exact_mod_cast (by omega : 8 ≤ T)
  have hD1r : (1:ℝ) ≤ D := by exact_mod_cast hD1
  have hDTr : (D:ℝ) + 1 ≤ T := by exact_mod_cast (by omega : D + 1 ≤ T)
  have hTpos : (0:ℝ) < T := by linarith
  have hT0 : (T:ℝ) ≠ 0 := hTpos.ne'

  have hs0 : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
  have hs2 : Real.sqrt b ^ 2 = b := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ Real.sqrt b := by
    have := Real.sqrt_le_sqrt (show (1:ℝ) ≤ b from hb)
    rwa [Real.sqrt_one] at this
  have hsb : Real.sqrt b ≤ b := by nlinarith [mul_le_mul_of_nonneg_left hs1 hs0]
  have hTPPb : (T:ℝ) * PP ≤ b := le_trans hTPP hsb
  have hTPP0 : 0 ≤ (T:ℝ) * PP := by positivity
  have hTPP2 : ((T:ℝ) * PP) ^ 2 ≤ b := by
    calc ((T:ℝ) * PP) ^ 2 ≤ (Real.sqrt b) ^ 2 := pow_le_pow_left₀ hTPP0 hTPP 2
      _ = b := hs2
  have hTs : (T:ℝ) ≤ Real.sqrt b := le_trans (by nlinarith) hTPP
  have hlogT : Real.log T ≤ PP / 2 := by
    have := Real.log_le_log hTpos hTs
    rw [Real.log_sqrt (by linarith)] at this
    linarith
  have hlogD : Real.log D ≤ Real.log T := Real.log_le_log (by linarith) (by linarith)
  have hlogΛ0 : 0 ≤ Real.log Λ := Real.log_nonneg hΛ
  have hlogβ0 : 0 ≤ Real.log β := Real.log_nonneg hβ
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn
  have hlog1 : Real.log (1 + Real.log Λ) ≤ Real.log Λ := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + Real.log Λ by linarith)
    linarith
  have hprod : Real.log (n * D * δ * (1 + Real.log Λ)) =
      Real.log n + Real.log D + Real.log δ + Real.log (1 + Real.log Λ) := by
    have h1 : (0:ℝ) < n := by linarith
    have h2 : (0:ℝ) < D := by linarith
    have h3 : (0:ℝ) < δ := by linarith
    have h4 : (0:ℝ) < 1 + Real.log Λ := by linarith
    rw [Real.log_mul (mul_pos (mul_pos h1 h2) h3).ne' h4.ne',
      Real.log_mul (mul_pos h1 h2).ne' h3.ne', Real.log_mul h1.ne' h2.ne']

  have hD2T0 : 0 ≤ (D:ℝ) ^ 2 / T := by positivity
  have hDρ : 0 ≤ (D:ℝ) * ρ := mul_nonneg (by positivity) hρ
  have hz0 : 0 ≤ z := by rw [hz]; linarith
  have hD2z : (D:ℝ) ^ 2 ≤ z * T / 7 := by
    have e : z * T / 7 = (D:ℝ) ^ 2 + D * ρ * T := by rw [hz]; field_simp
    rw [e]; have := mul_nonneg hDρ hTpos.le; linarith
  have hD2T : (D:ℝ) ^ 2 ≤ T / 14 := by nlinarith [mul_le_mul_of_nonneg_right hz2 hTpos.le]

  have hq0 : 0 ≤ kap / T := div_nonneg hkap hTpos.le
  obtain ⟨q, hq⟩ : ∃ q : ℝ, kap / T = q := ⟨_, rfl⟩
  have hkq : kap = q * T := by rw [← hq]; field_simp
  rw [hq] at hlogΛ hJ hq0
  rw [hkq] at hzk hlogΛD hlogΛT
  clear hq hkq hkap
  have hl0 : Real.log Λ + 26 * Real.log (n * D * δ * (1 + Real.log Λ)) ≤
      27 * (PP * (q + 1)) + 65 * PP := by
    rw [hprod]; linarith
  have key := GlobalTheory.T.hilbertSamuel_degree_ratio_lower_bound_rearranged T D n Λ β ΛD ΛT J δ h d deg z (27 * (PP * (q + 1)) + 65 * PP)
    (by omega) hD1 hn hΛ hβ hΛD hΛT hδ hd hz0 hz2 hcmp hl0 hclaim

  have hPPq : 0 ≤ PP * q := mul_nonneg (by linarith) hq0
  have F1 : (D:ℝ) ^ 2 * (PP * q) ≤ b / 7 := by
    linarith [mul_le_mul_of_nonneg_right hD2z hPPq]
  have F2 : (D:ℝ) ^ 2 * PP ≤ b / 14 := by
    linarith [mul_le_mul_of_nonneg_right hD2T (show (0:ℝ) ≤ PP by linarith)]
  have hDD2 : (D:ℝ) ≤ (D:ℝ) ^ 2 := by nlinarith
  have hDPPq : (D:ℝ) * (PP * q) ≤ b / 7 := by
    linarith [mul_le_mul_of_nonneg_right hDD2 hPPq]
  have hDPP : (D:ℝ) * PP ≤ b := by
    linarith [mul_le_mul_of_nonneg_right (show (D:ℝ) ≤ T by linarith) (show (0:ℝ) ≤ PP by linarith)]
  have t1 : J ≤ 9 * b := by linarith
  have hDlogT : (D:ℝ) ^ 2 * Real.log T ≤ (D:ℝ) ^ 2 * (PP / 2) :=
    mul_le_mul_of_nonneg_left hlogT (sq_nonneg _)
  have t2 : 26 * (D:ℝ) ^ 2 * ((27 * (PP * (q + 1)) + 65 * PP) + Real.log T) ≤ 300 * b := by
    linarith
  have t3 : ((T:ℝ) + D + 1) * Real.log β ≤ 2 * b := by
    have := mul_le_mul (show (T:ℝ) + D + 1 ≤ 2 * T by linarith) hlogβ hlogβ0 (by linarith)
    linarith
  have hG : Formalism.NormVectorIdentities.Items.hsG D n + 2 ≤ 5 * D * PP := by
    unfold Formalism.NormVectorIdentities.Items.hsG
    have a1 := mul_le_mul_of_nonneg_left hlogn (show (0:ℝ) ≤ D + 1 by linarith)
    have a2 := mul_le_mul_of_nonneg_left hPP (show (0:ℝ) ≤ D by linarith)
    have a3 := mul_le_mul_of_nonneg_right hD1r (show (0:ℝ) ≤ PP by linarith)
    nlinarith
  have hG0 : 0 ≤ Formalism.NormVectorIdentities.Items.hsG D n + 2 := by
    unfold Formalism.NormVectorIdentities.Items.hsG; positivity
  have hTDPP : (T:ℝ) * D * PP ≤ b := by
    have e1 : (T:ℝ) * D * PP ≤ T * T * PP := by
      have := mul_le_mul_of_nonneg_left (show (D:ℝ) ≤ T by linarith) hTPP0
      linarith
    have e2 : (T:ℝ) * T * PP ≤ T * T * PP * PP := by
      have := mul_le_mul_of_nonneg_left hPP (mul_nonneg hTPP0 hTpos.le)
      linarith
    linarith only [e1, e2, hTPP2]
  have t4 : ((T:ℝ) + D ^ 2) * (Formalism.NormVectorIdentities.Items.hsG D n + 2) ≤ 10 * b := by
    have := mul_le_mul (show (T:ℝ) + D ^ 2 ≤ 2 * T by linarith) hG hG0 (by linarith)
    linarith
  have hl2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have p1 := mul_le_mul_of_nonneg_left hlogΛD hz0
  have p2 := mul_le_mul_of_nonneg_left hlogΛT hz0
  have p3 : z * ((T:ℝ) * Real.log β) ≤ (1/2) * ((T:ℝ) * PP) :=
    mul_le_mul hz2 (mul_le_mul_of_nonneg_left hlogβ hTpos.le) (mul_nonneg hTpos.le hlogβ0) (by norm_num)
  have p4 : z * ((T:ℝ) * Real.log 2) ≤ (1/2) * ((T:ℝ) * 1) :=
    mul_le_mul hz2 (mul_le_mul_of_nonneg_left hl2.le hTpos.le) (mul_nonneg hTpos.le hl20) (by norm_num)
  have p5 : z * ((T:ℝ) * PP) ≤ (1/2) * ((T:ℝ) * PP) :=
    mul_le_mul_of_nonneg_right hz2 hTPP0
  have t5 : 2 * z * ((T:ℝ) * (Real.log 2 + (27 * (PP * (q + 1)) + 65 * PP) + Real.log β / 2) +
      Real.log ΛD + Real.log ΛT) ≤ 200 * b := by
    linarith

  set B : ℝ := (((T - 1).choose D : ℕ) : ℝ) * δ with hB
  have hB0 : 0 ≤ B := by positivity
  have hR : J + 26 * (D:ℝ) ^ 2 * ((27 * (PP * (q + 1)) + 65 * PP) + Real.log T) + ((T:ℝ) + D + 1) * Real.log β +
      ((T:ℝ) + D ^ 2) * (Formalism.NormVectorIdentities.Items.hsG D n + 2) + 2 * z * ((T:ℝ) * (Real.log 2 + (27 * (PP * (q + 1)) + 65 * PP) + Real.log β / 2) +
      Real.log ΛD + Real.log ΛT) ≤ 4000 * b := by linarith
  have hd2 : d ≤ 2 * B := by linarith [mul_le_mul_of_nonneg_right hz2 hd.le]
  have hdc := mul_le_mul_of_nonneg_right hd2 hc
  have hBR := mul_le_mul_of_nonneg_left hR hB0
  linarith

end GlobalTheory.CovHSNum
