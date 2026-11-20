import Formalism.SizeWindowBrackets.ClaimGaFree

namespace Formalism.LFunctionChainParameters.UnitWeightPartition

open Finset

variable {ι κ : Type*} [DecidableEq ι]

/- English proof (translation)
Establish `hF : ∑ j ∈ J, ∑ w ∈ W, l w * F j w = ∑ w ∈ W, ∑ j ∈ J, l w * F j w` using `Finset.sum_comm`. Establish `hE : ∑ j ∈ J, ∑ w ∈ W, l w * E j w = ∑ w ∈ W, ∑ j ∈ J, l w * E j w` using `Finset.sum_comm`. Unfold `ClaimSg Sg sgw Ga Fo Ee`. Rewrite using `[hF, hE, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl (fun w _ => ?_)` and prove the remaining obligations.

Simplify using `only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem weightedSlopeExcess_decomposition (W : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain F E : κ → ι → ℝ)
    (tau : ι → ℝ) : ClaimSg W J l gain F E tau := by
  have hF : ∑ j ∈ J, ∑ w ∈ W, l w * F j w = ∑ w ∈ W, ∑ j ∈ J, l w * F j w := Finset.sum_comm
  have hE : ∑ j ∈ J, ∑ w ∈ W, l w * E j w = ∑ w ∈ W, ∑ j ∈ J, l w * E j w := Finset.sum_comm
  unfold ClaimSg Sg sgw Ga Fo Ee
  rw [hF, hE, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/- English proof (translation)
Unfold `ClaimUnit`. Introduce `hP hl hio`. Establish `hmain : 2 * ∑ w ∈ W, l w * io w = 2 * ∑ p ∈ P, Real.log (p : ℝ) * iop p`. Use `congr 1`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to hP]`.

Use `Finset.sum_congr rfl (fun p hp => ?_)` and prove the remaining obligations. Rewrite using `[← hl p hp, Finset.sum_mul]`. Use `Finset.sum_congr rfl (fun w hw => ?_)` and prove the remaining obligations. Rewrite `hw` using `[Finset.mem_filter]`. Rewrite using `[hio w hw.1, hw.2]`.

Use `Eq.trans ?_ hmain` and prove the remaining obligations. Apply the tactic sequence `first | rfl | (show ∑ w ∈ W, 2 * l w * io w = _; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun w _ => mul_assoc _ _ _)) | (show ∑ w ∈ W, 2 * (l w * io w) = _; rw [Finset.mul_sum])`.
-/
theorem unit_weight_partition (W : Finset ι) (P : Finset ℕ) (pr : ι → ℕ) (l io : ι → ℝ)
    (iop : ℕ → ℝ) : ClaimUnit W P pr l io iop := by
  unfold ClaimUnit
  intro hP hl hio
  have hmain : 2 * ∑ w ∈ W, l w * io w = 2 * ∑ p ∈ P, Real.log (p : ℝ) * iop p := by
    congr 1
    rw [← Finset.sum_fiberwise_of_maps_to hP]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [← hl p hp, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun w hw => ?_)
    rw [Finset.mem_filter] at hw
    rw [hio w hw.1, hw.2]
  refine Eq.trans ?_ hmain
  first | rfl | (show ∑ w ∈ W, 2 * l w * io w = _; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun w _ => mul_assoc _ _ _)) | (show ∑ w ∈ W, 2 * (l w * io w) = _; rw [Finset.mul_sum])

/- English proof (translation)
Unfold `ClaimDe`. Introduce `hdM hT hdu`. Establish `hT1 : (1 : ℝ) < T - 1` using `by linarith`. Establish `hT1p : (0 : ℝ) < T - 1` using `by linarith`. Establish `hTp : (0 : ℝ) < T` using `by linarith`.

Establish `hx0 : 0 < 1 / (T - 1)` using `div_pos one_pos hT1p`. Establish `hx1 : 1 / (T - 1) < 1` using `by rw [div_lt_one hT1p]; exact hT1`. Establish `hq0 : 0 < 1 - 1 / (T - 1)` using `by linarith`. Establish `hq1 : 1 - 1 / (T - 1) ≤ 1` using `by linarith`. Establish `hdM0 : dM ≠ 0` using `hdM.ne'`.

Establish `hr : du / dM = (1 - 1 / (T - 1)) ^ f`. Rewrite using `[hdu, mul_div_right_comm, div_self hdM0, one_mul]`. Establish `hpow0 : 0 < (1 - 1 / (T - 1)) ^ f` using `pow_pos hq0 f`. Establish `hpow1 : (1 - 1 / (T - 1)) ^ f ≤ 1` using `pow_le_one₀ hq0.le hq1`. Establish `hbern : 1 + (f : ℝ) * (-(1 / (T - 1))) ≤ (1 + -(1 / (T - 1))) ^ f` using `one_add_mul_le_pow (by linarith) f`.

Establish `hq : (1 : ℝ) + -(1 / (T - 1)) = 1 - 1 / (T - 1)` using `by ring`. Rewrite `hbern` using `[hq]`. Establish `hfx : (f : ℝ) * (-(1 / (T - 1))) = -((f : ℝ) / (T - 1))` using `by ring`. Establish `hf0 : (0 : ℝ) ≤ f` using `Nat.cast_nonneg f`. Establish `hfT : (f : ℝ) / (T - 1) ≤ 2 * (f : ℝ) / T`.

Rewrite using `[div_le_iff₀ hT1p, div_mul_eq_mul_div, le_div_iff₀ hTp]`. Use polynomial arithmetic with `[mul_nonneg hf0 (by linarith : (0 : ℝ) ≤ T - 2)]`. Rewrite using `[hr]`. Use `⟨?_, by linarith, by linarith, by linarith⟩` and prove the remaining obligations. Rewrite using `[hdu]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem deficit_bounds (f : ℕ) (T dM du : ℝ) : ClaimDe f T dM du := by
  unfold ClaimDe
  intro hdM hT hdu
  have hT1 : (1 : ℝ) < T - 1 := by linarith
  have hT1p : (0 : ℝ) < T - 1 := by linarith
  have hTp : (0 : ℝ) < T := by linarith
  have hx0 : 0 < 1 / (T - 1) := div_pos one_pos hT1p
  have hx1 : 1 / (T - 1) < 1 := by rw [div_lt_one hT1p]; exact hT1
  have hq0 : 0 < 1 - 1 / (T - 1) := by linarith
  have hq1 : 1 - 1 / (T - 1) ≤ 1 := by linarith
  have hdM0 : dM ≠ 0 := hdM.ne'
  have hr : du / dM = (1 - 1 / (T - 1)) ^ f := by
    rw [hdu, mul_div_right_comm, div_self hdM0, one_mul]
  have hpow0 : 0 < (1 - 1 / (T - 1)) ^ f := pow_pos hq0 f
  have hpow1 : (1 - 1 / (T - 1)) ^ f ≤ 1 := pow_le_one₀ hq0.le hq1
  have hbern : 1 + (f : ℝ) * (-(1 / (T - 1))) ≤ (1 + -(1 / (T - 1))) ^ f :=
    one_add_mul_le_pow (by linarith) f
  have hq : (1 : ℝ) + -(1 / (T - 1)) = 1 - 1 / (T - 1) := by ring
  rw [hq] at hbern
  have hfx : (f : ℝ) * (-(1 / (T - 1))) = -((f : ℝ) / (T - 1)) := by ring
  have hf0 : (0 : ℝ) ≤ f := Nat.cast_nonneg f
  have hfT : (f : ℝ) / (T - 1) ≤ 2 * (f : ℝ) / T := by
    rw [div_le_iff₀ hT1p, div_mul_eq_mul_div, le_div_iff₀ hTp]
    nlinarith [mul_nonneg hf0 (by linarith : (0 : ℝ) ≤ T - 2)]
  rw [hr]
  refine ⟨?_, by linarith, by linarith, by linarith⟩
  rw [hdu]
  ring

/- English proof (translation)
Unfold `ClaimT`. Introduce `hl hdM hde0 hde1 hdu hlam hlen hsum`. Establish `hdu0 : 0 < du` using `by rw [hdu]; exact mul_pos (by linarith) hdM`. Establish `hdu2 : dM ≤ 2 * du`. Rewrite using `[hdu]`.

Use polynomial arithmetic with `[mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * de) hdM.le]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum (fun w hw => ?_)` and prove the remaining obligations. Rewrite using `[div_le_iff₀ hdu0]`. Establish `h1` using `hl w hw`.

Establish `h2` using `hlen w hw`. Use polynomial arithmetic with `[mul_nonneg h1 (sub_nonneg.2 h2), mul_nonneg (mul_nonneg h1 hlam) (sub_nonneg.2 hdu2)]`. Use `_ = 4 * lam * Real.log T := by rw [← Finset.mul_sum, hsum]`.
-/
theorem truncatedLength_bound (WT : Finset ι) (l len : ι → ℝ) (dM du de lam T : ℝ) :
    ClaimT WT l len dM du de lam T := by
  unfold ClaimT
  intro hl hdM hde0 hde1 hdu hlam hlen hsum
  have hdu0 : 0 < du := by rw [hdu]; exact mul_pos (by linarith) hdM
  have hdu2 : dM ≤ 2 * du := by
    rw [hdu]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * de) hdM.le]
  calc ∑ w ∈ WT, 2 * l w * len w / du ≤ ∑ w ∈ WT, 4 * lam * l w := by
        refine Finset.sum_le_sum (fun w hw => ?_)
        rw [div_le_iff₀ hdu0]
        have h1 := hl w hw
        have h2 := hlen w hw
        nlinarith [mul_nonneg h1 (sub_nonneg.2 h2),
          mul_nonneg (mul_nonneg h1 hlam) (sub_nonneg.2 hdu2)]
    _ = 4 * lam * Real.log T := by rw [← Finset.mul_sum, hsum]

/- English proof (translation)
Unfold `HypLow at H`. Take `⟨hl, hdM, hde0, hde1, hdu, hWT, htau, hio, hlen, hPT, hRd, hmuN⟩` from `H`. Establish `hsg` using `weightedSlopeExcess_decomposition W J l gain F E tau`. Unfold `ClaimSg at hsg`. Establish `hde' : 0 < 1 - de` using `by linarith`.

Establish `hdu0 : 0 < du` using `by rw [hdu]; exact mul_pos hde' hdM`. Establish `hdM0 : dM ≠ 0` using `hdM.ne'`. Establish `hde0' : 1 - de ≠ 0` using `hde'.ne'`. Establish `ha : Sg W l (sgw J gain F E) tau - Sg W l sg' tau ≤ Rd`. Unfold `Sg`.

Rewrite using `[← Finset.sum_sub_distrib]`. Conclude with `le_trans (le_of_eq (Finset.sum_congr rfl (fun w _ => by ring))) hRd`. Establish `hsplit : ∑ w ∈ W \ WT, 2 * l w * be du len tau w + ∑ w ∈ WT, 2 * l w * be du len tau w = BeSum W l du len tau` using `Finset.sum_sdiff hWT`. Establish `hT : ∑ w ∈ WT, 2 * l w * be du len tau w = ∑ w ∈ WT, 2 * l w * len w / du`. Use `Finset.sum_congr rfl (fun w hw => ?_)` and prove the remaining obligations.

Unfold `be`. Rewrite using `[htau w hw]`. Expand and normalize the polynomial expressions, which then agree. Establish `hN : ∑ w ∈ W \ WT, 2 * l w * be du len tau w ≤ ∑ w ∈ W \ WT, (1 / (1 - de) * (2 * (l w * io w)) + de / (1 - de) * (2 * (l w * tau w)))`. Use `Finset.sum_le_sum (fun w hw => ?_)` and prove the remaining obligations.

Establish `hwW` using `(Finset.mem_sdiff.1 hw).1`. Establish `h1` using `hl w hwW`. Establish `h2` using `hlen w hw`. Establish `h3` using `hio w hwW`. Unfold `be`.

Establish `key : 1 / (1 - de) * (2 * (l w * io w)) + de / (1 - de) * (2 * (l w * tau w)) - 2 * l w * ((len w - du * tau w) / du) = 2 * l w * (dM * (tau w + io w) - len w) / du`. Rewrite using `[hdu]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `h4 : 0 ≤ 2 * l w * (dM * (tau w + io w) - len w) / du` using `div_nonneg (mul_nonneg (by linarith) (by linarith)) hdu0.le`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hIOge : ∑ w ∈ W \ WT, l w * io w ≤ ∑ w ∈ W, l w * io w` using `Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun w hw _ => mul_nonneg (hl w hw) (hio w hw))`. Establish `hTa0 : ∑ w ∈ WT, l w * tau w = 0` using `Finset.sum_eq_zero (fun w hw => by rw [htau w hw, mul_zero])`. Establish `hTas : ∑ w ∈ W \ WT, l w * tau w + ∑ w ∈ WT, l w * tau w = ∑ w ∈ W, l w * tau w` using `Finset.sum_sdiff hWT`. Establish `hN2 : ∑ w ∈ W \ WT, (1 / (1 - de) * (2 * (l w * io w)) + de / (1 - de) * (2 * (l w * tau w))) = 1 / (1 - de) * (2 * ∑ w ∈ W \ WT, l w * io w) + de / (1 - de) * Ta W l tau`.

Rewrite using `[Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]`. Unfold `Ta`. Rewrite using `[← hTas, hTa0, add_zero]`. Establish `hc : 1 / (1 - de) * (2 * ∑ w ∈ W \ WT, l w * io w) ≤ X / (1 - de)`. Rewrite using `[hX, one_div, div_eq_inv_mul]`.

Conclude with `mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hde'.le)`. Establish `hbe : BeSum W l du len tau ≤ PT + X / (1 - de) + de / (1 - de) * Ta W l tau`. Rewrite using `[← hsplit, hT]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hmuN]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem le_muN_of_hypLow {W WT : Finset ι} {J : Finset κ} {l : ι → ℝ} {gain F E : κ → ι → ℝ}
    {tau io len sg' : ι → ℝ} {dM du de muMu muN PT Rd X : ℝ}
    (hX : X = 2 * ∑ w ∈ W, l w * io w)
    (H : HypLow W WT J l gain F E tau io len sg' dM du de muMu muN PT Rd) :
    muMu + Ga W J l gain tau + Fo W J l F - Ee W J l E - Rd - PT - X / (1 - de)
      - de / (1 - de) * Ta W l tau ≤ muN := by
  unfold HypLow at H
  obtain ⟨hl, hdM, hde0, hde1, hdu, hWT, htau, hio, hlen, hPT, hRd, hmuN⟩ := H
  have hsg := weightedSlopeExcess_decomposition W J l gain F E tau
  unfold ClaimSg at hsg
  have hde' : 0 < 1 - de := by linarith
  have hdu0 : 0 < du := by rw [hdu]; exact mul_pos hde' hdM
  have hdM0 : dM ≠ 0 := hdM.ne'
  have hde0' : 1 - de ≠ 0 := hde'.ne'
  have ha : Sg W l (sgw J gain F E) tau - Sg W l sg' tau ≤ Rd := by
    unfold Sg
    rw [← Finset.sum_sub_distrib]
    exact le_trans (le_of_eq (Finset.sum_congr rfl (fun w _ => by ring))) hRd
  have hsplit : ∑ w ∈ W \ WT, 2 * l w * be du len tau w + ∑ w ∈ WT, 2 * l w * be du len tau w
      = BeSum W l du len tau := Finset.sum_sdiff hWT
  have hT : ∑ w ∈ WT, 2 * l w * be du len tau w = ∑ w ∈ WT, 2 * l w * len w / du := by
    refine Finset.sum_congr rfl (fun w hw => ?_)
    unfold be
    rw [htau w hw]
    ring
  have hN : ∑ w ∈ W \ WT, 2 * l w * be du len tau w ≤ ∑ w ∈ W \ WT,
      (1 / (1 - de) * (2 * (l w * io w)) + de / (1 - de) * (2 * (l w * tau w))) := by
    refine Finset.sum_le_sum (fun w hw => ?_)
    have hwW := (Finset.mem_sdiff.1 hw).1
    have h1 := hl w hwW
    have h2 := hlen w hw
    have h3 := hio w hwW
    unfold be
    have key : 1 / (1 - de) * (2 * (l w * io w)) + de / (1 - de) * (2 * (l w * tau w))
        - 2 * l w * ((len w - du * tau w) / du) = 2 * l w * (dM * (tau w + io w) - len w) / du := by
      rw [hdu]
      field_simp
      ring
    have h4 : 0 ≤ 2 * l w * (dM * (tau w + io w) - len w) / du :=
      div_nonneg (mul_nonneg (by linarith) (by linarith)) hdu0.le
    linarith
  have hIOge : ∑ w ∈ W \ WT, l w * io w ≤ ∑ w ∈ W, l w * io w :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun w hw _ => mul_nonneg (hl w hw) (hio w hw))
  have hTa0 : ∑ w ∈ WT, l w * tau w = 0 :=
    Finset.sum_eq_zero (fun w hw => by rw [htau w hw, mul_zero])
  have hTas : ∑ w ∈ W \ WT, l w * tau w + ∑ w ∈ WT, l w * tau w = ∑ w ∈ W, l w * tau w :=
    Finset.sum_sdiff hWT
  have hN2 : ∑ w ∈ W \ WT,
      (1 / (1 - de) * (2 * (l w * io w)) + de / (1 - de) * (2 * (l w * tau w)))
      = 1 / (1 - de) * (2 * ∑ w ∈ W \ WT, l w * io w) + de / (1 - de) * Ta W l tau := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum]
    unfold Ta
    rw [← hTas, hTa0, add_zero]
  have hc : 1 / (1 - de) * (2 * ∑ w ∈ W \ WT, l w * io w) ≤ X / (1 - de) := by
    rw [hX, one_div, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hde'.le)
  have hbe : BeSum W l du len tau ≤ PT + X / (1 - de) + de / (1 - de) * Ta W l tau := by
    rw [← hsplit, hT]
    linarith
  rw [hmuN]
  linarith

/- English proof (translation)
Establish `hl2` using `le_muN_of_hypLow (X := 2 * Q) hq H`. Unfold `HypLow at H`. Unfold `HypLow2 at H2`. Take `⟨hl, -, hde0, -, -, -, -, hio, -, -, -, -⟩` from `H`. Take `⟨a1, a2, a3, a4, a5, a6, -, a8, a9⟩` from `H2`.

Establish `hde' : 0 < 1 - de` using `by linarith`. Establish `hQ0 : 0 ≤ Q`. Establish `: 0 ≤ ∑ w ∈ W, l w * io w` using `Finset.sum_nonneg (fun w hw => mul_nonneg (hl w hw) (hio w hw))`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hTa0 : 0 ≤ Ta W l tau`.

Unfold `Ta`. Establish `: 0 ≤ ∑ w ∈ W, l w * tau w` using `Finset.sum_nonneg (fun w hw => mul_nonneg (hl w hw) (a4 w hw))`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hio2 : 2 * Q / (1 - de) ≤ 4 * Q`. Rewrite using `[div_le_iff₀ hde']`.

Use polynomial arithmetic with `[mul_nonneg hQ0 (by linarith : (0 : ℝ) ≤ 1 - 2 * de)]`. Establish `hk : de / (1 - de) ≤ 2 * de`. Rewrite using `[div_le_iff₀ hde']`. Use polynomial arithmetic with `[mul_nonneg hde0 (by linarith : (0 : ℝ) ≤ 1 - 2 * de)]`. Establish `hchain : de / (1 - de) * Ta W l tau ≤ 4 * f / T * b ^ 2`.

Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem le_muN_of_hypLow_of_hypLow2 {W WT : Finset ι} {J : Finset κ} {l : ι → ℝ}
    {gain F E : κ → ι → ℝ} {tau io len sg' : ι → ℝ} {dM du de muMu muN PT Rd : ℝ}
    {f T b muM Q LT RX : ℝ}
    (hq : 2 * Q = 2 * ∑ w ∈ W, l w * io w)
    (H : HypLow W WT J l gain F E tau io len sg' dM du de muMu muN PT Rd)
    (H2 : HypLow2 W l tau io f T de b muM muMu Q PT LT Rd RX) :
    muM + Ga W J l gain tau + Fo W J l F - Ee W J l E - (4 * Q + LT + RX + 1) ≤ muN := by
  have hl2 := le_muN_of_hypLow (X := 2 * Q) hq H
  unfold HypLow at H
  unfold HypLow2 at H2
  obtain ⟨hl, -, hde0, -, -, -, -, hio, -, -, -, -⟩ := H
  obtain ⟨a1, a2, a3, a4, a5, a6, -, a8, a9⟩ := H2
  have hde' : 0 < 1 - de := by linarith
  have hQ0 : 0 ≤ Q := by
    have : 0 ≤ ∑ w ∈ W, l w * io w :=
      Finset.sum_nonneg (fun w hw => mul_nonneg (hl w hw) (hio w hw))
    linarith
  have hTa0 : 0 ≤ Ta W l tau := by
    unfold Ta
    have : 0 ≤ ∑ w ∈ W, l w * tau w :=
      Finset.sum_nonneg (fun w hw => mul_nonneg (hl w hw) (a4 w hw))
    linarith
  have hio2 : 2 * Q / (1 - de) ≤ 4 * Q := by
    rw [div_le_iff₀ hde']
    nlinarith [mul_nonneg hQ0 (by linarith : (0 : ℝ) ≤ 1 - 2 * de)]
  have hk : de / (1 - de) ≤ 2 * de := by
    rw [div_le_iff₀ hde']
    nlinarith [mul_nonneg hde0 (by linarith : (0 : ℝ) ≤ 1 - 2 * de)]
  have hchain : de / (1 - de) * Ta W l tau ≤ 4 * f / T * b ^ 2 :=
    calc de / (1 - de) * Ta W l tau ≤ 2 * de * Ta W l tau := mul_le_mul_of_nonneg_right hk hTa0
      _ ≤ 2 * (2 * f / T) * Ta W l tau := mul_le_mul_of_nonneg_right (by linarith) hTa0
      _ ≤ 2 * (2 * f / T) * b ^ 2 := mul_le_mul_of_nonneg_left a5 (by linarith)
      _ = 4 * f / T * b ^ 2 := by ring
  linarith

/- English proof (translation)
Unfold `ClaimLow2`. Introduce `H H2`. Use `le_muN_of_hypLow_of_hypLow2 ?_ H H2` and prove the remaining obligations. Unfold `HypLow2 at H2`. Take `⟨-, -, -, -, -, -, a7, -, -⟩` from `H2`.

Apply the tactic sequence `exact a7.symm.trans (by first | rfl | (show ∑ w ∈ W, 2 * l w * io w = _; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun w _ => mul_assoc _ _ _)) | (show ∑ w ∈ W, 2 * (l w * io w) = _; rw [Finset.mul_sum]))`.
-/
theorem lower_bound_simplified (W WT : Finset ι) (J : Finset κ) (l : ι → ℝ)
    (gain F E : κ → ι → ℝ) (tau io len sg' : ι → ℝ) (dM du de muMu muN PT Rd : ℝ)
    (f T b muM IOp LT RX : ℝ) :
    ClaimLow2 W WT J l gain F E tau io len sg' dM du de muMu muN PT Rd f T b muM IOp LT RX := by
  unfold ClaimLow2
  intro H H2
  refine le_muN_of_hypLow_of_hypLow2 ?_ H H2
  unfold HypLow2 at H2
  obtain ⟨-, -, -, -, -, -, a7, -, -⟩ := H2
  exact a7.symm.trans (by first | rfl | (show ∑ w ∈ W, 2 * l w * io w = _; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun w _ => mul_assoc _ _ _)) | (show ∑ w ∈ W, 2 * (l w * io w) = _; rw [Finset.mul_sum]))

/- English proof (translation)
Unfold `ClaimHigh`. Introduce `H`. Unfold `HypHigh at H`. Take `⟨hl, hsg', h1, h2⟩` from `H`. Establish `hsg` using `weightedSlopeExcess_decomposition W J l gain F E tau`.

Unfold `ClaimSg at hsg`. Establish `hle : Sg W l sg' tau ≤ Sg W l (sgw J gain F E) tau`. Unfold `Sg`. Use `Finset.sum_le_sum (fun w hw => ?_)` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_left (by linarith [hsg' w hw]) (by linarith [hl w hw])`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem claimHigh_valid (W : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain F E : κ → ι → ℝ)
    (tau sg' : ι → ℝ) (muMaxM muMaxMu muMaxN : ℝ) :
    ClaimHigh W J l gain F E tau sg' muMaxM muMaxMu muMaxN := by
  unfold ClaimHigh
  intro H
  unfold HypHigh at H
  obtain ⟨hl, hsg', h1, h2⟩ := H
  have hsg := weightedSlopeExcess_decomposition W J l gain F E tau
  unfold ClaimSg at hsg
  have hle : Sg W l sg' tau ≤ Sg W l (sgw J gain F E) tau := by
    unfold Sg
    refine Finset.sum_le_sum (fun w hw => ?_)
    exact mul_le_mul_of_nonneg_left (by linarith [hsg' w hw]) (by linarith [hl w hw])
  linarith

end Formalism.LFunctionChainParameters.UnitWeightPartition
