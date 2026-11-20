import Mathlib
import GroundTheory.PAdicHodge.ExistsIsRootForallNormPowMulLe
import GroundTheory.PAdicHodge.ExtRobbaPointDiv
import GroundTheory.PAdicHodge.ExtRobbaUnits
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace TeichLift

open Laurent Filter Topology UniformSpace

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

/- English proof (translation)
Rewrite using `[mem_Econ, coeffB_algebraMap]`. Conclude with `T.convergesAt_zcoeff_mul ρ0.2.1 ρ0.2.2 (T.convergesAt_teich z _) (T.convergesAt_of_mem_int hV ρ0.2.1 ρ0.2.2)`.
-/
theorem teich_mul_int_mem_Econ (z : L) {V : Γ} (hV : V ∈ T.int) (ρ0 : Set.Ioo (0 : ℝ) 1) :
    algebraMap Γ T.B (T.teich z * V) ∈ T.Econ ρ0 := by
  rw [mem_Econ, coeffB_algebraMap]
  exact T.convergesAt_zcoeff_mul ρ0.2.1 ρ0.2.2 (T.convergesAt_teich z _)
    (T.convergesAt_of_mem_int hV ρ0.2.1 ρ0.2.2)

def liftExt (ρ0 : Set.Ioo (0 : ℝ) 1) (z : L) {V : Γ} (hV : V ∈ T.int) : T.RobbaExt ρ0 :=
  ((⟨algebraMap Γ T.B (T.teich z * V), T.teich_mul_int_mem_Econ z hV ρ0⟩ : T.Econ ρ0) :
    T.RobbaExt ρ0)

/- English proof (translation)
Rewrite using `[liftExt, extNorm_coe]`. Use `show gaussNorm (T.coeffB (algebraMap Γ T.B (T.teich z * V))) σ = ‖z‖`. Rewrite using `[coeffB_algebraMap, T.gaussNorm_zcoeff_mul (rad_pos ρ0 σ) (rad_lt_one ρ0 σ) (T.convergesAt_teich z _) (T.convergesAt_of_mem_int hV (rad_pos ρ0 σ) (rad_lt_one ρ0 σ)), T.gaussNorm_teich z (rad_pos ρ0 σ), T.gaussNorm_eq_one_of_mem_int hV h1 (rad_pos ρ0 σ) (rad_lt_one ρ0 σ), mul_one]`.
-/
theorem extNorm_liftExt {ρ0 : Set.Ioo (0 : ℝ) 1} (z : L) {V : Γ} (hV : V ∈ T.int)
    (h1 : ‖T.red V‖ = 1) (σ : Set.Ioc (0 : ℝ) ρ0) :
    T.extNorm ρ0 σ (T.liftExt ρ0 z hV) = ‖z‖ := by
  rw [liftExt, extNorm_coe]
  show gaussNorm (T.coeffB (algebraMap Γ T.B (T.teich z * V))) σ = ‖z‖
  rw [coeffB_algebraMap, T.gaussNorm_zcoeff_mul (rad_pos ρ0 σ) (rad_lt_one ρ0 σ)
    (T.convergesAt_teich z _) (T.convergesAt_of_mem_int hV (rad_pos ρ0 σ) (rad_lt_one ρ0 σ)),
    T.gaussNorm_teich z (rad_pos ρ0 σ),
    T.gaussNorm_eq_one_of_mem_int hV h1 (rad_pos ρ0 σ) (rad_lt_one ρ0 σ), mul_one]

variable {ξ : T.int} (hξ : T.IsPrimOne ξ)

/- English proof (translation)
Rewrite using `[zcoeff_one]`. Conclude with `convergesAt_pi_single _ _ _`.
-/
theorem convergesAt_one_ptRad : ConvergesAt (T.zcoeff (1 : Γ)) (T.ptRad ξ) := by
  rw [zcoeff_one]; exact convergesAt_pi_single _ _ _

/- English proof (translation)
Use `T.ptE_teich_mul hξ a 1 (T.convergesAt_one_ptRad (ξ := ξ))` as an intermediate fact. Rewrite `this` using `[mul_one, ptE_one, mul_one]`. Then use the resulting hypothesis.
-/
theorem ptE_teich (a : L) : T.ptE hξ (T.teich a) = T.ptSharp hξ a := by
  have := T.ptE_teich_mul hξ a 1 (T.convergesAt_one_ptRad (ξ := ξ))
  rwa [mul_one, ptE_one, mul_one] at this

/- English proof (translation)
Use `T.ptE_π_pow hξ 1` as an intermediate fact. Rewrite `this` using `[pow_one, pow_one]`. Then use the resulting hypothesis.
-/
theorem ptE_π : T.ptE hξ T.π = T.ptPi hξ := by
  have := T.ptE_π_pow hξ 1
  rwa [pow_one, pow_one] at this

/- English proof (translation)
Rewrite using `[liftExt, ptEval_coe]`. Use `show T.ptEvalB hξ (algebraMap Γ T.B (T.teich z * V)) = _`. Rewrite using `[ptEvalB_algebraMap, T.ptE_teich_mul hξ z V (T.convergesAt_of_mem_int hV (T.ptRad_pos' hξ) (T.ptRad_lt_one' hξ))]`.
-/
theorem ptEval_liftExt {ρ0 : Set.Ioo (0 : ℝ) 1} (hr : T.ptRad ξ ≤ ρ0) (z : L) {V : Γ}
    (hV : V ∈ T.int) :
    T.ptEval hξ hr (T.liftExt ρ0 z hV) = T.ptSharp hξ z * T.ptE hξ V := by
  rw [liftExt, ptEval_coe]
  show T.ptEvalB hξ (algebraMap Γ T.B (T.teich z * V)) = _
  rw [ptEvalB_algebraMap, T.ptE_teich_mul hξ z V
    (T.convergesAt_of_mem_int hV (T.ptRad_pos' hξ) (T.ptRad_lt_one' hξ))]

/- English proof (translation)
Establish `hr0` using `T.ptRad_pos' hξ`. Establish `hr1` using `T.ptRad_lt_one' hξ`. Establish `ht` using `T.tail_mem_int hY`. Establish `htc` using `T.convergesAt_of_mem_int ht hr0 hr1`. Establish `hc1 : ConvergesAt (T.zcoeff (T.teich (T.red Y))) (T.ptRad ξ)` using `T.convergesAt_teich _ _`.

Establish `hc2 : ConvergesAt (T.zcoeff (T.π * T.tail Y)) (T.ptRad ξ)` using `T.convergesAt_zcoeff_mul hr0 hr1 (T.convergesAt_π _) htc`. Establish `hYe` using `T.eq_teich_add_π_mul_tail Y`. Establish `e : T.ptE hξ Y = T.ptSharp hξ (T.red Y) + T.ptPi hξ * T.ptE hξ (T.tail Y)` using `by conv_lhs => rw [hYe]`. Rewrite using `[T.ptE_add hξ hc1 hc2, T.ptE_mul hξ (T.convergesAt_π _) htc, ptE_teich, ptE_π]`. Rewrite using `[e]`.

Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ ?_)` and prove the remaining obligations. Rewrite using `[norm_ptSharp]`. Rewrite using `[norm_mul, norm_ptPi]`. Establish `h1 : ‖T.ptE hξ (T.tail Y)‖ ≤ 1` using `(T.norm_ptE_le hξ htc).trans (T.gaussNorm_le_one_of_mem_int ht hr0 hr1.le)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_ptE_int_le {Y : Γ} (hY : Y ∈ T.int) :
    ‖T.ptE hξ Y‖ ≤ max ‖T.red Y‖ (T.ptRad ξ) := by
  have hr0 := T.ptRad_pos' hξ
  have hr1 := T.ptRad_lt_one' hξ
  have ht := T.tail_mem_int hY
  have htc := T.convergesAt_of_mem_int ht hr0 hr1
  have hc1 : ConvergesAt (T.zcoeff (T.teich (T.red Y))) (T.ptRad ξ) := T.convergesAt_teich _ _
  have hc2 : ConvergesAt (T.zcoeff (T.π * T.tail Y)) (T.ptRad ξ) :=
    T.convergesAt_zcoeff_mul hr0 hr1 (T.convergesAt_π _) htc
  have hYe := T.eq_teich_add_π_mul_tail Y
  have e : T.ptE hξ Y = T.ptSharp hξ (T.red Y) + T.ptPi hξ * T.ptE hξ (T.tail Y) := by
    conv_lhs => rw [hYe]
    rw [T.ptE_add hξ hc1 hc2, T.ptE_mul hξ (T.convergesAt_π _) htc, ptE_teich, ptE_π]
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ ?_)
  · rw [norm_ptSharp]
  · rw [norm_mul, norm_ptPi]
    have h1 : ‖T.ptE hξ (T.tail Y)‖ ≤ 1 :=
      (T.norm_ptE_le hξ htc).trans (T.gaussNorm_le_one_of_mem_int ht hr0 hr1.le)
    calc ‖T.coeff (ξ : Γ) 0‖ * ‖T.ptE hξ (T.tail Y)‖ ≤ ‖T.coeff (ξ : Γ) 0‖ * 1 :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = T.ptRad ξ := mul_one _

/- English proof (translation)
Distinguish the cases in `hw0 : w = 0`. Use `⟨0, 1, T.int.one_mem, by rw [map_one, norm_one], by rw [hw0, norm_zero, norm_zero], ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero, zero_mul, hw0]`. Take `⟨d, hd⟩` from `NormedField.exists_lt_norm L ‖w‖`. Establish `hd0 : d ≠ 0` using `by rintro rfl; rw [norm_zero] at hd; exact absurd hd (not_lt.2 (norm_nonneg _))`.

Establish `hsd : T.ptSharp hξ d ≠ 0` using `T.sharp_ne_zero hξ hd0`. Use `set w' := w / T.ptSharp hξ d with hw'`. Establish `hw'1 : ‖w'‖ ≤ 1`. Rewrite using `[hw', norm_div, norm_ptSharp, div_le_one (norm_pos_iff.2 hd0)]`. Conclude with `hd.le`.

Take `⟨z', hz', V, hV, hVe⟩` from `T.exists_lift_value hξ hw'1`. Establish `hr0` using `T.ptRad_pos' hξ`. Establish `hr1` using `T.ptRad_lt_one' hξ`. Establish `hVc` using `T.convergesAt_of_mem_int hV hr0 hr1`. Rewrite `hVe` using `[T.ptE_teich_mul hξ z' V hVc]`.

Establish `hw'0 : w' ≠ 0` using `div_ne_zero hw0 hsd`. Establish `hz'0 : z' ≠ 0`. Introduce and unpack `rfl`. Rewrite `hVe` using `[map_zero, zero_mul]`. Conclude with `hw'0 hVe.symm`.

Establish `hnV : ‖T.ptE hξ V‖ = 1`. Use `congrArg norm hVe` as an intermediate fact. Rewrite `this` using `[norm_mul, norm_ptSharp, hz']`. Establish `hpos : 0 < ‖w'‖` using `norm_pos_iff.2 hw'0`. Clear denominators, using `at this` for the nonvanishing conditions.

Use polynomial arithmetic with `[this]`. Establish `hred : ‖T.red V‖ = 1`. Use `le_antisymm (T.norm_red_le_one V hV) ?_` and prove the remaining obligations. Use `T.norm_ptE_int_le hξ hV` as an intermediate fact. Rewrite `this` using `[hnV]`.

Break down `le_max_iff.1 this with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd h (not_le.2 hr1)`. Use `⟨d * z', V, hV, hred, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[norm_mul, hz', hw', norm_div, norm_ptSharp]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[map_mul, mul_assoc, hVe, hw', mul_div_cancel₀ _ hsd]`.
-/
theorem exists_lift_value' (w : T.UntiltField hξ) :
    ∃ (z : L) (V : Γ) (hV : V ∈ T.int), ‖T.red V‖ = 1 ∧ ‖z‖ = ‖w‖ ∧
      T.ptSharp hξ z * T.ptE hξ V = w := by
  by_cases hw0 : w = 0
  · refine ⟨0, 1, T.int.one_mem, by rw [map_one, norm_one], by rw [hw0, norm_zero, norm_zero], ?_⟩
    rw [map_zero, zero_mul, hw0]
  obtain ⟨d, hd⟩ := NormedField.exists_lt_norm L ‖w‖
  have hd0 : d ≠ 0 := by rintro rfl; rw [norm_zero] at hd; exact absurd hd (not_lt.2 (norm_nonneg _))
  have hsd : T.ptSharp hξ d ≠ 0 := T.sharp_ne_zero hξ hd0
  set w' := w / T.ptSharp hξ d with hw'
  have hw'1 : ‖w'‖ ≤ 1 := by
    rw [hw', norm_div, norm_ptSharp, div_le_one (norm_pos_iff.2 hd0)]; exact hd.le
  obtain ⟨z', hz', V, hV, hVe⟩ := T.exists_lift_value hξ hw'1
  have hr0 := T.ptRad_pos' hξ
  have hr1 := T.ptRad_lt_one' hξ
  have hVc := T.convergesAt_of_mem_int hV hr0 hr1
  rw [T.ptE_teich_mul hξ z' V hVc] at hVe
  have hw'0 : w' ≠ 0 := div_ne_zero hw0 hsd
  have hz'0 : z' ≠ 0 := by
    rintro rfl; rw [map_zero, zero_mul] at hVe; exact hw'0 hVe.symm
  have hnV : ‖T.ptE hξ V‖ = 1 := by
    have := congrArg norm hVe
    rw [norm_mul, norm_ptSharp, hz'] at this
    have hpos : 0 < ‖w'‖ := norm_pos_iff.2 hw'0
    field_simp at this
    nlinarith [this]
  have hred : ‖T.red V‖ = 1 := by
    refine le_antisymm (T.norm_red_le_one V hV) ?_
    have := T.norm_ptE_int_le hξ hV
    rw [hnV] at this
    rcases le_max_iff.1 this with h | h
    · exact h
    · exact absurd h (not_le.2 hr1)
  refine ⟨d * z', V, hV, hred, ?_, ?_⟩
  · rw [norm_mul, hz', hw', norm_div, norm_ptSharp]
    field_simp
  · rw [map_mul, mul_assoc, hVe, hw', mul_div_cancel₀ _ hsd]

/- English proof (translation)
Use `T.prefixLe_π_pow_mul_teich 0 c n ((norm_nonneg c).trans hb) fun _ => hb` as an intermediate fact. Rewrite `this` using `[pow_zero, one_mul]`. Then use the resulting hypothesis.
-/
theorem prefixLe_teich' (c : L) (n : ℕ) {b : ℝ} (hb : ‖c‖ ≤ b) : T.PrefixLe (T.teich c) n b := by
  have := T.prefixLe_π_pow_mul_teich 0 c n ((norm_nonneg c).trans hb) fun _ => hb
  rwa [pow_zero, one_mul] at this

/- English proof (translation)
Establish `hr0` using `T.ptRad_pos' hξ`. Establish `hr1` using `T.ptRad_lt_one' hξ`. Use `set M := max ‖a‖ ‖b‖`. Establish `hM0 : 0 ≤ M` using `le_max_of_le_left (norm_nonneg _)`. Use `set D := T.teich a + T.teich b - T.teich (a + b) with hD`.

Establish `hDred : T.red D = 0` using `by simp [D, red_teich]`. Establish `hDe : D = T.π * T.tail D`. Use `T.sub_teich_eq_π_mul_tail D` as an intermediate fact. Rewrite `this` using `[hDred, T.teich_zero, sub_zero]`. Then use the resulting hypothesis. Establish `hpre : ∀ n, T.PrefixLe D n M` using `fun n => T.prefixLe_sub (T.prefixLe_add (T.prefixLe_teich' a n (le_max_left _ _)) (T.prefixLe_teich' b n (le_max_right _ _))) (T.prefixLe_teich' (a + b) n ((IsUltrametricDist.norm_add_le_max _ _).trans le_rfl))`.

Establish `htail : ∀ n, ‖T.coeff (T.tail D) n‖ ≤ M` using `fun n => by`. Rewrite using `[← coeff_succ]`. Conclude with `hpre (n + 1) (n + 1) le_rfl`. Establish `hbdd : T.IsBddElt (T.tail D)` using `T.isBddElt_of_le htail`. Establish `htc : ConvergesAt (T.zcoeff (T.tail D)) (T.ptRad ξ)` using `T.convergesAt_of_isBddElt hbdd hr0 hr1`.

Establish `hgn : gaussNorm (T.zcoeff (T.tail D)) (T.ptRad ξ) ≤ M`. Use `gaussNorm_le fun n => ?_` and prove the remaining obligations. Break down `lt_or_ge n 0 with hn | hn` into its components or cases. Rewrite using `[T.zcoeff_of_neg _ hn, norm_zero, zero_mul]`. Conclude with `hM0`.

Take `⟨k, rfl⟩` from `Int.eq_ofNat_of_zero_le hn`. Rewrite using `[T.zcoeff_natCast, zpow_natCast]`. Combine the equalities or inequalities in the displayed calculation. Establish `hc : ∀ c : L, ConvergesAt (T.zcoeff (T.teich c)) (T.ptRad ξ)` using `fun c => T.convergesAt_teich c _`. Establish `hval : T.ptE hξ D = T.ptSharp hξ a + T.ptSharp hξ b - T.ptSharp hξ (a + b)`.

Rewrite using `[hD, sub_eq_add_neg, T.ptE_add hξ (T.convergesAt_zcoeff_add hr0 hr1 (hc a) (hc b)) (T.convergesAt_zcoeff_neg hr0 hr1 (hc _)), T.ptE_add hξ (hc a) (hc b), T.ptE_neg hξ (hc _), ptE_teich, ptE_teich, ptE_teich, ← sub_eq_add_neg]`. Rewrite using `[← hval, hDe, T.ptE_mul hξ (T.convergesAt_π _) htc, ptE_π, norm_mul, norm_ptPi]`. Conclude with `mul_le_mul_of_nonneg_left ((T.norm_ptE_le hξ htc).trans hgn) (norm_nonneg _)`.
-/
theorem norm_sharp_add_sub_le (a b : L) :
    ‖T.ptSharp hξ a + T.ptSharp hξ b - T.ptSharp hξ (a + b)‖ ≤ T.ptRad ξ * max ‖a‖ ‖b‖ := by
  have hr0 := T.ptRad_pos' hξ
  have hr1 := T.ptRad_lt_one' hξ
  set M := max ‖a‖ ‖b‖
  have hM0 : 0 ≤ M := le_max_of_le_left (norm_nonneg _)
  set D := T.teich a + T.teich b - T.teich (a + b) with hD
  have hDred : T.red D = 0 := by simp [D, red_teich]
  have hDe : D = T.π * T.tail D := by
    have := T.sub_teich_eq_π_mul_tail D
    rwa [hDred, T.teich_zero, sub_zero] at this
  have hpre : ∀ n, T.PrefixLe D n M := fun n =>
    T.prefixLe_sub (T.prefixLe_add (T.prefixLe_teich' a n (le_max_left _ _))
      (T.prefixLe_teich' b n (le_max_right _ _)))
      (T.prefixLe_teich' (a + b) n ((IsUltrametricDist.norm_add_le_max _ _).trans le_rfl))
  have htail : ∀ n, ‖T.coeff (T.tail D) n‖ ≤ M := fun n => by
    rw [← coeff_succ]; exact hpre (n + 1) (n + 1) le_rfl
  have hbdd : T.IsBddElt (T.tail D) := T.isBddElt_of_le htail
  have htc : ConvergesAt (T.zcoeff (T.tail D)) (T.ptRad ξ) := T.convergesAt_of_isBddElt hbdd hr0 hr1
  have hgn : gaussNorm (T.zcoeff (T.tail D)) (T.ptRad ξ) ≤ M := by
    refine gaussNorm_le fun n => ?_
    rcases lt_or_ge n 0 with hn | hn
    · rw [T.zcoeff_of_neg _ hn, norm_zero, zero_mul]; exact hM0
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [T.zcoeff_natCast, zpow_natCast]
    calc ‖T.coeff (T.tail D) k‖ * T.ptRad ξ ^ k ≤ M * 1 :=
          mul_le_mul (htail k) (pow_le_one₀ hr0.le hr1.le) (by positivity) hM0
      _ = M := mul_one M
  have hc : ∀ c : L, ConvergesAt (T.zcoeff (T.teich c)) (T.ptRad ξ) := fun c => T.convergesAt_teich c _
  have hval : T.ptE hξ D = T.ptSharp hξ a + T.ptSharp hξ b - T.ptSharp hξ (a + b) := by
    rw [hD, sub_eq_add_neg, T.ptE_add hξ (T.convergesAt_zcoeff_add hr0 hr1 (hc a) (hc b))
      (T.convergesAt_zcoeff_neg hr0 hr1 (hc _)), T.ptE_add hξ (hc a) (hc b),
      T.ptE_neg hξ (hc _), ptE_teich, ptE_teich, ptE_teich, ← sub_eq_add_neg]
  rw [← hval, hDe, T.ptE_mul hξ (T.convergesAt_π _) htc, ptE_π, norm_mul, norm_ptPi]
  exact mul_le_mul_of_nonneg_left ((T.norm_ptE_le hξ htc).trans hgn) (norm_nonneg _)

/- English proof (translation)
Establish `hr0` using `T.ptRad_pos' hξ`. It suffices to establish `H : ‖∑ i ∈ s, a i‖ ≤ M ∧ ‖∑ i ∈ s, T.ptSharp hξ (a i) - T.ptSharp hξ (∑ i ∈ s, a i)‖ ≤ T.ptRad ξ * M from H.2`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [hM0, mul_nonneg hr0.le hM0]`. Consider the case `insert i s hi ih`.

Establish `ih'` using `ih fun j hj => hM j (Finset.mem_insert_of_mem hj)`. Establish `hai` using `hM i (Finset.mem_insert_self i s)`. Rewrite using `[Finset.sum_insert hi, Finset.sum_insert hi]`. Use `⟨(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hai ih'.1), ?_⟩` and prove the remaining obligations. Establish `e : T.ptSharp hξ (a i) + ∑ j ∈ s, T.ptSharp hξ (a j) - T.ptSharp hξ (a i + ∑ j ∈ s, a j) = (∑ j ∈ s, T.ptSharp hξ (a j) - T.ptSharp hξ (∑ j ∈ s, a j)) + (T.ptSharp hξ (a i) + T.ptSharp hξ (∑ j ∈ s, a j) - T.ptSharp hξ (a i + ∑ j ∈ s, a j))`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih'.2 ?_)` and prove the remaining obligations. Conclude with `(T.norm_sharp_add_sub_le hξ _ _).trans (mul_le_mul_of_nonneg_left (max_le hai ih'.1) hr0.le)`.
-/
theorem norm_sum_sharp_sub_le {ι : Type*} (s : Finset ι) (a : ι → L) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i ∈ s, ‖a i‖ ≤ M) :
    ‖∑ i ∈ s, T.ptSharp hξ (a i) - T.ptSharp hξ (∑ i ∈ s, a i)‖ ≤ T.ptRad ξ * M := by
  classical
  have hr0 := T.ptRad_pos' hξ
  suffices H : ‖∑ i ∈ s, a i‖ ≤ M ∧
      ‖∑ i ∈ s, T.ptSharp hξ (a i) - T.ptSharp hξ (∑ i ∈ s, a i)‖ ≤ T.ptRad ξ * M from H.2
  induction s using Finset.induction_on with
  | empty => simp [hM0, mul_nonneg hr0.le hM0]
  | insert i s hi ih =>
    have ih' := ih fun j hj => hM j (Finset.mem_insert_of_mem hj)
    have hai := hM i (Finset.mem_insert_self i s)
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    refine ⟨(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hai ih'.1), ?_⟩
    have e : T.ptSharp hξ (a i) + ∑ j ∈ s, T.ptSharp hξ (a j) - T.ptSharp hξ (a i + ∑ j ∈ s, a j) =
        (∑ j ∈ s, T.ptSharp hξ (a j) - T.ptSharp hξ (∑ j ∈ s, a j)) +
        (T.ptSharp hξ (a i) + T.ptSharp hξ (∑ j ∈ s, a j) - T.ptSharp hξ (a i + ∑ j ∈ s, a j)) := by
      ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih'.2 ?_)
    exact (T.norm_sharp_add_sub_le hξ _ _).trans
      (mul_le_mul_of_nonneg_left (max_le hai ih'.1) hr0.le)

include hξ in
/- English proof (translation)
Introduce `h`. Use `T.ptRad_le_extNorm_ξExt (ξ := ξ) (topRad ρ0)` as an intermediate fact. Rewrite `this` using `[h, extNorm_zero]`. Conclude with `absurd this (not_le.2 (T.ptRad_pos' hξ))`.
-/
theorem ξExt_ne_zero {ρ0 : Set.Ioo (0 : ℝ) 1} : T.ξExt ξ ρ0 ≠ 0 := by
  intro h
  have := T.ptRad_le_extNorm_ξExt (ξ := ξ) (topRad ρ0)
  rw [h, extNorm_zero] at this
  exact absurd this (not_le.2 (T.ptRad_pos' hξ))

include hξ in

/- English proof (translation)
Take `⟨h1, h2⟩` from `T.idx_coe (b := ⟨algebraMap Γ T.B ξ, T.algebraMap_ξ_mem_Econ (ξ := ξ) ρ0⟩) (T.ξExt_ne_zero hξ) ⟨T.ptRad_pos' hξ, hr⟩`. Establish `e : T.coeffB ((⟨algebraMap Γ T.B ξ, T.algebraMap_ξ_mem_Econ (ξ` using `ξ) ρ0⟩ : T.Econ ρ0) : T.B) = T.zcoeff (ξ : Γ) := T.coeffB_algebraMap _`. Rewrite `h1`, `h2` using `[e]`. Take `⟨h3, h4⟩` from `T.idx_prim_self hξ`. Conclude with `⟨h1.trans h3, h2.trans h4⟩`.
-/
theorem idx_ξExt {ρ0 : Set.Ioo (0 : ℝ) 1} (hr : T.ptRad ξ < ρ0) :
    T.lowIdx (T.ξExt ξ ρ0) (T.ptRad ξ) = 0 ∧ T.highIdx (T.ξExt ξ ρ0) (T.ptRad ξ) = 1 := by
  obtain ⟨h1, h2⟩ := T.idx_coe (b := ⟨algebraMap Γ T.B ξ, T.algebraMap_ξ_mem_Econ (ξ := ξ) ρ0⟩)
    (T.ξExt_ne_zero hξ) ⟨T.ptRad_pos' hξ, hr⟩
  have e : T.coeffB ((⟨algebraMap Γ T.B ξ, T.algebraMap_ξ_mem_Econ (ξ := ξ) ρ0⟩ : T.Econ ρ0) : T.B) =
      T.zcoeff (ξ : Γ) := T.coeffB_algebraMap _
  rw [e] at h1 h2
  obtain ⟨h3, h4⟩ := T.idx_prim_self hξ
  exact ⟨h1.trans h3, h2.trans h4⟩

include hξ in

/- English proof (translation)
Rewrite using `[mult, (T.idx_ξExt hξ hr).1, (T.idx_ξExt hξ hr).2]`. Both sides reduce to the same expression.
-/
theorem mult_ξExt {ρ0 : Set.Ioo (0 : ℝ) 1} (hr : T.ptRad ξ < ρ0) :
    T.mult (T.ξExt ξ ρ0) (T.ptRad ξ) = 1 := by
  rw [mult, (T.idx_ξExt hξ hr).1, (T.idx_ξExt hξ hr).2]; rfl

section Taylor

variable {ρ0 : Set.Ioo (0 : ℝ) 1}

include hξ in
/- English proof (translation)
Rewrite using `[ξExt, extNorm_coe]`. Use `show gaussNorm (T.coeffB (algebraMap Γ T.B ξ)) σ = _`. Rewrite using `[coeffB_algebraMap, T.gaussNorm_prim hξ (rad_pos ρ0 σ) (rad_lt_one ρ0 σ)]`. Both sides reduce to the same expression.
-/
theorem extNorm_ξExt (σ : Set.Ioc (0 : ℝ) ρ0) :
    T.extNorm ρ0 σ (T.ξExt ξ ρ0) = max (T.ptRad ξ) σ := by
  rw [ξExt, extNorm_coe]
  show gaussNorm (T.coeffB (algebraMap Γ T.B ξ)) σ = _
  rw [coeffB_algebraMap, T.gaussNorm_prim hξ (rad_pos ρ0 σ) (rad_lt_one ρ0 σ)]
  rfl

variable (hr : T.ptRad ξ ≤ ρ0)

structure DivStep (y : T.RobbaExt ρ0) where

  z : L

  V : Γ
  hV : V ∈ T.int
  hred : ‖T.red V‖ = 1
  hz : ‖z‖ = ‖T.ptEval hξ hr y‖
  hval : T.ptSharp hξ z * T.ptE hξ V = T.ptEval hξ hr y

  next : T.RobbaExt ρ0
  eq : y = T.liftExt ρ0 z hV + T.ξExt ξ ρ0 * next

/- English proof (translation)
Take `⟨z, V, hV, hred, hz, hval⟩` from `T.exists_lift_value' hξ (T.ptEval hξ hr y)`. Establish `h0 : T.ptEval hξ hr (y - T.liftExt ρ0 z hV) = 0`. Rewrite using `[map_sub, T.ptEval_liftExt hξ hr z hV, hval, sub_self]`. Take `⟨y', hy'⟩` from `(T.ptEval_eq_zero_iff hξ hr _).1 h0`. Conclude with `⟨⟨z, V, hV, hred, hz, hval, y', by rw [← hy']; ring⟩⟩`.
-/
theorem nonempty_divStep (y : T.RobbaExt ρ0) : Nonempty (T.DivStep hξ hr y) := by
  obtain ⟨z, V, hV, hred, hz, hval⟩ := T.exists_lift_value' hξ (T.ptEval hξ hr y)
  have h0 : T.ptEval hξ hr (y - T.liftExt ρ0 z hV) = 0 := by
    rw [map_sub, T.ptEval_liftExt hξ hr z hV, hval, sub_self]
  obtain ⟨y', hy'⟩ := (T.ptEval_eq_zero_iff hξ hr _).1 h0
  exact ⟨⟨z, V, hV, hred, hz, hval, y', by rw [← hy']; ring⟩⟩

def divStep (y : T.RobbaExt ρ0) : T.DivStep hξ hr y := Classical.choice (T.nonempty_divStep hξ hr y)

def tay (x : T.RobbaExt ρ0) : ℕ → T.RobbaExt ρ0
  | 0 => x
  | j + 1 => (T.divStep hξ hr (tay x j)).next

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tay_zero (x : T.RobbaExt ρ0) : T.tay hξ hr x 0 = x := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tay_succ (x : T.RobbaExt ρ0) (j : ℕ) :
    T.tay hξ hr x (j + 1) = (T.divStep hξ hr (T.tay hξ hr x j)).next := rfl

/- English proof (translation)
Proceed by induction on `J with`. Consider the case `zero`. Simplify using `only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul, pow_one, tay_succ]`. Conclude with `(T.divStep hξ hr (T.tay hξ hr x 0)).eq`. Consider the case `succ J ih`.

Rewrite using `[Finset.sum_range_succ, T.tay_succ hξ hr x (J + 1)]`. Establish `e` using `(T.divStep hξ hr (T.tay hξ hr x (J + 1))).eq`. Use `conv_lhs => rw [ih]`. Use `conv_lhs => rw [e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem taylor_eq (x : T.RobbaExt ρ0) (J : ℕ) :
    x = ∑ j ∈ Finset.range (J + 1), T.ξExt ξ ρ0 ^ j *
        T.liftExt ρ0 (T.divStep hξ hr (T.tay hξ hr x j)).z (T.divStep hξ hr (T.tay hξ hr x j)).hV +
      T.ξExt ξ ρ0 ^ (J + 1) * T.tay hξ hr x (J + 1) := by
  induction J with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul, pow_one,
      tay_succ]
    exact (T.divStep hξ hr (T.tay hξ hr x 0)).eq
  | succ J ih =>
    rw [Finset.sum_range_succ, T.tay_succ hξ hr x (J + 1)]
    have e := (T.divStep hξ hr (T.tay hξ hr x (J + 1))).eq
    conv_lhs => rw [ih]
    conv_lhs => rw [e]
    ring

variable {hξ hr}

/- English proof (translation)
The claim follows from `T.norm_ptEval_le hξ hr y`.
-/
theorem norm_ptEval_le_r (y : T.RobbaExt ρ0) :
    ‖T.ptEval hξ hr y‖ ≤ T.extNorm ρ0 (T.ptRadIoc hξ hr) y := T.norm_ptEval_le hξ hr y

/- English proof (translation)
Establish `e : y - T.liftExt ρ0 (T.divStep hξ hr y).z (T.divStep hξ hr y).hV = T.ξExt ξ ρ0 * (T.divStep hξ hr y).next` using `sub_eq_iff_eq_add'.2 (T.divStep hξ hr y).eq`. Rewrite using `[e, extNorm_mul, T.extNorm_ξExt hξ]`.
-/
theorem extNorm_next (y : T.RobbaExt ρ0) (σ : Set.Ioc (0 : ℝ) ρ0) :
    T.extNorm ρ0 σ (y - T.liftExt ρ0 (T.divStep hξ hr y).z (T.divStep hξ hr y).hV) =
      max (T.ptRad ξ) σ * T.extNorm ρ0 σ (T.divStep hξ hr y).next := by
  have e : y - T.liftExt ρ0 (T.divStep hξ hr y).z (T.divStep hξ hr y).hV =
      T.ξExt ξ ρ0 * (T.divStep hξ hr y).next := sub_eq_iff_eq_add'.2 (T.divStep hξ hr y).eq
  rw [e, extNorm_mul, T.extNorm_ξExt hξ]

/- English proof (translation)
Establish `h` using `T.extNorm_next (hξ := hξ) (hr := hr) y (T.ptRadIoc hξ hr)`. Rewrite `h` using `[show ((T.ptRadIoc hξ hr : Set.Ioc (0 : ℝ) ρ0) : ℝ) = T.ptRad ξ from rfl, max_self]`. Rewrite using `[← h, sub_eq_add_neg]`. Use `(T.extNorm_add_le _ _ _).trans (max_le le_rfl ?_)` and prove the remaining obligations. Rewrite using `[extNorm_neg, T.extNorm_liftExt _ _ (T.divStep hξ hr y).hred, (T.divStep hξ hr y).hz]`.

Conclude with `T.norm_ptEval_le hξ hr y`.
-/
theorem extNorm_next_le (y : T.RobbaExt ρ0) :
    T.ptRad ξ * T.extNorm ρ0 (T.ptRadIoc hξ hr) (T.divStep hξ hr y).next ≤
      T.extNorm ρ0 (T.ptRadIoc hξ hr) y := by
  have h := T.extNorm_next (hξ := hξ) (hr := hr) y (T.ptRadIoc hξ hr)
  rw [show ((T.ptRadIoc hξ hr : Set.Ioc (0 : ℝ) ρ0) : ℝ) = T.ptRad ξ from rfl, max_self] at h
  rw [← h, sub_eq_add_neg]
  refine (T.extNorm_add_le _ _ _).trans (max_le le_rfl ?_)
  rw [extNorm_neg, T.extNorm_liftExt _ _ (T.divStep hξ hr y).hred, (T.divStep hξ hr y).hz]
  exact T.norm_ptEval_le hξ hr y

/- English proof (translation)
Establish `h` using `T.extNorm_next (hξ := hξ) (hr := hr) y (T.ptRadIoc hξ hr)`. Rewrite `h` using `[show ((T.ptRadIoc hξ hr : Set.Ioc (0 : ℝ) ρ0) : ℝ) = T.ptRad ξ from rfl, max_self]`. Rewrite using `[← h]`. Use `T.extNorm_eq_of_lt ?_` and prove the remaining obligations. Rewrite using `[sub_sub_cancel, T.extNorm_liftExt _ _ (T.divStep hξ hr y).hred, (T.divStep hξ hr y).hz]`.

Conclude with `hlt`.
-/
theorem extNorm_next_eq (y : T.RobbaExt ρ0)
    (hlt : ‖T.ptEval hξ hr y‖ < T.extNorm ρ0 (T.ptRadIoc hξ hr) y) :
    T.ptRad ξ * T.extNorm ρ0 (T.ptRadIoc hξ hr) (T.divStep hξ hr y).next =
      T.extNorm ρ0 (T.ptRadIoc hξ hr) y := by
  have h := T.extNorm_next (hξ := hξ) (hr := hr) y (T.ptRadIoc hξ hr)
  rw [show ((T.ptRadIoc hξ hr : Set.Ioc (0 : ℝ) ρ0) : ℝ) = T.ptRad ξ from rfl, max_self] at h
  rw [← h]
  refine T.extNorm_eq_of_lt ?_
  rw [sub_sub_cancel, T.extNorm_liftExt _ _ (T.divStep hξ hr y).hred, (T.divStep hξ hr y).hz]
  exact hlt

end Taylor

section NonDeg

variable {ρ0 : Set.Ioo (0 : ℝ) 1} (hr : T.ptRad ξ < ρ0)

/- English proof (translation)
Establish `hr0` using `T.ptRad_pos' hξ`. Use `set a : Set.Ioc (0 : ℝ) ρ0 := T.ptRadIoc hξ hr.le`. Use `set b : Set.Ioc (0 : ℝ) ρ0 := ⟨(T.ptRad ξ + ρ0) / 2, by linarith, by linarith⟩`. Establish `hab : (a : ℝ) ≤ b` using `by show T.ptRad ξ ≤ (T.ptRad ξ + ρ0) / 2; linarith`. Establish `hcont` using `T.continuousOn_normR y a b`.

Establish `hmem : (a : ℝ) ∈ Set.Icc (a : ℝ) b` using `⟨le_rfl, hab⟩`. Establish `hca : c < T.normR y a` using `by rw [T.normR_eq]; exact hc`. Take `⟨δ, hδ, hδ'⟩` from `Metric.continuousWithinAt_iff.1 (hcont a hmem) (T.normR y a - c) (by linarith)`. Use `⟨min (δ / 2) ((ρ0 - T.ptRad ξ) / 2), lt_min (by linarith) (by linarith), by linarith [min_le_right (δ / 2) ((ρ0 - T.ptRad ξ) / 2)], fun σ h1 h2 => ?_⟩` and prove the remaining obligations. Establish `hσ : (σ : ℝ) ∈ Set.Icc (a : ℝ) b` using `⟨h1, by show (σ : ℝ) ≤ (T.ptRad ξ + ρ0) / 2; linarith [min_le_right (δ / 2) ((ρ0 - T.ptRad ξ) / 2)]⟩`.

Establish `hd : dist (σ : ℝ) a < δ`. Rewrite using `[Real.dist_eq, abs_of_nonneg (by show (0:ℝ) ≤ σ - T.ptRad ξ; linarith)]`. Use `show (σ : ℝ) - T.ptRad ξ < δ`. Combine the linear relations using `[min_le_left (δ / 2) ((ρ0 - T.ptRad ξ) / 2)]`. Use `hδ' hσ hd` as an intermediate fact.

Rewrite `this` using `[Real.dist_eq, T.normR_eq y σ]`. Use `neg_abs_le (T.extNorm ρ0 σ y - T.normR y a)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_nbhd_gt {y : T.RobbaExt ρ0} {c : ℝ}
    (hc : c < T.extNorm ρ0 (T.ptRadIoc hξ hr.le) y) :
    ∃ η > 0, T.ptRad ξ + η ≤ ρ0 ∧ ∀ σ : Set.Ioc (0 : ℝ) ρ0, T.ptRad ξ ≤ σ →
      (σ : ℝ) ≤ T.ptRad ξ + η → c < T.extNorm ρ0 σ y := by
  have hr0 := T.ptRad_pos' hξ
  set a : Set.Ioc (0 : ℝ) ρ0 := T.ptRadIoc hξ hr.le
  set b : Set.Ioc (0 : ℝ) ρ0 := ⟨(T.ptRad ξ + ρ0) / 2, by linarith, by linarith⟩
  have hab : (a : ℝ) ≤ b := by show T.ptRad ξ ≤ (T.ptRad ξ + ρ0) / 2; linarith
  have hcont := T.continuousOn_normR y a b
  have hmem : (a : ℝ) ∈ Set.Icc (a : ℝ) b := ⟨le_rfl, hab⟩
  have hca : c < T.normR y a := by rw [T.normR_eq]; exact hc
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.1 (hcont a hmem) (T.normR y a - c)
    (by linarith)
  refine ⟨min (δ / 2) ((ρ0 - T.ptRad ξ) / 2), lt_min (by linarith) (by linarith),
    by linarith [min_le_right (δ / 2) ((ρ0 - T.ptRad ξ) / 2)], fun σ h1 h2 => ?_⟩
  have hσ : (σ : ℝ) ∈ Set.Icc (a : ℝ) b :=
    ⟨h1, by show (σ : ℝ) ≤ (T.ptRad ξ + ρ0) / 2; linarith [min_le_right (δ / 2) ((ρ0 - T.ptRad ξ) / 2)]⟩
  have hd : dist (σ : ℝ) a < δ := by
    rw [Real.dist_eq, abs_of_nonneg (by show (0:ℝ) ≤ σ - T.ptRad ξ; linarith)]
    show (σ : ℝ) - T.ptRad ξ < δ
    linarith [min_le_left (δ / 2) ((ρ0 - T.ptRad ξ) / 2)]
  have := hδ' hσ hd
  rw [Real.dist_eq, T.normR_eq y σ] at this
  have := neg_abs_le (T.extNorm ρ0 σ y - T.normR y a)
  linarith

/- English proof (translation)
Use `set D := T.divStep hξ hr.le y`. Establish `hlift : ∀ σ, T.extNorm ρ0 σ (T.liftExt ρ0 D.z D.hV) = ‖T.ptEval hξ hr.le y‖` using `fun σ => by`. Rewrite using `[T.extNorm_liftExt _ _ D.hred, D.hz]`. Establish `e : y - T.liftExt ρ0 D.z D.hV = T.ξExt ξ ρ0 * D.next` using `sub_eq_iff_eq_add'.2 D.eq`. Establish `hnext : D.next ≠ 0`.

Introduce `h0`. Establish `hyl : y = T.liftExt ρ0 D.z D.hV` using `by rw [← sub_eq_zero, e, h0, mul_zero]`. Establish `h3` using `hlift (T.ptRadIoc hξ hr.le)`. Rewrite `h3` using `[← hyl]`. Rewrite `hlt` using `[h3]`.

Conclude with `lt_irrefl _ hlt`. Use `⟨hnext, ?_⟩` and prove the remaining obligations. Take `⟨η, hη, hηle, hηgt⟩` from `T.exists_nbhd_gt (hξ := hξ) hr hlt`. Establish `hh : 0 < T.ptRad ξ ∧ T.ptRad ξ < ρ0` using `⟨T.ptRad_pos' hξ, hr⟩`. Take `⟨h1, h2⟩` from `T.idx_eq_of_near hy hh hη hηle (y' := y - T.liftExt ρ0 D.z D.hV) fun σ hσ1 hσ2 => by`.

Rewrite using `[sub_sub_cancel, hlift]`. Conclude with `hηgt σ hσ1 hσ2`. Establish `hm1 : T.mult y (T.ptRad ξ) = T.mult (y - T.liftExt ρ0 D.z D.hV) (T.ptRad ξ)`. Rewrite using `[mult, mult, h1, h2]`. Rewrite using `[hm1, e, T.mult_mul (T.ξExt_ne_zero hξ) hnext hh, T.mult_ξExt hξ hr]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem mult_next {y : T.RobbaExt ρ0} (hy : y ≠ 0)
    (hlt : ‖T.ptEval hξ hr.le y‖ < T.extNorm ρ0 (T.ptRadIoc hξ hr.le) y) :
    (T.divStep hξ hr.le y).next ≠ 0 ∧
      T.mult (T.divStep hξ hr.le y).next (T.ptRad ξ) = T.mult y (T.ptRad ξ) - 1 := by
  set D := T.divStep hξ hr.le y
  have hlift : ∀ σ, T.extNorm ρ0 σ (T.liftExt ρ0 D.z D.hV) = ‖T.ptEval hξ hr.le y‖ := fun σ => by
    rw [T.extNorm_liftExt _ _ D.hred, D.hz]
  have e : y - T.liftExt ρ0 D.z D.hV = T.ξExt ξ ρ0 * D.next := sub_eq_iff_eq_add'.2 D.eq
  have hnext : D.next ≠ 0 := by
    intro h0
    have hyl : y = T.liftExt ρ0 D.z D.hV := by rw [← sub_eq_zero, e, h0, mul_zero]
    have h3 := hlift (T.ptRadIoc hξ hr.le)
    rw [← hyl] at h3
    rw [h3] at hlt
    exact lt_irrefl _ hlt
  refine ⟨hnext, ?_⟩
  obtain ⟨η, hη, hηle, hηgt⟩ := T.exists_nbhd_gt (hξ := hξ) hr hlt
  have hh : 0 < T.ptRad ξ ∧ T.ptRad ξ < ρ0 := ⟨T.ptRad_pos' hξ, hr⟩
  obtain ⟨h1, h2⟩ := T.idx_eq_of_near hy hh hη hηle (y' := y - T.liftExt ρ0 D.z D.hV)
    fun σ hσ1 hσ2 => by
      rw [sub_sub_cancel, hlift]
      exact hηgt σ hσ1 hσ2
  have hm1 : T.mult y (T.ptRad ξ) = T.mult (y - T.liftExt ρ0 D.z D.hV) (T.ptRad ξ) := by
    rw [mult, mult, h1, h2]
  rw [hm1, e, T.mult_mul (T.ξExt_ne_zero hξ) hnext hh, T.mult_ξExt hξ hr]
  ring

/- English proof (translation)
Use `set N := fun j => T.extNorm ρ0 (T.ptRadIoc hξ hr.le) (T.tay hξ hr.le x j)`. Use `set v := fun j => ‖T.ptEval hξ hr.le (T.tay hξ hr.le x j)‖`. Establish `hle : ∀ j, v j ≤ N j` using `fun j => T.norm_ptEval_le hξ hr.le _`. Establish `hind : ∀ J, (∀ j < J, v j < N j) → ∀ j ≤ J, T.tay hξ hr.le x j ≠ 0 ∧ T.mult (T.tay hξ hr.le x j) (T.ptRad ξ) = T.mult x (T.ptRad ξ) - j ∧ T.ptRad ξ ^ j * N j = N 0`. Introduce `J hJ j hj`.

Proceed by induction on `j with`. Consider the case `zero => exact ⟨hx, by simp [tay_zero], by simp [N]⟩`. Consider the case `succ j ih`. Take `⟨h0, hm, hn⟩` from `ih (by omega)`. Establish `hlt` using `hJ j (by omega)`.

Take `⟨h0', hm'⟩` from `T.mult_next (hξ := hξ) hr h0 hlt`. Use `⟨by rw [tay_succ]; exact h0', by rw [tay_succ, hm', hm]; push_cast; ring, ?_⟩` and prove the remaining obligations. Use `T.extNorm_next_eq (hξ := hξ) (hr := hr.le) _ hlt` as an intermediate fact. Rewrite using `[← hn, pow_succ]`. Simplify using `only [N, tay_succ]`.

Rewrite using `[mul_assoc, this]`. Establish `hex : ∃ J, ¬ (v J < N J)`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Use `set M := (T.mult x (T.ptRad ξ)).toNat`.

Take `⟨-, hm, -⟩` from `hind (M + 1) (fun j _ => hcon j) (M + 1) le_rfl`. Use `T.mult_nonneg (T.tay hξ hr.le x (M + 1)) (T.ptRad ξ)` as an intermediate fact. Establish `hM : (M : ℤ) = T.mult x (T.ptRad ξ)` using `Int.toNat_of_nonneg (T.mult_nonneg x _)`. Rewrite `this` using `[hm]`. Move the coercions through the operations in `at this`.

Use linear arithmetic over natural numbers and integers. Use `set J := Nat.find hex`. Establish `hJmin : ∀ j < J, v j < N j` using `fun j hj => by`. Use `Nat.find_min hex hj` as an intermediate fact. Use `push_neg at this`.

Conclude with `this`. Establish `hJ` using `Nat.find_spec hex`. Take `⟨-, hmJ, -⟩` from `hind J hJmin J le_rfl`. Use `⟨J, ?_, fun j hj => ⟨(hind J hJmin j hj).1, (hind J hJmin j hj).2.2⟩, hJmin, le_antisymm (hle J) (not_lt.1 hJ)⟩` and prove the remaining obligations. Use `T.mult_nonneg (T.tay hξ hr.le x J) (T.ptRad ξ)` as an intermediate fact.

Rewrite `this` using `[hmJ]`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_nondeg {x : T.RobbaExt ρ0} (hx : x ≠ 0) :
    ∃ J : ℕ, (J : ℤ) ≤ T.mult x (T.ptRad ξ) ∧
      (∀ j ≤ J, T.tay hξ hr.le x j ≠ 0 ∧
        T.ptRad ξ ^ j * T.extNorm ρ0 (T.ptRadIoc hξ hr.le) (T.tay hξ hr.le x j) =
          T.extNorm ρ0 (T.ptRadIoc hξ hr.le) x) ∧
      (∀ j < J, ‖T.ptEval hξ hr.le (T.tay hξ hr.le x j)‖ <
        T.extNorm ρ0 (T.ptRadIoc hξ hr.le) (T.tay hξ hr.le x j)) ∧
      ‖T.ptEval hξ hr.le (T.tay hξ hr.le x J)‖ =
        T.extNorm ρ0 (T.ptRadIoc hξ hr.le) (T.tay hξ hr.le x J) := by
  classical
  set N := fun j => T.extNorm ρ0 (T.ptRadIoc hξ hr.le) (T.tay hξ hr.le x j)
  set v := fun j => ‖T.ptEval hξ hr.le (T.tay hξ hr.le x j)‖
  have hle : ∀ j, v j ≤ N j := fun j => T.norm_ptEval_le hξ hr.le _

  have hind : ∀ J, (∀ j < J, v j < N j) → ∀ j ≤ J, T.tay hξ hr.le x j ≠ 0 ∧
      T.mult (T.tay hξ hr.le x j) (T.ptRad ξ) = T.mult x (T.ptRad ξ) - j ∧
      T.ptRad ξ ^ j * N j = N 0 := by
    intro J hJ j hj
    induction j with
    | zero => exact ⟨hx, by simp [tay_zero], by simp [N]⟩
    | succ j ih =>
      obtain ⟨h0, hm, hn⟩ := ih (by omega)
      have hlt := hJ j (by omega)
      obtain ⟨h0', hm'⟩ := T.mult_next (hξ := hξ) hr h0 hlt
      refine ⟨by rw [tay_succ]; exact h0', by rw [tay_succ, hm', hm]; push_cast; ring, ?_⟩
      have := T.extNorm_next_eq (hξ := hξ) (hr := hr.le) _ hlt
      rw [← hn, pow_succ]
      simp only [N, tay_succ]
      rw [mul_assoc, this]
  have hex : ∃ J, ¬ (v J < N J) := by
    by_contra hcon
    push_neg at hcon
    set M := (T.mult x (T.ptRad ξ)).toNat
    obtain ⟨-, hm, -⟩ := hind (M + 1) (fun j _ => hcon j) (M + 1) le_rfl
    have := T.mult_nonneg (T.tay hξ hr.le x (M + 1)) (T.ptRad ξ)
    have hM : (M : ℤ) = T.mult x (T.ptRad ξ) := Int.toNat_of_nonneg (T.mult_nonneg x _)
    rw [hm] at this
    push_cast at this
    omega
  set J := Nat.find hex
  have hJmin : ∀ j < J, v j < N j := fun j hj => by
    have := Nat.find_min hex hj; push_neg at this; exact this
  have hJ := Nat.find_spec hex
  obtain ⟨-, hmJ, -⟩ := hind J hJmin J le_rfl
  refine ⟨J, ?_, fun j hj => ⟨(hind J hJmin j hj).1, (hind J hJmin j hj).2.2⟩, hJmin,
    le_antisymm (hle J) (not_lt.1 hJ)⟩
  have := T.mult_nonneg (T.tay hξ hr.le x J) (T.ptRad ξ)
  rw [hmJ] at this
  omega

end NonDeg

section Move

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg]; exact h.ne'), norm_neg, max_eq_left h.le]`.
-/
theorem ultra_norm_sub_eq_left {E : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E]
    {a b : E} (h : ‖b‖ < ‖a‖) : ‖a - b‖ = ‖a‖ := by
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg]; exact h.ne'),
    norm_neg, max_eq_left h.le]

include hξ in
/- English proof (translation)
The claim follows from `(hs.trans (T.ptRad_lt_one' hξ)).le`.
-/
theorem norm_teich_le_one_of_lt {s : L} (hs : ‖s‖ < T.ptRad ξ) : ‖s‖ ≤ 1 :=
  (hs.trans (T.ptRad_lt_one' hξ)).le

include hξ in

def movePt {s : L} (hs : ‖s‖ < T.ptRad ξ) : T.int := ξ - T.teichInt (T.norm_teich_le_one_of_lt hξ hs)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_movePt {s : L} (hs : ‖s‖ < T.ptRad ξ) : (T.movePt hξ hs : Γ) = ξ - T.teich s := rfl

/- English proof (translation)
Rewrite using `[coe_movePt, coeff_zero, coeff_zero, map_sub, red_teich]`.
-/
theorem coeff_zero_movePt {s : L} (hs : ‖s‖ < T.ptRad ξ) :
    T.coeff (T.movePt hξ hs : Γ) 0 = T.coeff (ξ : Γ) 0 - s := by
  rw [coe_movePt, coeff_zero, coeff_zero, map_sub, red_teich]

/- English proof (translation)
Use `show ‖T.coeff (T.movePt hξ hs : Γ) 0‖ = ‖T.coeff (ξ : Γ) 0‖`. Rewrite using `[coeff_zero_movePt]`. Conclude with `ultra_norm_sub_eq_left hs`.
-/
theorem ptRad_movePt {s : L} (hs : ‖s‖ < T.ptRad ξ) : T.ptRad (T.movePt hξ hs) = T.ptRad ξ := by
  show ‖T.coeff (T.movePt hξ hs : Γ) 0‖ = ‖T.coeff (ξ : Γ) 0‖
  rw [coeff_zero_movePt]
  exact ultra_norm_sub_eq_left hs

/- English proof (translation)
Introduce `h0`. Use `T.ptRad_movePt hξ hs` as an intermediate fact. Rewrite `this` using `[ptRad, h0, norm_zero]`. Conclude with `(T.ptRad_pos' hξ).ne this`. Use `norm_coeff_zero_lt := by`.

Use `T.ptRad_movePt hξ hs` as an intermediate fact. Rewrite `this` using `[ptRad]`. Rewrite using `[this]`. Conclude with `T.ptRad_lt_one' hξ`. Use `norm_coeff_one := by`.

Establish `hs1 : ‖s‖ < 1` using `hs.trans (T.ptRad_lt_one' hξ)`. Establish `hx : T.PrefixLe (ξ : Γ) 1 1` using `fun m _ => T.mem_int_iff.1 ξ.2 m`. Establish `hy : T.PrefixLe (-T.teich s) 1 ‖s‖` using `T.prefixLe_neg (T.prefixLe_teich' s 1 le_rfl)`. Establish `h` using `T.norm_coeff_add_sub_le 1 (norm_nonneg s) hs1.le hx hy 1 le_rfl`. Rewrite `h` using `[Real.one_rpow, one_mul, ← sub_eq_add_neg]`.

Take `⟨ht0, -⟩` from `coeffHolderExp_pos_le_one (p := p) 1`. Establish `hlt : ‖s‖ ^ coeffHolderExp p 1 < 1` using `Real.rpow_lt_one (norm_nonneg _) hs1 ht0`. Establish `e1 : ‖T.coeff (ξ : Γ) 1‖ = 1` using `hξ.norm_coeff_one`. Rewrite using `[coe_movePt]`. Use `ultra_norm_sub_eq_left (a := T.coeff (ξ : Γ) 1) (b := T.coeff (ξ : Γ) 1 - T.coeff ((ξ : Γ) - T.teich s) 1) (by` as an intermediate fact.

Rewrite using `[norm_sub_rev, e1]`. Conclude with `h.trans_lt hlt)`. Rewrite `this` using `[sub_sub_cancel, e1]`. Conclude with `this`.
-/
theorem isPrimOne_movePt {s : L} (hs : ‖s‖ < T.ptRad ξ) : T.IsPrimOne (T.movePt hξ hs) where
  coeff_zero_ne := by
    intro h0
    have := T.ptRad_movePt hξ hs
    rw [ptRad, h0, norm_zero] at this
    exact (T.ptRad_pos' hξ).ne this
  norm_coeff_zero_lt := by
    have := T.ptRad_movePt hξ hs
    rw [ptRad] at this
    rw [this]; exact T.ptRad_lt_one' hξ
  norm_coeff_one := by
    have hs1 : ‖s‖ < 1 := hs.trans (T.ptRad_lt_one' hξ)
    have hx : T.PrefixLe (ξ : Γ) 1 1 := fun m _ => T.mem_int_iff.1 ξ.2 m
    have hy : T.PrefixLe (-T.teich s) 1 ‖s‖ := T.prefixLe_neg (T.prefixLe_teich' s 1 le_rfl)
    have h := T.norm_coeff_add_sub_le 1 (norm_nonneg s) hs1.le hx hy 1 le_rfl
    rw [Real.one_rpow, one_mul, ← sub_eq_add_neg] at h
    obtain ⟨ht0, -⟩ := coeffHolderExp_pos_le_one (p := p) 1
    have hlt : ‖s‖ ^ coeffHolderExp p 1 < 1 := Real.rpow_lt_one (norm_nonneg _) hs1 ht0
    have e1 : ‖T.coeff (ξ : Γ) 1‖ = 1 := hξ.norm_coeff_one
    rw [coe_movePt]
    have := ultra_norm_sub_eq_left (a := T.coeff (ξ : Γ) 1)
      (b := T.coeff (ξ : Γ) 1 - T.coeff ((ξ : Γ) - T.teich s) 1) (by
        rw [norm_sub_rev, e1]; exact h.trans_lt hlt)
    rw [sub_sub_cancel, e1] at this
    exact this

/- English proof (translation)
Rewrite using `[ptEval_coe]`. Conclude with `T.ptEvalB_algebraMap hη X`.
-/
theorem ptEval_coe_algebraMap {η : T.int} (hη : T.IsPrimOne η) {ρ0 : Set.Ioo (0 : ℝ) 1}
    (hr : T.ptRad η ≤ ρ0) {X : Γ} (hX : algebraMap Γ T.B X ∈ T.Econ ρ0) :
    T.ptEval hη hr ((⟨algebraMap Γ T.B X, hX⟩ : T.Econ ρ0) : T.RobbaExt ρ0) = T.ptE hη X := by
  rw [ptEval_coe]
  exact T.ptEvalB_algebraMap hη X

/- English proof (translation)
Use `set hη := T.isPrimOne_movePt hξ hs`. Rewrite using `[ξExt, T.ptEval_coe_algebraMap hη hr]`. Establish `hr0` using `T.ptRad_pos' hη`. Establish `hr1` using `T.ptRad_lt_one' hη`. Establish `e : (ξ : Γ) = (T.movePt hξ hs : Γ) + T.teich s` using `by rw [coe_movePt]; ring`.

Rewrite using `[e, T.ptE_add hη (T.convergesAt_of_mem_int (T.movePt hξ hs).2 hr0 hr1) (T.convergesAt_teich s _), T.ptE_ξ hη, ptE_teich, zero_add]`.
-/
theorem ptEval_ξExt_movePt {s : L} (hs : ‖s‖ < T.ptRad ξ) {ρ0 : Set.Ioo (0 : ℝ) 1}
    (hr : T.ptRad (T.movePt hξ hs) ≤ ρ0) :
    T.ptEval (T.isPrimOne_movePt hξ hs) hr (T.ξExt ξ ρ0) = T.ptSharp (T.isPrimOne_movePt hξ hs) s := by
  set hη := T.isPrimOne_movePt hξ hs
  rw [ξExt, T.ptEval_coe_algebraMap hη hr]
  have hr0 := T.ptRad_pos' hη
  have hr1 := T.ptRad_lt_one' hη
  have e : (ξ : Γ) = (T.movePt hξ hs : Γ) + T.teich s := by rw [coe_movePt]; ring
  rw [e, T.ptE_add hη (T.convergesAt_of_mem_int (T.movePt hξ hs).2 hr0 hr1) (T.convergesAt_teich s _),
    T.ptE_ξ hη, ptE_teich, zero_add]

end Move

section Step

/- English proof (translation)
Establish `hr0` using `T.ptRad_pos' hξ`. Establish `hr1` using `T.ptRad_lt_one' hξ`. Establish `ht` using `T.tail_mem_int hV`. Establish `htc` using `T.convergesAt_of_mem_int ht hr0 hr1`. Establish `hc1 : ConvergesAt (T.zcoeff (T.teich (T.red V))) (T.ptRad ξ)` using `T.convergesAt_teich _ _`.

Establish `hc2 : ConvergesAt (T.zcoeff (T.π * T.tail V)) (T.ptRad ξ)` using `T.convergesAt_zcoeff_mul hr0 hr1 (T.convergesAt_π _) htc`. Establish `e : T.ptE hξ V = T.ptSharp hξ (T.red V) + T.ptPi hξ * T.ptE hξ (T.tail V)` using `by conv_lhs => rw [T.eq_teich_add_π_mul_tail V]`. Rewrite using `[T.ptE_add hξ hc1 hc2, T.ptE_mul hξ (T.convergesAt_π _) htc, ptE_teich, ptE_π]`. Rewrite using `[e, add_sub_cancel_left, norm_mul, norm_ptPi]`. Establish `h1 : ‖T.ptE hξ (T.tail V)‖ ≤ 1` using `(T.norm_ptE_le hξ htc).trans (T.gaussNorm_le_one_of_mem_int ht hr0 hr1.le)`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_ptE_sub_sharp_red_le {V : Γ} (hV : V ∈ T.int) :
    ‖T.ptE hξ V - T.ptSharp hξ (T.red V)‖ ≤ T.ptRad ξ := by
  have hr0 := T.ptRad_pos' hξ
  have hr1 := T.ptRad_lt_one' hξ
  have ht := T.tail_mem_int hV
  have htc := T.convergesAt_of_mem_int ht hr0 hr1
  have hc1 : ConvergesAt (T.zcoeff (T.teich (T.red V))) (T.ptRad ξ) := T.convergesAt_teich _ _
  have hc2 : ConvergesAt (T.zcoeff (T.π * T.tail V)) (T.ptRad ξ) :=
    T.convergesAt_zcoeff_mul hr0 hr1 (T.convergesAt_π _) htc
  have e : T.ptE hξ V = T.ptSharp hξ (T.red V) + T.ptPi hξ * T.ptE hξ (T.tail V) := by
    conv_lhs => rw [T.eq_teich_add_π_mul_tail V]
    rw [T.ptE_add hξ hc1 hc2, T.ptE_mul hξ (T.convergesAt_π _) htc, ptE_teich, ptE_π]
  rw [e, add_sub_cancel_left, norm_mul, norm_ptPi]
  have h1 : ‖T.ptE hξ (T.tail V)‖ ≤ 1 :=
    (T.norm_ptE_le hξ htc).trans (T.gaussNorm_le_one_of_mem_int ht hr0 hr1.le)
  calc ‖T.coeff (ξ : Γ) 0‖ * ‖T.ptE hξ (T.tail V)‖ ≤ ‖T.coeff (ξ : Γ) 0‖ * 1 :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = T.ptRad ξ := mul_one _

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using hM0`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.sum_insert hi]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj)))`.
-/
theorem norm_finset_sum_le_ultra {E : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E]
    {ι : Type*} (s : Finset ι) (f : ι → E) {M : ℝ} (hM0 : 0 ≤ M) (h : ∀ i ∈ s, ‖f i‖ ≤ M) :
    ‖∑ i ∈ s, f i‖ ≤ M := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hM0
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj)))

variable [IsAlgClosed L] {ρ0 : Set.Ioo (0 : ℝ) 1} (hr : T.ptRad ξ < ρ0)

/- English proof (translation)
Take `⟨J, hJm, hpos, hstrict, hJeq⟩` from `T.exists_nondeg (hξ := hξ) hr hx`. Use `set r := T.ptRad ξ with hrdef`. Establish `hr0 : 0 < r` using `T.ptRad_pos' hξ`. Establish `hr1 : r < 1` using `T.ptRad_lt_one' hξ`. Use `set ε := ‖T.ptEval hξ hr.le x‖ with hεdef`.

Use `set N := T.extNorm ρ0 (T.ptRadIoc hξ hr.le) x with hNdef`. Establish `hεpos : 0 < ε` using `norm_pos_iff.2 hε0`. Establish `hNpos : 0 < N` using `hεpos.trans hεN`. Use `set D := fun j => T.divStep hξ hr.le (T.tay hξ hr.le x j)`. Use `set b : ℕ → L := fun j => (D j).z * T.red (D j).V with hbdef`.

Establish `hnb : ∀ j, ‖b j‖ = ‖T.ptEval hξ hr.le (T.tay hξ hr.le x j)‖` using `fun j => by`. Simplify using `only [hbdef, norm_mul, (D j).hred, mul_one, (D j).hz]`. Establish `hJ1 : 1 ≤ J`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Establish `hJ0 : J = 0` using `by omega`. Rewrite `hJeq` using `[hJ0, tay_zero]`. Establish `hεN' : ε = N` using `hJeq`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hb0 : ‖b 0‖ = ε` using `by rw [hnb, tay_zero]`.

Establish `hbJ : r ^ J * ‖b J‖ = N` using `by rw [hnb, hJeq]; exact (hpos J le_rfl).2`. Use `set g : Polynomial L := ∑ j ∈ Finset.range (J + 1), Polynomial.C (b j) * Polynomial.X ^ j with hgdef`. Establish `hcoeff : ∀ k, g.coeff k = if k < J + 1 then b k else 0` using `fun k => by`. Rewrite using `[hgdef, Polynomial.finset_sum_coeff]`. Simplify using `only [Polynomial.coeff_C_mul_X_pow]`.

Rewrite using `[Finset.sum_ite_eq (Finset.range (J + 1)) k (fun j => b j)]`. Simplify using `[Finset.mem_range]`. Establish `hbJne : b J ≠ 0`. Introduce `h0`. Rewrite `hbJ` using `[h0, norm_zero, mul_zero]`.

Conclude with `hNpos.ne hbJ`. Establish `hdeg : g.natDegree = J`. Use `Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ (by rw [hcoeff, if_pos (by omega)]; exact hbJne)` and prove the remaining obligations. Use `Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj => ?_` and prove the remaining obligations. Use `(Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_` and prove the remaining obligations.

Use `Finset.mem_range.1 hj` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hg0 : g.coeff 0 ≠ 0`. Rewrite using `[hcoeff, if_pos (by omega)]; intro h0; rw [h0, norm_zero] at hb0; exact hεpos.ne hb0`. Take `⟨s, hroot, hsj⟩` from `exists_isRoot_forall_norm_pow_mul_le (by omega : 0 < g.natDegree) hg0`.

Establish `hsj' : ∀ j ≤ J, ‖s‖ ^ j * ‖b j‖ ≤ ε` using `fun j hj => by`. Use `hsj j` as an intermediate fact. Rewrite `this` using `[hcoeff, if_pos (by omega), hcoeff, if_pos (by omega), hb0]`. Then use the resulting hypothesis. Establish `hratio : (‖s‖ / r) ^ J ≤ ε / N`. Use `hsj' J le_rfl` as an intermediate fact.

Rewrite using `[div_pow, div_le_div_iff₀ (pow_pos hr0 J) hNpos, ← hbJ]`. Use polynomial arithmetic with `[pow_pos hr0 J, norm_nonneg (b J)]`. Establish `hεN1 : ε / N < 1` using `(div_lt_one hNpos).2 hεN`. Establish `hsr : ‖s‖ / r < 1`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Use `one_le_pow₀ (n := J) h` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hs : ‖s‖ < r` using `by rwa [div_lt_one hr0] at hsr`. Use `⟨s, hs, J, hJ1, hJm, hratio, ?_⟩` and prove the remaining obligations.

Use `set hη := T.isPrimOne_movePt hξ hs`. Establish `hrη : T.ptRad (T.movePt hξ hs) ≤ ρ0` using `(T.ptRad_movePt hξ hs).trans_le hr.le`. Establish `hrad : T.ptRad (T.movePt hξ hs) = r` using `T.ptRad_movePt hξ hs`. Use `set θ := T.ptEval hη hrη`. Establish `hθξ : θ (T.ξExt ξ ρ0) = T.ptSharp hη s` using `T.ptEval_ξExt_movePt hξ hs hrη`.

Establish `hlift : ∀ j, θ (T.liftExt ρ0 (D j).z (D j).hV) = T.ptSharp hη ((D j).z) * T.ptE hη (D j).V` using `fun j => T.ptEval_liftExt hη hrη _ _`. Establish `hexp` using `congrArg θ (T.taylor_eq hξ hr.le x J)`. Rewrite `hexp` using `[map_add, map_sum]`. Simplify using `only [map_mul, map_pow, hθξ, hlift] at hexp`. Use `set a : ℕ → L := fun j => s ^ j * b j`.

Establish `ha : ∀ j ∈ Finset.range (J + 1), ‖a j‖ ≤ ε` using `fun j hj => by`. Simplify using `only [a, norm_mul, norm_pow]; exact hsj' j (by have := Finset.mem_range.1 hj; omega)`. Establish `hsum0 : ∑ j ∈ Finset.range (J + 1), a j = 0`. Use `hroot` as an intermediate fact. Rewrite `this` using `[Polynomial.IsRoot, hgdef, Polynomial.eval_finset_sum]`.

Simplify using `only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] at this`. Rewrite using `[← this]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [a]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hA : ‖∑ j ∈ Finset.range (J + 1), T.ptSharp hη (a j)‖ ≤ r * ε`. Use `T.norm_sum_sharp_sub_le hη (Finset.range (J + 1)) a hεpos.le ha` as an intermediate fact. Rewrite `this` using `[hsum0, map_zero, sub_zero, hrad]`. Then use the resulting hypothesis. Establish `hB : ‖∑ j ∈ Finset.range (J + 1), T.ptSharp hη s ^ j * (T.ptSharp hη ((D j).z) * (T.ptE hη (D j).V - T.ptSharp hη (T.red (D j).V)))‖ ≤ r * ε`. Use `norm_finset_sum_le_ultra _ _ (by positivity) fun j hj => ?_` and prove the remaining obligations.

Rewrite using `[norm_mul, norm_mul, norm_pow, norm_ptSharp, norm_ptSharp]`. Establish `h1` using `T.norm_ptE_sub_sharp_red_le hη (D j).hV`. Rewrite `h1` using `[hrad]`. Establish `h2 : ‖s‖ ^ j * ‖(D j).z‖ ≤ ε`. Use `ha j hj` as an intermediate fact.

Simplify using `only [a, b, norm_mul, norm_pow, (D j).hred, mul_one] at this`. Conclude with `this`. Combine the equalities or inequalities in the displayed calculation. Establish `hIoc : T.ptRadIoc hη hrη = T.ptRadIoc hξ hr.le` using `Subtype.ext hrad`. Establish `hC : ‖T.ptSharp hη s ^ (J + 1) * θ (T.tay hξ hr.le x (J + 1))‖ ≤ ε * (‖s‖ / r)`.

Rewrite using `[norm_mul, norm_pow, norm_ptSharp]`. Establish `h1 : ‖θ (T.tay hξ hr.le x (J + 1))‖ ≤ T.extNorm ρ0 (T.ptRadIoc hξ hr.le) (T.tay hξ hr.le x (J + 1))`. Use `T.norm_ptEval_le hη hrη (T.tay hξ hr.le x (J + 1))` as an intermediate fact. Rewrite `this` using `[hIoc]`. Then use the resulting hypothesis. Establish `h2 : r ^ (J + 1) * T.extNorm ρ0 (T.ptRadIoc hξ hr.le) (T.tay hξ hr.le x (J + 1)) ≤ N`.

Use `T.extNorm_next_le (hξ := hξ) (hr := hr.le) (T.tay hξ hr.le x J)` as an intermediate fact. Rewrite `this` using `[← tay_succ]`. Rewrite using `[pow_succ, ← (hpos J le_rfl).2]`. Use polynomial arithmetic with `[pow_pos hr0 J]`. Establish `h3 : ‖s‖ ^ (J + 1) * T.extNorm ρ0 (T.ptRadIoc hξ hr.le) (T.tay hξ hr.le x (J + 1)) ≤ (‖s‖ / r) ^ (J + 1) * N`.

Rewrite using `[div_pow, div_mul_eq_mul_div, le_div_iff₀ (pow_pos hr0 _)]`. Use polynomial arithmetic with `[pow_nonneg (norm_nonneg s) (J + 1)]`. Combine the equalities or inequalities in the displayed calculation. Establish `hsplit : θ x = ∑ j ∈ Finset.range (J + 1), T.ptSharp hη (a j) + ∑ j ∈ Finset.range (J + 1), T.ptSharp hη s ^ j * (T.ptSharp hη ((D j).z) * (T.ptE hη (D j).V - T.ptSharp hη (T.red (D j).V))) + T.ptSharp hη s ^ (J + 1) * θ (T.tay hξ hr.le x (J + 1))`. Rewrite using `[hexp, ← Finset.sum_add_distrib]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `hl` using `hlift j`. Simplify using `only [D] at hl`. Rewrite using `[hl]`.

Simplify using `only [a, b, D, map_mul, map_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsplit]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations.

Conclude with `hA.trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (le_max_left _ _) hεpos.le)`. Conclude with `hB.trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (le_max_left _ _) hεpos.le)`. Conclude with `hC.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hεpos.le)`.
-/
theorem step_estimate {x : T.RobbaExt ρ0} (hx : x ≠ 0) (hε0 : T.ptEval hξ hr.le x ≠ 0)
    (hεN : ‖T.ptEval hξ hr.le x‖ < T.extNorm ρ0 (T.ptRadIoc hξ hr.le) x) :
    ∃ (s : L) (hs : ‖s‖ < T.ptRad ξ) (J : ℕ), 1 ≤ J ∧ (J : ℤ) ≤ T.mult x (T.ptRad ξ) ∧
      (‖s‖ / T.ptRad ξ) ^ J ≤
        ‖T.ptEval hξ hr.le x‖ / T.extNorm ρ0 (T.ptRadIoc hξ hr.le) x ∧
      ‖T.ptEval (T.isPrimOne_movePt hξ hs) ((T.ptRad_movePt hξ hs).trans_le hr.le) x‖ ≤
        ‖T.ptEval hξ hr.le x‖ * max (T.ptRad ξ) (‖s‖ / T.ptRad ξ) := by
  classical
  obtain ⟨J, hJm, hpos, hstrict, hJeq⟩ := T.exists_nondeg (hξ := hξ) hr hx
  set r := T.ptRad ξ with hrdef
  have hr0 : 0 < r := T.ptRad_pos' hξ
  have hr1 : r < 1 := T.ptRad_lt_one' hξ
  set ε := ‖T.ptEval hξ hr.le x‖ with hεdef
  set N := T.extNorm ρ0 (T.ptRadIoc hξ hr.le) x with hNdef
  have hεpos : 0 < ε := norm_pos_iff.2 hε0
  have hNpos : 0 < N := hεpos.trans hεN
  set D := fun j => T.divStep hξ hr.le (T.tay hξ hr.le x j)
  set b : ℕ → L := fun j => (D j).z * T.red (D j).V with hbdef
  have hnb : ∀ j, ‖b j‖ = ‖T.ptEval hξ hr.le (T.tay hξ hr.le x j)‖ := fun j => by
    simp only [hbdef, norm_mul, (D j).hred, mul_one, (D j).hz]
  have hJ1 : 1 ≤ J := by
    by_contra h
    push_neg at h
    have hJ0 : J = 0 := by omega
    rw [hJ0, tay_zero] at hJeq
    have hεN' : ε = N := hJeq
    linarith
  have hb0 : ‖b 0‖ = ε := by rw [hnb, tay_zero]
  have hbJ : r ^ J * ‖b J‖ = N := by rw [hnb, hJeq]; exact (hpos J le_rfl).2

  set g : Polynomial L := ∑ j ∈ Finset.range (J + 1), Polynomial.C (b j) * Polynomial.X ^ j
    with hgdef
  have hcoeff : ∀ k, g.coeff k = if k < J + 1 then b k else 0 := fun k => by
    rw [hgdef, Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq (Finset.range (J + 1)) k (fun j => b j)]
    simp [Finset.mem_range]
  have hbJne : b J ≠ 0 := by
    intro h0; rw [h0, norm_zero, mul_zero] at hbJ; exact hNpos.ne hbJ
  have hdeg : g.natDegree = J := by
    refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ (by rw [hcoeff, if_pos (by omega)]; exact hbJne)
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    have := Finset.mem_range.1 hj; omega
  have hg0 : g.coeff 0 ≠ 0 := by
    rw [hcoeff, if_pos (by omega)]; intro h0; rw [h0, norm_zero] at hb0; exact hεpos.ne hb0
  obtain ⟨s, hroot, hsj⟩ := exists_isRoot_forall_norm_pow_mul_le (by omega : 0 < g.natDegree) hg0
  have hsj' : ∀ j ≤ J, ‖s‖ ^ j * ‖b j‖ ≤ ε := fun j hj => by
    have := hsj j
    rwa [hcoeff, if_pos (by omega), hcoeff, if_pos (by omega), hb0] at this
  have hratio : (‖s‖ / r) ^ J ≤ ε / N := by
    have := hsj' J le_rfl
    rw [div_pow, div_le_div_iff₀ (pow_pos hr0 J) hNpos, ← hbJ]
    nlinarith [pow_pos hr0 J, norm_nonneg (b J)]
  have hεN1 : ε / N < 1 := (div_lt_one hNpos).2 hεN
  have hsr : ‖s‖ / r < 1 := by
    by_contra h
    push_neg at h
    have := one_le_pow₀ (n := J) h
    linarith
  have hs : ‖s‖ < r := by rwa [div_lt_one hr0] at hsr
  refine ⟨s, hs, J, hJ1, hJm, hratio, ?_⟩

  set hη := T.isPrimOne_movePt hξ hs
  have hrη : T.ptRad (T.movePt hξ hs) ≤ ρ0 := (T.ptRad_movePt hξ hs).trans_le hr.le
  have hrad : T.ptRad (T.movePt hξ hs) = r := T.ptRad_movePt hξ hs
  set θ := T.ptEval hη hrη
  have hθξ : θ (T.ξExt ξ ρ0) = T.ptSharp hη s := T.ptEval_ξExt_movePt hξ hs hrη
  have hlift : ∀ j, θ (T.liftExt ρ0 (D j).z (D j).hV) =
      T.ptSharp hη ((D j).z) * T.ptE hη (D j).V := fun j => T.ptEval_liftExt hη hrη _ _
  have hexp := congrArg θ (T.taylor_eq hξ hr.le x J)
  rw [map_add, map_sum] at hexp
  simp only [map_mul, map_pow, hθξ, hlift] at hexp

  set a : ℕ → L := fun j => s ^ j * b j
  have ha : ∀ j ∈ Finset.range (J + 1), ‖a j‖ ≤ ε := fun j hj => by
    simp only [a, norm_mul, norm_pow]; exact hsj' j (by have := Finset.mem_range.1 hj; omega)
  have hsum0 : ∑ j ∈ Finset.range (J + 1), a j = 0 := by
    have := hroot
    rw [Polynomial.IsRoot, hgdef, Polynomial.eval_finset_sum] at this
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [a]; ring
  have hA : ‖∑ j ∈ Finset.range (J + 1), T.ptSharp hη (a j)‖ ≤ r * ε := by
    have := T.norm_sum_sharp_sub_le hη (Finset.range (J + 1)) a hεpos.le ha
    rwa [hsum0, map_zero, sub_zero, hrad] at this
  have hB : ‖∑ j ∈ Finset.range (J + 1), T.ptSharp hη s ^ j *
      (T.ptSharp hη ((D j).z) * (T.ptE hη (D j).V - T.ptSharp hη (T.red (D j).V)))‖ ≤ r * ε := by
    refine norm_finset_sum_le_ultra _ _ (by positivity) fun j hj => ?_
    rw [norm_mul, norm_mul, norm_pow, norm_ptSharp, norm_ptSharp]
    have h1 := T.norm_ptE_sub_sharp_red_le hη (D j).hV
    rw [hrad] at h1
    have h2 : ‖s‖ ^ j * ‖(D j).z‖ ≤ ε := by
      have := ha j hj
      simp only [a, b, norm_mul, norm_pow, (D j).hred, mul_one] at this
      exact this
    calc ‖s‖ ^ j * (‖(D j).z‖ * ‖T.ptE hη (D j).V - T.ptSharp hη (T.red (D j).V)‖)
        = (‖s‖ ^ j * ‖(D j).z‖) * ‖T.ptE hη (D j).V - T.ptSharp hη (T.red (D j).V)‖ := by ring
      _ ≤ ε * r := mul_le_mul h2 h1 (norm_nonneg _) hεpos.le
      _ = r * ε := mul_comm _ _
  have hIoc : T.ptRadIoc hη hrη = T.ptRadIoc hξ hr.le := Subtype.ext hrad
  have hC : ‖T.ptSharp hη s ^ (J + 1) * θ (T.tay hξ hr.le x (J + 1))‖ ≤ ε * (‖s‖ / r) := by
    rw [norm_mul, norm_pow, norm_ptSharp]
    have h1 : ‖θ (T.tay hξ hr.le x (J + 1))‖ ≤
        T.extNorm ρ0 (T.ptRadIoc hξ hr.le) (T.tay hξ hr.le x (J + 1)) := by
      have := T.norm_ptEval_le hη hrη (T.tay hξ hr.le x (J + 1))
      rwa [hIoc] at this
    have h2 : r ^ (J + 1) * T.extNorm ρ0 (T.ptRadIoc hξ hr.le) (T.tay hξ hr.le x (J + 1)) ≤ N := by
      have := T.extNorm_next_le (hξ := hξ) (hr := hr.le) (T.tay hξ hr.le x J)
      rw [← tay_succ] at this
      rw [pow_succ, ← (hpos J le_rfl).2]
      nlinarith [pow_pos hr0 J]
    have h3 : ‖s‖ ^ (J + 1) * T.extNorm ρ0 (T.ptRadIoc hξ hr.le) (T.tay hξ hr.le x (J + 1)) ≤
        (‖s‖ / r) ^ (J + 1) * N := by
      rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (pow_pos hr0 _)]
      nlinarith [pow_nonneg (norm_nonneg s) (J + 1)]
    calc ‖s‖ ^ (J + 1) * ‖θ (T.tay hξ hr.le x (J + 1))‖
        ≤ ‖s‖ ^ (J + 1) * T.extNorm ρ0 (T.ptRadIoc hξ hr.le) (T.tay hξ hr.le x (J + 1)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ (‖s‖ / r) ^ (J + 1) * N := h3
      _ = (‖s‖ / r) * ((‖s‖ / r) ^ J * N) := by ring
      _ ≤ (‖s‖ / r) * ((ε / N) * N) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hratio hNpos.le) (by positivity)
      _ = ε * (‖s‖ / r) := by field_simp

  have hsplit : θ x = ∑ j ∈ Finset.range (J + 1), T.ptSharp hη (a j) +
      ∑ j ∈ Finset.range (J + 1), T.ptSharp hη s ^ j *
        (T.ptSharp hη ((D j).z) * (T.ptE hη (D j).V - T.ptSharp hη (T.red (D j).V))) +
      T.ptSharp hη s ^ (J + 1) * θ (T.tay hξ hr.le x (J + 1)) := by
    rw [hexp, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have hl := hlift j
    simp only [D] at hl
    rw [hl]
    simp only [a, b, D, map_mul, map_pow]
    ring
  rw [hsplit]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · exact hA.trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (le_max_left _ _) hεpos.le)
    · exact hB.trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (le_max_left _ _) hεpos.le)
  · exact hC.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hεpos.le)

end Step

end TeichLift

end GroundTheory.PAdicHodge
