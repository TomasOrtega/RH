import Formalism.EisensteinCokernelLengths.StatementLIFTV
import Formalism.LagrangeIdealLifts.LiftLagrangeIdealInt
import Formalism.WindowSums.PowerSeriesRelationList

namespace Formalism.ZetaNonvanishing.LIFTV

/- English proof (translation)
Introduce `ℓ _ R _ _ sg S₁ S₂ c hd hc`. Conclude with `Formalism.LIFT.lift_LagrangeIdeal R (ℓ : R) ℤ S₁ S₂ c (fun a b => sg + padicValInt ℓ (a - b)) hd hc`.
-/
theorem lagrangeIdealSg_proof : LagrangeIdealSg := by
  intro ℓ _ R _ _ sg S₁ S₂ c hd hc
  exact Formalism.LIFT.lift_LagrangeIdeal R (ℓ : R) ℤ S₁ S₂ c (fun a b => sg + padicValInt ℓ (a - b)) hd hc

/- English proof (translation)
Unfold `WindowDiff`. Introduce `ℓ hℓ a₀ y D S a hS hD`. Establish `hp : ℓ.Prime` using `hℓ.out`. Establish `hl1 : 1 < ℓ` using `hp.one_lt`. Establish `hlR : (1 : ℝ) < ℓ` using `by exact_mod_cast hl1`.

Use `set K := Nat.log ℓ D with hK`. Establish `hv : ∀ b ∈ S.erase a, padicValInt ℓ (a - b) = ((Finset.Icc 1 K).filter (fun k => (ℓ : ℤ) ^ k ∣ a - b)).card`. Introduce `b hb`. Establish `hne : a - b ≠ 0` using `sub_ne_zero.mpr (Finset.ne_of_mem_erase hb).symm`. Establish `hle : padicValInt ℓ (a - b) ≤ K`.

Establish `h1 : (ℓ : ℤ) ^ padicValInt ℓ (a - b) ≤ |a - b|` using `Int.le_of_dvd (abs_pos.mpr hne) ((dvd_abs _ _).mpr (padicValInt_dvd (a - b)))`. Establish `h3 : ℓ ^ padicValInt ℓ (a - b) ≤ D`. Establish `h4` using `le_trans h1 (hD b (Finset.mem_of_mem_erase hb))`. Conclude with `h4` after adjusting the coercions. Conclude with `Nat.le_log_of_pow_le hl1 h3`.

Establish `hset : (Finset.Icc 1 K).filter (fun k => (ℓ : ℤ) ^ k ∣ a - b) = Finset.Icc 1 (padicValInt ℓ (a - b))`. Use extensionality with `k`. Simplify using `only [Finset.mem_filter, Finset.mem_Icc, padicValInt_dvd_iff, hne, false_or]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hset, Nat.card_Icc, Nat.add_sub_cancel]`.

Establish `hsum : ∑ b ∈ S.erase a, padicValInt ℓ (a - b) = ∑ k ∈ Finset.Icc 1 K, ((S.erase a).filter (fun b => (ℓ : ℤ) ^ k ∣ a - b)).card`. Rewrite using `[Finset.sum_congr rfl hv]`. Simplify using `only [Finset.card_filter]`. Conclude with `Finset.sum_comm`. Establish `hk : ∀ k ∈ Finset.Icc 1 K, ((((S.erase a).filter (fun b => (ℓ : ℤ) ^ k ∣ a - b)).card : ℕ) : ℝ) ≤ ((y : ℝ) + 1) / (ℓ : ℝ) ^ k + 1`.

Introduce `k _`. Establish `hM : (0 : ℤ) < (ℓ : ℤ) ^ k` using `by positivity`. Establish `hsub : (S.erase a).filter (fun b => (ℓ : ℤ) ^ k ∣ a - b) ⊆ (Finset.Ico a₀ (a₀ + y + 1)).filter (fun x => x ≡ a [ZMOD (ℓ : ℤ) ^ k])`. Introduce `b hb`. Rewrite `hb`, the goal using `[Finset.mem_filter]`.

Establish `hbS` using `hS (Finset.mem_of_mem_erase hb.1)`. Rewrite `hbS` using `[Finset.mem_Icc]`. Conclude with `⟨Finset.mem_Ico.mpr ⟨hbS.1, by omega⟩, Int.modEq_iff_dvd.mpr hb.2⟩`. Establish `hcard` using `Int.Ico_filter_modEq_card a₀ (a₀ + y + 1) hM a`. Establish `hle` using `Finset.card_le_card hsub`.

Establish `hMq : (0 : ℚ) < (ℓ : ℚ) ^ k` using `by positivity`. Establish `hq : ((((Finset.Ico a₀ (a₀ + y + 1)).filter (fun x => x ≡ a [ZMOD (ℓ : ℤ) ^ k])).card : ℤ) : ℚ) ≤ ((y : ℚ) + 1) / (ℓ : ℚ) ^ k + 1`. Rewrite using `[hcard]`. Use `push_cast`. Apply `max_le` to reduce the goal to its premises.

Establish `e1` using `Int.ceil_lt_add_one (((a₀ : ℚ) + y + 1 - a) / (ℓ : ℚ) ^ k)`. Establish `e2` using `Int.le_ceil (((a₀ : ℚ) - a) / (ℓ : ℚ) ^ k)`. Establish `e3 : ((a₀ : ℚ) + y + 1 - a) / (ℓ : ℚ) ^ k - ((a₀ : ℚ) - a) / (ℓ : ℚ) ^ k = ((y : ℚ) + 1) / (ℓ : ℚ) ^ k`. Rewrite using `[← sub_div]`. Expand and normalize the polynomial expressions, which then agree.

Combine the linear equalities and inequalities to obtain the conclusion. Check the signs of the components of the expression. Establish `hq2 : ((((S.erase a).filter (fun b => (ℓ : ℤ) ^ k ∣ a - b)).card : ℕ) : ℚ) ≤ ((y : ℚ) + 1) / (ℓ : ℚ) ^ k + 1`. Establish `h5 : ((((S.erase a).filter (fun b => (ℓ : ℤ) ^ k ∣ a - b)).card : ℕ) : ℚ) ≤ ((((Finset.Ico a₀ (a₀ + y + 1)).filter (fun x => x ≡ a [ZMOD (ℓ : ℤ) ^ k])).card : ℤ) : ℚ)`. Conclude with `hle` after adjusting the coercions.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hq3` using `(Rat.cast_le (K := ℝ)).mpr hq2`. Move the coercions through the operations in `at hq3`. Conclude with `hq3`. Establish `hgeo : ∑ k ∈ Finset.Icc 1 K, ((ℓ : ℝ)⁻¹) ^ k ≤ 1 / ((ℓ : ℝ) - 1)`.

Establish `h0 : (0 : ℝ) ≤ (ℓ : ℝ)⁻¹` using `by positivity`. Establish `h1 : (ℓ : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ hlR`. Establish `h2` using `geom_sum_Ico_le_of_lt_one (m := 1) (n := K + 1) h0 h1`. Establish `hI : Finset.Ico 1 (K + 1) = Finset.Icc 1 K`. Use extensionality with `j`.

Simplify using `only [Finset.mem_Ico, Finset.mem_Icc]`. Use linear arithmetic over natural numbers and integers. Rewrite `h2` using `[hI]`. Establish `hl0 : (ℓ : ℝ) ≠ 0` using `by positivity`. Establish `hl1' : (ℓ : ℝ) - 1 ≠ 0` using `by linarith`.

Establish `e : (ℓ : ℝ)⁻¹ ^ 1 / (1 - (ℓ : ℝ)⁻¹) = 1 / ((ℓ : ℝ) - 1)`. Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsumk : ∑ k ∈ Finset.Icc 1 K, (((y : ℝ) + 1) / (ℓ : ℝ) ^ k + 1) = ((y : ℝ) + 1) * ∑ k ∈ Finset.Icc 1 K, ((ℓ : ℝ)⁻¹) ^ k + K`. Rewrite using `[Finset.sum_add_distrib, Finset.mul_sum]`.

Simplify using `[div_eq_mul_inv, inv_pow]`. Establish `hlog : (K : ℝ) ≤ Real.logb ℓ D` using `Real.natLog_le_logb D ℓ`. Establish `hy : (0 : ℝ) ≤ (y : ℝ) + 1` using `by positivity`. Rewrite using `[hsum]`. Use `push_cast`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem windowDiff_proof : WindowDiff := by
  unfold WindowDiff
  intro ℓ hℓ a₀ y D S a hS hD
  have hp : ℓ.Prime := hℓ.out
  have hl1 : 1 < ℓ := hp.one_lt
  have hlR : (1 : ℝ) < ℓ := by exact_mod_cast hl1
  set K := Nat.log ℓ D with hK

  have hv : ∀ b ∈ S.erase a, padicValInt ℓ (a - b) =
      ((Finset.Icc 1 K).filter (fun k => (ℓ : ℤ) ^ k ∣ a - b)).card := by
    intro b hb
    have hne : a - b ≠ 0 := sub_ne_zero.mpr (Finset.ne_of_mem_erase hb).symm
    have hle : padicValInt ℓ (a - b) ≤ K := by
      have h1 : (ℓ : ℤ) ^ padicValInt ℓ (a - b) ≤ |a - b| :=
        Int.le_of_dvd (abs_pos.mpr hne) ((dvd_abs _ _).mpr (padicValInt_dvd (a - b)))
      have h3 : ℓ ^ padicValInt ℓ (a - b) ≤ D := by
        have h4 := le_trans h1 (hD b (Finset.mem_of_mem_erase hb))
        exact_mod_cast h4
      exact Nat.le_log_of_pow_le hl1 h3
    have hset : (Finset.Icc 1 K).filter (fun k => (ℓ : ℤ) ^ k ∣ a - b) =
        Finset.Icc 1 (padicValInt ℓ (a - b)) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc, padicValInt_dvd_iff, hne, false_or]
      omega
    rw [hset, Nat.card_Icc, Nat.add_sub_cancel]
  have hsum : ∑ b ∈ S.erase a, padicValInt ℓ (a - b) =
      ∑ k ∈ Finset.Icc 1 K, ((S.erase a).filter (fun b => (ℓ : ℤ) ^ k ∣ a - b)).card := by
    rw [Finset.sum_congr rfl hv]
    simp only [Finset.card_filter]
    exact Finset.sum_comm

  have hk : ∀ k ∈ Finset.Icc 1 K, ((((S.erase a).filter (fun b => (ℓ : ℤ) ^ k ∣ a - b)).card : ℕ) : ℝ)
      ≤ ((y : ℝ) + 1) / (ℓ : ℝ) ^ k + 1 := by
    intro k _
    have hM : (0 : ℤ) < (ℓ : ℤ) ^ k := by positivity
    have hsub : (S.erase a).filter (fun b => (ℓ : ℤ) ^ k ∣ a - b) ⊆
        (Finset.Ico a₀ (a₀ + y + 1)).filter (fun x => x ≡ a [ZMOD (ℓ : ℤ) ^ k]) := by
      intro b hb
      rw [Finset.mem_filter] at hb ⊢
      have hbS := hS (Finset.mem_of_mem_erase hb.1)
      rw [Finset.mem_Icc] at hbS
      exact ⟨Finset.mem_Ico.mpr ⟨hbS.1, by omega⟩, Int.modEq_iff_dvd.mpr hb.2⟩
    have hcard := Int.Ico_filter_modEq_card a₀ (a₀ + y + 1) hM a
    have hle := Finset.card_le_card hsub
    have hMq : (0 : ℚ) < (ℓ : ℚ) ^ k := by positivity
    have hq : ((((Finset.Ico a₀ (a₀ + y + 1)).filter (fun x => x ≡ a [ZMOD (ℓ : ℤ) ^ k])).card : ℤ) : ℚ)
        ≤ ((y : ℚ) + 1) / (ℓ : ℚ) ^ k + 1 := by
      rw [hcard]
      push_cast
      apply max_le
      · have e1 := Int.ceil_lt_add_one (((a₀ : ℚ) + y + 1 - a) / (ℓ : ℚ) ^ k)
        have e2 := Int.le_ceil (((a₀ : ℚ) - a) / (ℓ : ℚ) ^ k)
        have e3 : ((a₀ : ℚ) + y + 1 - a) / (ℓ : ℚ) ^ k - ((a₀ : ℚ) - a) / (ℓ : ℚ) ^ k
            = ((y : ℚ) + 1) / (ℓ : ℚ) ^ k := by
          rw [← sub_div]
          ring
        linarith
      · positivity
    have hq2 : ((((S.erase a).filter (fun b => (ℓ : ℤ) ^ k ∣ a - b)).card : ℕ) : ℚ)
        ≤ ((y : ℚ) + 1) / (ℓ : ℚ) ^ k + 1 := by
      have h5 : ((((S.erase a).filter (fun b => (ℓ : ℤ) ^ k ∣ a - b)).card : ℕ) : ℚ)
          ≤ ((((Finset.Ico a₀ (a₀ + y + 1)).filter (fun x => x ≡ a [ZMOD (ℓ : ℤ) ^ k])).card : ℤ) : ℚ) := by
        exact_mod_cast hle
      linarith
    have hq3 := (Rat.cast_le (K := ℝ)).mpr hq2
    push_cast at hq3
    exact hq3
  have hgeo : ∑ k ∈ Finset.Icc 1 K, ((ℓ : ℝ)⁻¹) ^ k ≤ 1 / ((ℓ : ℝ) - 1) := by
    have h0 : (0 : ℝ) ≤ (ℓ : ℝ)⁻¹ := by positivity
    have h1 : (ℓ : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hlR
    have h2 := geom_sum_Ico_le_of_lt_one (m := 1) (n := K + 1) h0 h1
    have hI : Finset.Ico 1 (K + 1) = Finset.Icc 1 K := by
      ext j
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    rw [hI] at h2
    have hl0 : (ℓ : ℝ) ≠ 0 := by positivity
    have hl1' : (ℓ : ℝ) - 1 ≠ 0 := by linarith
    have e : (ℓ : ℝ)⁻¹ ^ 1 / (1 - (ℓ : ℝ)⁻¹) = 1 / ((ℓ : ℝ) - 1) := by
      field_simp
    linarith
  have hsumk : ∑ k ∈ Finset.Icc 1 K, (((y : ℝ) + 1) / (ℓ : ℝ) ^ k + 1)
      = ((y : ℝ) + 1) * ∑ k ∈ Finset.Icc 1 K, ((ℓ : ℝ)⁻¹) ^ k + K := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    simp [div_eq_mul_inv, inv_pow]
  have hlog : (K : ℝ) ≤ Real.logb ℓ D := Real.natLog_le_logb D ℓ
  have hy : (0 : ℝ) ≤ (y : ℝ) + 1 := by positivity
  rw [hsum]
  push_cast
  calc _ ≤ ∑ k ∈ Finset.Icc 1 K, (((y : ℝ) + 1) / (ℓ : ℝ) ^ k + 1) := Finset.sum_le_sum hk
    _ = ((y : ℝ) + 1) * ∑ k ∈ Finset.Icc 1 K, ((ℓ : ℝ)⁻¹) ^ k + K := hsumk
    _ ≤ ((y : ℝ) + 1) * (1 / ((ℓ : ℝ) - 1)) + Real.logb ℓ D := by gcongr
    _ = ((y : ℝ) + 1) / ((ℓ : ℝ) - 1) + Real.logb ℓ D := by ring

end Formalism.ZetaNonvanishing.LIFTV
