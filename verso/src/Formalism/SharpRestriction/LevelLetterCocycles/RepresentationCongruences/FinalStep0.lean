import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TsumThree
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsSumPadicValIntWindowEq

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

/- English proof (translation)
Introduce `J aS eW eU`. Establish `hl' : (11 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hl1 : (1 : ℝ) < l` using `by linarith`. Establish `hxm : (0 : ℝ) < (l : ℝ) - 1` using `by linarith`. Establish `hxi0 : 0 ≤ (l : ℝ)⁻¹` using `by positivity`.

Establish `hyi0 : 0 ≤ ((l : ℝ) - 1)⁻¹` using `inv_nonneg.2 hxm.le`. Establish `hyi10 : ((l : ℝ) - 1)⁻¹ ≤ 1 / 10` using `Formalism.MainNotions.N.FrobeniusPowerSeries.NumericInequalities.p_le hl'`. Establish `hyix : ((l : ℝ) - 1)⁻¹ ≤ 11 / 10 * (l : ℝ)⁻¹` using `Formalism.MainNotions.N.FrobeniusPowerSeries.NumericInequalities.p_le_u hl'`. Establish `hsq : (l : ℝ) / ((l : ℝ) - 1) ^ 2 ≤ 121 / 100 * (l : ℝ)⁻¹` using `Formalism.MainNotions.N.FrobeniusPowerSeries.NumericInequalities.q_le hl'`. Establish `hsq0 : 0 ≤ (l : ℝ) / ((l : ℝ) - 1) ^ 2` using `by positivity`.

Establish `hH1 : H + 1 ≤ 2 * h` using `by omega`. Establish `hHr : (H : ℝ) ≤ h + η` using `by exact_mod_cast hH`. Establish `hMr : (M : ℝ) ≤ h` using `by exact_mod_cast hM`. Establish `hηr : (20 : ℝ) * η ≤ h` using `by exact_mod_cast hη`. Establish `hH1r : (H : ℝ) + 1 ≤ 2 * (h : ℝ)` using `by exact_mod_cast hH1`.

Establish `hH0 : (0 : ℝ) ≤ H` using `Nat.cast_nonneg H`. Establish `hlogH0 : 0 ≤ Real.logb l ((H : ℝ) + 1)` using `Real.logb_nonneg hl1 (by linarith)`. Establish `hlogH : Real.logb l ((H : ℝ) + 1) ≤ Real.logb l (2 * (h : ℝ))` using `Real.logb_le_logb_of_le hl1 (by linarith) hH1r`. Establish `hW : (eW : ℝ) ≤ (H : ℝ) * ((l : ℝ) / ((l : ℝ) - 1) ^ 2) + 3 + Real.logb l ((H : ℝ) + 1)`. Establish `h0 : 0 ≤ (H : ℝ) * l / ((l : ℝ) - 1) ^ 2 + 3 + Real.logb l ((H : ℝ) + 1)`.

Establish `: 0 ≤ (H : ℝ) * l / ((l : ℝ) - 1) ^ 2` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Establish `hHsq : (H : ℝ) * ((l : ℝ) / ((l : ℝ) - 1) ^ 2) ≤ ((h : ℝ) + η) * (121 / 100 * (l : ℝ)⁻¹)` using `mul_le_mul hHr hsq hsq0 (by positivity)`. Establish `hηxi : (20 * (η : ℝ)) * (l : ℝ)⁻¹ ≤ (h : ℝ) * (l : ℝ)⁻¹` using `mul_le_mul_of_nonneg_right hηr hxi0`.

Establish `hl1n : ((l - 1 : ℕ) : ℝ) = (l : ℝ) - 1`. Rewrite using `[Nat.cast_sub (by omega : 1 ≤ l), Nat.cast_one]`. Establish `hA : (aS : ℝ) ≤ (M : ℝ) * ((l : ℝ) - 1)⁻¹ + 1`. Establish `hd : ((M / (l - 1) : ℕ) : ℝ) ≤ (M : ℝ) / ((l - 1 : ℕ) : ℝ)` using `Nat.cast_div_le`. Rewrite `hd` using `[hl1n, div_eq_mul_inv]`.

Establish `he : (aS : ℝ) = ((M / (l - 1) : ℕ) : ℝ) + 1` using `by show ((M / (l - 1) + 1 : ℕ) : ℝ) = ((M / (l - 1) : ℕ) : ℝ) + 1`. Rewrite using `[Nat.cast_add, Nat.cast_one]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hF : (padicValNat l aS.factorial : ℝ) ≤ (aS : ℝ) * ((l : ℝ) - 1)⁻¹`. Establish `hfa` using `padicValNat_factorial_le_div_sub_one' l aS`.

Rewrite `hfa` using `[div_eq_mul_inv]`. Then use the resulting hypothesis. Establish `hFA : (aS : ℝ) * ((l : ℝ) - 1)⁻¹ ≤ ((M : ℝ) * ((l : ℝ) - 1)⁻¹ + 1) * ((l : ℝ) - 1)⁻¹` using `mul_le_mul_of_nonneg_right hA hyi0`. Establish `hyy : ((l : ℝ) - 1)⁻¹ * ((l : ℝ) - 1)⁻¹ ≤ 11 / 100 * (l : ℝ)⁻¹`. Establish `hq` using `mul_le_mul_of_nonneg_right hyi10 hyi0`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hMyy : (M : ℝ) * (((l : ℝ) - 1)⁻¹ * ((l : ℝ) - 1)⁻¹) ≤ (h : ℝ) * (11 / 100 * (l : ℝ)⁻¹)` using `mul_le_mul hMr hyy (mul_self_nonneg _) (Nat.cast_nonneg h)`. Establish `hMy : (M : ℝ) * ((l : ℝ) - 1)⁻¹ ≤ (h : ℝ) * (11 / 10 * (l : ℝ)⁻¹)` using `mul_le_mul hMr hyix hyi0 (Nat.cast_nonneg h)`. Establish `hhy : (h : ℝ) * ((l : ℝ) - 1)⁻¹ ≤ (h : ℝ) * (11 / 10 * (l : ℝ)⁻¹)` using `mul_le_mul_of_nonneg_left hyix (Nat.cast_nonneg h)`. Establish `hJsub : J ⊆ Finset.Ico (-(M : ℤ)) (-(M : ℤ) + (M : ℤ)) ∪ Finset.Ico (1 : ℤ) (1 + ((h + M : ℕ) : ℤ))`. Introduce `j hjJ`.

Break down `Finset.mem_union.1 hjJ with hA' | hB'` into its components or cases. Take `⟨hA1, hne⟩` from `Finset.mem_filter.1 hA'`. Take `⟨p, hp, rfl⟩` from `Finset.mem_image.1 hA1`. Take `⟨hp1, hp2⟩` from `Finset.mem_product.1 hp`. Take `⟨ht1, ht2⟩` from `Finset.mem_Icc.1 hp2`.

Take `⟨hu1, hu2⟩` from `hj p.1 hp1`. Rewrite using `[Finset.mem_union, Finset.mem_Ico, Finset.mem_Ico]`. Use `push_cast`. Use linear arithmetic over natural numbers and integers. Take `⟨hj1, hj2⟩` from `Finset.mem_Icc.1 hB'`.

Rewrite using `[Finset.mem_union, Finset.mem_Ico, Finset.mem_Ico]`. Use `push_cast`. Use linear arithmetic over natural numbers and integers. Establish `hw1` using `sum_padicValInt_window_le l (-(M : ℤ)) M M (by`. Introduce `i hi`.

Rewrite `hi` using `[Finset.mem_Ico]`. Conclude with `⟨by omega, abs_le.2 ⟨by omega, by omega⟩⟩)`. Establish `hw2` using `sum_padicValInt_window_le l (1 : ℤ) (h + M) (h + M) (by`. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_Ico]`.

Move the coercions through the operations in `at hi ⊢`. Conclude with `⟨by omega, abs_le.2 ⟨by omega, by omega⟩⟩)`. Establish `hdisj : Disjoint (Finset.Ico (-(M : ℤ)) (-(M : ℤ) + (M : ℤ))) (Finset.Ico (1 : ℤ) (1 + ((h + M : ℕ) : ℤ)))`. Rewrite using `[Finset.disjoint_left]`. Introduce `x hx hy`.

Rewrite `hx`, `hy` using `[Finset.mem_Ico]`. Use linear arithmetic over natural numbers and integers. Establish `hle : ∑ j ∈ J, padicValInt l j ≤ ∑ j ∈ Finset.Ico (-(M : ℤ)) (-(M : ℤ) + (M : ℤ)), padicValInt l j + ∑ j ∈ Finset.Ico (1 : ℤ) (1 + ((h + M : ℕ) : ℤ)), padicValInt l j`. Rewrite using `[← Finset.sum_union hdisj]`. Conclude with `Finset.sum_le_sum_of_subset hJsub`.

Establish `hler : ((∑ j ∈ J, padicValInt l j : ℕ) : ℝ) ≤ ((∑ j ∈ Finset.Ico (-(M : ℤ)) (-(M : ℤ) + (M : ℤ)), padicValInt l j : ℕ) : ℝ) + ((∑ j ∈ Finset.Ico (1 : ℤ) (1 + ((h + M : ℕ) : ℤ)), padicValInt l j : ℕ) : ℝ)`. Conclude with `hle` after adjusting the coercions. Establish `hcM : ((h + M : ℕ) : ℝ) = (h : ℝ) + M` using `Nat.cast_add h M`. Rewrite `hw2` using `[hcM, div_eq_mul_inv]`. Rewrite `hw1` using `[div_eq_mul_inv]`.

Establish `hU : ((2 * eW + eU : ℕ) : ℝ) = 2 * (eW : ℝ) + ((∑ j ∈ J, padicValInt l j : ℕ) : ℝ) + (aS : ℝ) + (padicValNat l aS.factorial : ℝ)` using `by show ((2 * eW + ((∑ j ∈ J, padicValInt l j) + aS + padicValNat l aS.factorial) : ℕ) : ℝ) = _`. Simplify using `only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hU]`. Establish `hgoal : (71 : ℝ) / 10 * (h : ℝ) / l = 71 / 10 * ((h : ℝ) * (l : ℝ)⁻¹)` using `by ring`.

Rewrite using `[hgoal]`. Establish `hhx : 0 ≤ (h : ℝ) * (l : ℝ)⁻¹` using `mul_nonneg (Nat.cast_nonneg h) hxi0`. Combine the linear relations using `[hW, hHsq, hηxi, hlogH, hler, hw1, hw2, hA, hF, hFA, hMyy, hMy, hhy, hyi10]`.
-/
theorem lift_le (l : ℕ) [Fact l.Prime] (hl : 11 ≤ l) (h η H M : ℕ) (h1 : 1 ≤ h) (hη : 20 * η ≤ h)
    (hH : H ≤ h + η) (hM : M ≤ h) (jumps : Finset ℤ)
    (hj : ∀ u ∈ jumps, -(M : ℤ) ≤ u ∧ u ≤ h) :
    let J : Finset ℤ :=
      ((jumps ×ˢ Finset.Icc (1 : ℤ) M).image (fun p : ℤ × ℤ => p.1 + p.2)).filter (fun j => j ≠ 0) ∪
        Finset.Icc (1 : ℤ) M
    let aS : ℕ := M / (l - 1) + 1
    let eW : ℕ := ⌊(H : ℝ) * l / ((l : ℝ) - 1) ^ 2 + 3 + Real.logb l ((H : ℝ) + 1)⌋₊
    let eU : ℕ := (∑ j ∈ J, padicValInt l j) + aS + padicValNat l aS.factorial
    ((2 * eW + eU : ℕ) : ℝ) ≤ 71 / 10 * (h : ℝ) / l + 71 / 10 + 2 * Real.logb l (2 * (h : ℝ)) := by
  intro J aS eW eU
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hl1 : (1 : ℝ) < l := by linarith
  have hxm : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  have hxi0 : 0 ≤ (l : ℝ)⁻¹ := by positivity
  have hyi0 : 0 ≤ ((l : ℝ) - 1)⁻¹ := inv_nonneg.2 hxm.le
  have hyi10 : ((l : ℝ) - 1)⁻¹ ≤ 1 / 10 := Formalism.MainNotions.N.FrobeniusPowerSeries.NumericInequalities.p_le hl'
  have hyix : ((l : ℝ) - 1)⁻¹ ≤ 11 / 10 * (l : ℝ)⁻¹ := Formalism.MainNotions.N.FrobeniusPowerSeries.NumericInequalities.p_le_u hl'
  have hsq : (l : ℝ) / ((l : ℝ) - 1) ^ 2 ≤ 121 / 100 * (l : ℝ)⁻¹ := Formalism.MainNotions.N.FrobeniusPowerSeries.NumericInequalities.q_le hl'
  have hsq0 : 0 ≤ (l : ℝ) / ((l : ℝ) - 1) ^ 2 := by positivity
  have hH1 : H + 1 ≤ 2 * h := by omega
  have hHr : (H : ℝ) ≤ h + η := by exact_mod_cast hH
  have hMr : (M : ℝ) ≤ h := by exact_mod_cast hM
  have hηr : (20 : ℝ) * η ≤ h := by exact_mod_cast hη
  have hH1r : (H : ℝ) + 1 ≤ 2 * (h : ℝ) := by exact_mod_cast hH1
  have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hlogH0 : 0 ≤ Real.logb l ((H : ℝ) + 1) := Real.logb_nonneg hl1 (by linarith)
  have hlogH : Real.logb l ((H : ℝ) + 1) ≤ Real.logb l (2 * (h : ℝ)) :=
    Real.logb_le_logb_of_le hl1 (by linarith) hH1r
  have hW : (eW : ℝ) ≤ (H : ℝ) * ((l : ℝ) / ((l : ℝ) - 1) ^ 2) + 3 + Real.logb l ((H : ℝ) + 1) := by
    have h0 : 0 ≤ (H : ℝ) * l / ((l : ℝ) - 1) ^ 2 + 3 + Real.logb l ((H : ℝ) + 1) := by
      have : 0 ≤ (H : ℝ) * l / ((l : ℝ) - 1) ^ 2 := by positivity
      linarith
    calc (eW : ℝ) ≤ (H : ℝ) * l / ((l : ℝ) - 1) ^ 2 + 3 + Real.logb l ((H : ℝ) + 1) :=
          Nat.floor_le h0
      _ = (H : ℝ) * ((l : ℝ) / ((l : ℝ) - 1) ^ 2) + 3 + Real.logb l ((H : ℝ) + 1) := by ring
  have hHsq : (H : ℝ) * ((l : ℝ) / ((l : ℝ) - 1) ^ 2) ≤ ((h : ℝ) + η) * (121 / 100 * (l : ℝ)⁻¹) :=
    mul_le_mul hHr hsq hsq0 (by positivity)
  have hηxi : (20 * (η : ℝ)) * (l : ℝ)⁻¹ ≤ (h : ℝ) * (l : ℝ)⁻¹ := mul_le_mul_of_nonneg_right hηr hxi0
  have hl1n : ((l - 1 : ℕ) : ℝ) = (l : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ l), Nat.cast_one]
  have hA : (aS : ℝ) ≤ (M : ℝ) * ((l : ℝ) - 1)⁻¹ + 1 := by
    have hd : ((M / (l - 1) : ℕ) : ℝ) ≤ (M : ℝ) / ((l - 1 : ℕ) : ℝ) := Nat.cast_div_le
    rw [hl1n, div_eq_mul_inv] at hd
    have he : (aS : ℝ) = ((M / (l - 1) : ℕ) : ℝ) + 1 := by
      show ((M / (l - 1) + 1 : ℕ) : ℝ) = ((M / (l - 1) : ℕ) : ℝ) + 1
      rw [Nat.cast_add, Nat.cast_one]
    linarith
  have hF : (padicValNat l aS.factorial : ℝ) ≤ (aS : ℝ) * ((l : ℝ) - 1)⁻¹ := by
    have hfa := padicValNat_factorial_le_div_sub_one' l aS
    rwa [div_eq_mul_inv] at hfa
  have hFA : (aS : ℝ) * ((l : ℝ) - 1)⁻¹ ≤ ((M : ℝ) * ((l : ℝ) - 1)⁻¹ + 1) * ((l : ℝ) - 1)⁻¹ :=
    mul_le_mul_of_nonneg_right hA hyi0
  have hyy : ((l : ℝ) - 1)⁻¹ * ((l : ℝ) - 1)⁻¹ ≤ 11 / 100 * (l : ℝ)⁻¹ := by
    have hq := mul_le_mul_of_nonneg_right hyi10 hyi0
    linarith
  have hMyy : (M : ℝ) * (((l : ℝ) - 1)⁻¹ * ((l : ℝ) - 1)⁻¹) ≤ (h : ℝ) * (11 / 100 * (l : ℝ)⁻¹) :=
    mul_le_mul hMr hyy (mul_self_nonneg _) (Nat.cast_nonneg h)
  have hMy : (M : ℝ) * ((l : ℝ) - 1)⁻¹ ≤ (h : ℝ) * (11 / 10 * (l : ℝ)⁻¹) :=
    mul_le_mul hMr hyix hyi0 (Nat.cast_nonneg h)
  have hhy : (h : ℝ) * ((l : ℝ) - 1)⁻¹ ≤ (h : ℝ) * (11 / 10 * (l : ℝ)⁻¹) :=
    mul_le_mul_of_nonneg_left hyix (Nat.cast_nonneg h)
  have hJsub : J ⊆ Finset.Ico (-(M : ℤ)) (-(M : ℤ) + (M : ℤ)) ∪
      Finset.Ico (1 : ℤ) (1 + ((h + M : ℕ) : ℤ)) := by
    intro j hjJ
    rcases Finset.mem_union.1 hjJ with hA' | hB'
    · obtain ⟨hA1, hne⟩ := Finset.mem_filter.1 hA'
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hA1
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hp
      obtain ⟨ht1, ht2⟩ := Finset.mem_Icc.1 hp2
      obtain ⟨hu1, hu2⟩ := hj p.1 hp1
      rw [Finset.mem_union, Finset.mem_Ico, Finset.mem_Ico]
      push_cast
      omega
    · obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hB'
      rw [Finset.mem_union, Finset.mem_Ico, Finset.mem_Ico]
      push_cast
      omega
  have hw1 := sum_padicValInt_window_le l (-(M : ℤ)) M M (by
    intro i hi
    rw [Finset.mem_Ico] at hi
    exact ⟨by omega, abs_le.2 ⟨by omega, by omega⟩⟩)
  have hw2 := sum_padicValInt_window_le l (1 : ℤ) (h + M) (h + M) (by
    intro i hi
    rw [Finset.mem_Ico] at hi
    push_cast at hi ⊢
    exact ⟨by omega, abs_le.2 ⟨by omega, by omega⟩⟩)
  have hdisj : Disjoint (Finset.Ico (-(M : ℤ)) (-(M : ℤ) + (M : ℤ)))
      (Finset.Ico (1 : ℤ) (1 + ((h + M : ℕ) : ℤ))) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    rw [Finset.mem_Ico] at hx hy
    omega
  have hle : ∑ j ∈ J, padicValInt l j ≤
      ∑ j ∈ Finset.Ico (-(M : ℤ)) (-(M : ℤ) + (M : ℤ)), padicValInt l j +
        ∑ j ∈ Finset.Ico (1 : ℤ) (1 + ((h + M : ℕ) : ℤ)), padicValInt l j := by
    rw [← Finset.sum_union hdisj]
    exact Finset.sum_le_sum_of_subset hJsub
  have hler : ((∑ j ∈ J, padicValInt l j : ℕ) : ℝ) ≤
      ((∑ j ∈ Finset.Ico (-(M : ℤ)) (-(M : ℤ) + (M : ℤ)), padicValInt l j : ℕ) : ℝ) +
        ((∑ j ∈ Finset.Ico (1 : ℤ) (1 + ((h + M : ℕ) : ℤ)), padicValInt l j : ℕ) : ℝ) := by
    exact_mod_cast hle
  have hcM : ((h + M : ℕ) : ℝ) = (h : ℝ) + M := Nat.cast_add h M
  rw [hcM, div_eq_mul_inv] at hw2
  rw [div_eq_mul_inv] at hw1
  have hU : ((2 * eW + eU : ℕ) : ℝ) = 2 * (eW : ℝ) + ((∑ j ∈ J, padicValInt l j : ℕ) : ℝ) +
      (aS : ℝ) + (padicValNat l aS.factorial : ℝ) := by
    show ((2 * eW + ((∑ j ∈ J, padicValInt l j) + aS + padicValNat l aS.factorial) : ℕ) : ℝ) = _
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [hU]
  have hgoal : (71 : ℝ) / 10 * (h : ℝ) / l = 71 / 10 * ((h : ℝ) * (l : ℝ)⁻¹) := by ring
  rw [hgoal]
  have hhx : 0 ≤ (h : ℝ) * (l : ℝ)⁻¹ := mul_nonneg (Nat.cast_nonneg h) hxi0
  linarith [hW, hHsq, hηxi, hlogH, hler, hw1, hw2, hA, hF, hFA, hMyy, hMy, hhy, hyi10]

/- English proof (translation)
Establish `hl' : (11 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hl1 : (1 : ℝ) < l` using `by linarith`. Establish `hX : ((b + η + S : ℕ) : ℝ) = (b : ℝ) + η + S` using `by push_cast; ring`. Establish `hb1 : (1 : ℝ) ≤ b` using `by exact_mod_cast hb`. Establish `hηr : (20 : ℝ) * η ≤ b` using `by exact_mod_cast hηb`.

Establish `hSr : (20 : ℝ) * S ≤ b` using `by exact_mod_cast hSb`. Establish `hη0 : (0 : ℝ) ≤ η` using `Nat.cast_nonneg η`. Establish `hS0 : (0 : ℝ) ≤ S` using `Nat.cast_nonneg S`. Establish `hX1 : (1 : ℝ) ≤ ((b + η + S : ℕ) : ℝ)` using `by rw [hX]; linarith`. Establish `hL : 0 ≤ Real.logb l (2 * ((b + η + S : ℕ) : ℝ))` using `Real.logb_nonneg hl1 (by linarith)`.

Establish `hE : Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) + 1 ≤ Sg l (b + η + S) w S η`. Unfold `Sg`. Establish `e1 : 0 ≤ ((b + η + S : ℕ) : ℝ) / (l : ℝ) ^ 2` using `by positivity`. Establish `e2 : 0 ≤ ((w : ℝ) + S + η) / l` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hdiv : 71 / 10 * ((b + η + S : ℕ) : ℝ) / l ≤ 71 / 10 * ((b + η + S : ℕ) : ℝ) / 11` using `by gcongr`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem step0 (l : ℕ) (hl : 11 ≤ l) (b w S η : ℕ) (hb : 1 ≤ b) (hηb : 20 * η ≤ b) (hSb : 20 * S ≤ b)
    (hwb : 20 * w ≤ b) (hsm : (b : ℝ) / 4 < 40 * Sg l (b + η + S) w S η) :
    71 / 10 * ((b + η + S : ℕ) : ℝ) / l + 71 / 10 + 2 * Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) ≤
      160 * Sg l (b + η + S) w S η := by
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hl1 : (1 : ℝ) < l := by linarith
  have hX : ((b + η + S : ℕ) : ℝ) = (b : ℝ) + η + S := by push_cast; ring
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hηr : (20 : ℝ) * η ≤ b := by exact_mod_cast hηb
  have hSr : (20 : ℝ) * S ≤ b := by exact_mod_cast hSb
  have hη0 : (0 : ℝ) ≤ η := Nat.cast_nonneg η
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg S
  have hX1 : (1 : ℝ) ≤ ((b + η + S : ℕ) : ℝ) := by rw [hX]; linarith
  have hL : 0 ≤ Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) := Real.logb_nonneg hl1 (by linarith)
  have hE : Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) + 1 ≤ Sg l (b + η + S) w S η := by
    unfold Sg
    have e1 : 0 ≤ ((b + η + S : ℕ) : ℝ) / (l : ℝ) ^ 2 := by positivity
    have e2 : 0 ≤ ((w : ℝ) + S + η) / l := by positivity
    linarith
  have hdiv : 71 / 10 * ((b + η + S : ℕ) : ℝ) / l ≤ 71 / 10 * ((b + η + S : ℕ) : ℝ) / 11 := by
    gcongr
  linarith

def bandBound (l h w S η : ℕ) (band : ℝ) : ℝ :=
  (h : ℝ) / (l : ℝ) ^ 2 + ((w : ℝ) + η) / l + S + 1 + Real.logb l (2 * (h : ℝ)) + η * band

def brOne (l h w S η R : ℕ) (band : ℝ) : ℝ :=
  (h : ℝ) / (l : ℝ) ^ 2 + ((w : ℝ) + η) / l + (R : ℝ) ^ 2 * (S + 1 + Real.logb l (2 * (h : ℝ))) +
    η * band

end Formalism.MainNotions.N.FrobeniusPowerSeries
