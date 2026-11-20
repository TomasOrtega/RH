import Formalism.PolynomialDimension.DigitClassSize

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.CountingSumsFrames

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma dimPol_mono (k' : ℕ) {a b : ℕ} (h : a ≤ b) : dimPol k' a ≤ dimPol k' b :=
  Nat.choose_le_choose k' (by omega)

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma dimPol_mul_deg (k' b : ℕ) : dimPol k' b * (b + 1 + k') = dimPol k' (b + 1) * (b + 1) := by
  unfold dimPol
  have h := Nat.choose_mul_succ_eq (b + k') k'
  rw [show b + k' + 1 - k' = b + 1 by omega] at h
  rw [show b + 1 + k' = b + k' + 1 by omega]
  exact h

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma dimPol_succ_vars (k' b : ℕ) : dimPol (k' + 1) b * (k' + 1) = (b + k' + 1) * dimPol k' b := by
  unfold dimPol
  rw [show b + (k' + 1) = b + k' + 1 by omega]
  exact (Nat.add_one_mul_choose_eq (b + k') k').symm

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma dimPol_mul_deg_real (k' b : ℕ) :
    (dimPol k' b : ℝ) * ((b : ℝ) + 1 + k') = (dimPol k' (b + 1) : ℝ) * ((b : ℝ) + 1) := by
  exact_mod_cast dimPol_mul_deg k' b

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem harmonic_level_count_rec (k' : ℕ) : ∀ A B : ℕ,
    ∑ j ∈ range (min A B + 1), dimHar k' (A - j) (B - j) = dimPol k' A * dimPol k' B
  | 0, B => by simp [dimHar]
  | A + 1, 0 => by simp [dimHar]
  | A + 1, B + 1 => by
    rw [show min (A + 1) (B + 1) + 1 = (min A B + 1) + 1 by omega, Finset.sum_range_succ']
    have e : ∀ j ∈ range (min A B + 1),
        dimHar k' (A + 1 - (j + 1)) (B + 1 - (j + 1)) = dimHar k' (A - j) (B - j) := by
      intro j _
      rw [show A + 1 - (j + 1) = A - j by omega, show B + 1 - (j + 1) = B - j by omega]
    rw [Finset.sum_congr rfl e, harmonic_level_count_rec k' A B]
    have hle : dimPol k' A * dimPol k' B ≤ dimPol k' (A + 1) * dimPol k' (B + 1) :=
      Nat.mul_le_mul (dimPol_mono k' (by omega)) (dimPol_mono k' (by omega))
    simp only [dimHar, Nat.sub_zero, Nat.add_sub_cancel, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, or_self, if_false]
    exact Nat.add_sub_cancel' hle

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem harmonic_level_count : LevelCount :=
  fun k' A B => harmonic_level_count_rec k' A B

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.
-/
lemma sum_Icc_dimHar (k' A B J : ℕ) (hJ : J ≤ min A B) :
    ∑ j ∈ Icc J (min A B), dimHar k' (A - j) (B - j) = dimPol k' (A - J) * dimPol k' (B - J) := by
  have e : Icc J (min A B) = Ico J (J + (min (A - J) (B - J) + 1)) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> omega
  rw [e, Finset.sum_Ico_eq_sum_range,
    show J + (min (A - J) (B - J) + 1) - J = min (A - J) (B - J) + 1 by omega,
    ← harmonic_level_count_rec k' (A - J) (B - J)]
  apply Finset.sum_congr rfl
  intro i _
  rw [show A - (J + i) = A - J - i by omega, show B - (J + i) = B - J - i by omega]

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma dimPol_ratio (B J : ℕ) (hJ : J ≤ B) : ∀ k' : ℕ,
    (dimPol k' (B - J) : ℝ) ≤ (1 - (J : ℝ) / ((B : ℝ) + k' + 1)) ^ k' * dimPol k' B
  | 0 => by simp [dimPol]
  | k' + 1 => by
    have ih := dimPol_ratio B J hJ k'
    have h1 : (dimPol (k' + 1) (B - J) : ℝ) * ((k' : ℝ) + 1)
        = ((B : ℝ) - J + k' + 1) * dimPol k' (B - J) := by
      have := congrArg (Nat.cast : ℕ → ℝ) (dimPol_succ_vars k' (B - J))
      push_cast [Nat.cast_sub hJ] at this
      linarith
    have h2 : (dimPol (k' + 1) B : ℝ) * ((k' : ℝ) + 1) = ((B : ℝ) + k' + 1) * dimPol k' B := by
      have := congrArg (Nat.cast : ℕ → ℝ) (dimPol_succ_vars k' B)
      push_cast at this
      linarith
    have hJB : (J : ℝ) ≤ B := by exact_mod_cast hJ
    have hB0 : (0 : ℝ) < (B : ℝ) + k' + 1 := by positivity
    have hB1 : (0 : ℝ) < (B : ℝ) + ((k' + 1 : ℕ) : ℝ) + 1 := by positivity
    set x := (J : ℝ) / ((B : ℝ) + k' + 1) with hx
    set y := (J : ℝ) / ((B : ℝ) + ((k' + 1 : ℕ) : ℝ) + 1) with hy
    have hx1 : x ≤ 1 := by rw [hx, div_le_one hB0]; linarith
    have hyx : y ≤ x := by
      rw [hx, hy]
      apply div_le_div_of_nonneg_left (by positivity) hB0
      push_cast; linarith
    have hxe : (1 - x) * ((B : ℝ) + k' + 1) = (B : ℝ) - J + k' + 1 := by
      rw [hx]; field_simp; ring
    have hP0 : (0 : ℝ) ≤ dimPol k' B := by positivity
    have hk : (0 : ℝ) < (k' : ℝ) + 1 := by positivity
    rw [← mul_le_mul_iff_of_pos_right hk, h1]
    calc ((B : ℝ) - J + k' + 1) * dimPol k' (B - J)
        ≤ ((B : ℝ) - J + k' + 1) * ((1 - x) ^ k' * dimPol k' B) :=
          mul_le_mul_of_nonneg_left ih (by linarith)
      _ = (1 - x) ^ (k' + 1) * ((dimPol (k' + 1) B : ℝ) * ((k' : ℝ) + 1)) := by
          rw [h2, ← hxe]; ring
      _ ≤ (1 - y) ^ (k' + 1) * ((dimPol (k' + 1) B : ℝ) * ((k' : ℝ) + 1)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact pow_le_pow_left₀ (by linarith) (by linarith) _
      _ = (1 - y) ^ (k' + 1) * (dimPol (k' + 1) B : ℝ) * ((k' : ℝ) + 1) := by ring

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation.
-/
lemma tail_bound (k' A B J : ℕ) (hJ : J ≤ min A B) :
    ((dimPol k' (A - J) * dimPol k' (B - J) : ℕ) : ℝ) ≤
      (1 - (J : ℝ) / (B + k' + 1)) ^ k' * ((dimPol k' A * dimPol k' B : ℕ) : ℝ) := by
  have hJB' : J ≤ B := le_trans hJ (min_le_right A B)
  have hJB : (J:ℝ) ≤ B := by exact_mod_cast hJB'
  have hx0 : 0 ≤ 1 - (J:ℝ) / ((B:ℝ) + k' + 1) := by
    rw [sub_nonneg, div_le_one (by positivity)]; linarith
  have h1 : (dimPol k' (A - J) : ℝ) ≤ dimPol k' A := by
    exact_mod_cast dimPol_mono k' (Nat.sub_le A J)
  have h2 := dimPol_ratio B J hJB' k'
  rw [Nat.cast_mul, Nat.cast_mul]
  calc (dimPol k' (A - J) : ℝ) * dimPol k' (B - J)
      ≤ dimPol k' A * ((1 - (J:ℝ) / ((B:ℝ) + k' + 1)) ^ k' * dimPol k' B) :=
        mul_le_mul h1 h2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    _ = _ := by ring

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem highLevelTail : LevelTail :=
  fun k' A B J hJ => ⟨sum_Icc_dimHar k' A B J hJ, tail_bound k' A B J hJ⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion.

Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation.

Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Rewrite the conclusion using the stated equalities.

Check the signs of the components of the expression. A detailed English derivation is pending.
-/
theorem level_tail_exp_bound : LevelTailExp := by
  intro k' A B J La b' hk hb hLa hJ hB
  by_cases hJm : J ≤ min A B
  · rw [sum_Icc_dimHar k' A B J hJm]
    refine le_trans (tail_bound k' A B J hJm) ?_
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    have hD : (0:ℝ) < (B:ℝ) + k' + 1 := by positivity
    have hJB : (J:ℝ) ≤ B := by exact_mod_cast le_trans hJm (min_le_right A B)
    have ht1 : 0 ≤ 1 - (J:ℝ) / ((B:ℝ) + k' + 1) := by
      rw [sub_nonneg, div_le_one hD]; linarith
    have hexp : 1 - (J:ℝ) / ((B:ℝ) + k' + 1) ≤ Real.exp (-((J:ℝ) / ((B:ℝ) + k' + 1))) := by
      linarith [Real.add_one_le_exp (-((J:ℝ) / ((B:ℝ) + k' + 1)))]
    have hpow := pow_le_pow_left₀ ht1 hexp k'
    rw [← Real.exp_nat_mul] at hpow
    refine le_trans hpow (Real.exp_le_exp.mpr ?_)
    have hk' : (2:ℝ) ≤ k' := by exact_mod_cast hk
    have hk1 : (k':ℝ) + 1 ≠ 0 := by positivity
    have hb0 : b' ≠ 0 := hb.ne'
    have htb : La * b' / (k' + 1) / (2 * b') ≤ (J:ℝ) / ((B:ℝ) + k' + 1) := by
      calc La * b' / (k' + 1) / (2 * b') ≤ (J:ℝ) / (2 * b') :=
            div_le_div_of_nonneg_right hJ (by positivity)
        _ ≤ (J:ℝ) / ((B:ℝ) + k' + 1) := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hD hB
    have hs : La * b' / (k' + 1) / (2 * b') = La / (2 * ((k':ℝ) + 1)) := by
      field_simp <;> ring
    rw [hs] at htb
    have e3 : (k':ℝ) * (La / (2 * ((k':ℝ) + 1))) - La / 3 = La * ((k':ℝ) - 2) / (6 * ((k':ℝ) + 1)) := by
      field_simp <;> ring
    have n3 : 0 ≤ La * ((k':ℝ) - 2) / (6 * ((k':ℝ) + 1)) := by
      apply div_nonneg (mul_nonneg hLa (by linarith)) (by positivity)
    have m3 := mul_le_mul_of_nonneg_left htb (by linarith : (0:ℝ) ≤ k')
    nlinarith [m3, e3, n3]
  · push_neg at hJm
    rw [Finset.Icc_eq_empty_of_lt hJm, Finset.sum_empty, Nat.cast_zero]
    positivity

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Combine the linear equalities and inequalities to obtain the conclusion. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion.

A detailed English derivation is pending.
-/
theorem harmonic_lower_bound : HarLower := by
  intro k' al be
  by_cases h : al = 0 ∨ be = 0
  · have hd : dimHar k' al be = dimPol k' al * dimPol k' be := by
      unfold dimHar; rw [if_pos h, Nat.sub_zero]
    rw [hd]
    have hP : (0:ℝ) ≤ ((dimPol k' al * dimPol k' be : ℕ) : ℝ) := Nat.cast_nonneg _
    rcases Nat.eq_zero_or_pos (be + k') with h0 | h0
    · have h0' : ((be:ℝ) + k') = 0 := by exact_mod_cast h0
      rw [h0', div_zero]; exact hP
    · have hpos : (0:ℝ) < (be:ℝ) + k' := by exact_mod_cast h0
      rw [mul_div_assoc]
      calc _ ≤ ((dimPol k' al * dimPol k' be : ℕ) : ℝ) * 1 := by
            apply mul_le_mul_of_nonneg_left _ hP
            rw [div_le_one hpos]; linarith [(Nat.cast_nonneg be : (0:ℝ) ≤ be)]
        _ = _ := mul_one _
  · push_neg at h
    obtain ⟨ha, hb⟩ := h
    have hle1 : dimPol k' (al - 1) ≤ dimPol k' al := dimPol_mono k' (Nat.sub_le _ _)
    have hrec := dimPol_mul_deg k' (be - 1)
    rw [show be - 1 + 1 = be by omega] at hrec
    have hd : dimHar k' al be = dimPol k' al * dimPol k' be - dimPol k' (al - 1) * dimPol k' (be - 1) := by
      unfold dimHar; rw [if_neg (by omega)]
    have hle2 : dimPol k' (al - 1) * dimPol k' (be - 1) ≤ dimPol k' al * dimPol k' be :=
      Nat.mul_le_mul hle1 (dimPol_mono k' (Nat.sub_le _ _))
    rw [hd, Nat.cast_sub hle2]
    push_cast
    have hbe : (0:ℝ) < be := by exact_mod_cast Nat.pos_of_ne_zero hb
    have hpos : (0:ℝ) < (be:ℝ) + k' := by positivity
    have hrec' : (dimPol k' (be - 1) : ℝ) * ((be:ℝ) + k') = dimPol k' be * be := by exact_mod_cast hrec
    have hle1' : (dimPol k' (al - 1) : ℝ) ≤ dimPol k' al := by exact_mod_cast hle1
    set Pa := (dimPol k' al : ℝ)
    set Pb := (dimPol k' be : ℝ)
    set Pa1 := (dimPol k' (al - 1) : ℝ)
    set Pb1 := (dimPol k' (be - 1) : ℝ)
    have h3 : Pa1 * (Pb * be) ≤ Pa * (Pb * be) := mul_le_mul_of_nonneg_right hle1' (by positivity)
    have h4 : Pa1 * (Pb1 * ((be:ℝ) + k')) = Pa1 * (Pb * be) := by rw [hrec']
    rw [div_le_iff₀ hpos]
    have e : (Pa * Pb - Pa1 * Pb1) * ((be:ℝ) + k') =
        Pa * Pb * k' + (Pa * (Pb * be) - Pa1 * (Pb1 * ((be:ℝ) + k'))) := by ring
    rw [e, h4]
    linarith

end Formalism.CountingSumsFrames
