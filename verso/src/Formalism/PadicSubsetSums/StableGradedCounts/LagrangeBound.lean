import Formalism.PadicSubsetSums.CentralIdempotents.WindowSums
import Formalism.PadicSubsetSums.StableGradedCounts.PadicDigits

namespace Formalism.IrreducibleCountingLemmas.WindowSums

/- English proof (translation)
Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem sum_le_of_unique {ι : Type} (s : Finset ι) (g : ι → ℕ) (r : ℕ)
    (hle : ∀ i ∈ s, g i ≤ r) (huniq : ∀ i ∈ s, ∀ j ∈ s, g i ≠ 0 → g j ≠ 0 → i = j) :
    ∑ i ∈ s, g i ≤ r := by
  classical
  by_cases h : ∃ i ∈ s, g i ≠ 0
  · obtain ⟨i, hi, hgi⟩ := h
    rw [← Finset.add_sum_erase s g hi]
    have h0 : ∑ j ∈ s.erase i, g j = 0 := Finset.sum_eq_zero fun j hj => by
      by_contra hne
      exact (Finset.ne_of_mem_erase hj) (huniq j (Finset.mem_of_mem_erase hj) i hi hne hgi)
    rw [h0, add_zero]
    exact hle i hi
  · push Not at h
    rw [Finset.sum_eq_zero h]
    exact Nat.zero_le _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Both sides reduce to the same expression. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Use linear arithmetic over natural numbers and integers. Chain the equalities or inequalities of the calculation.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sumPadicValDifferencesLe : LagrangeBoundT := by
  intro l a A' r' Cc hl ha hA hlt hdiv c hc n hn
  have hfact : Fact l.Prime := ⟨hl⟩
  have hlZ : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hnotL : ¬ (l : ℤ) ∣ (l : ℤ) ^ a - 1 := by
    intro h
    have h1 : (l : ℤ) ∣ (l : ℤ) ^ a := dvd_pow_self _ (by omega)
    have h2 : (l : ℤ) ∣ 1 := by
      have h3 := dvd_sub h1 h
      rwa [sub_sub_cancel] at h3
    exact hlZ.not_isUnit (isUnit_of_dvd_one h2)
  have hsep : ∀ x m1 m2 : ℤ, |m1 - m2| < l → (l : ℤ) ∣ x + m1 * ((l : ℤ) ^ a - 1) →
      (l : ℤ) ∣ x + m2 * ((l : ℤ) ^ a - 1) → m1 = m2 := by
    intro x m1 m2 hm h1 h2
    have h3 : (l : ℤ) ∣ (m1 - m2) * ((l : ℤ) ^ a - 1) := by
      have e : (m1 - m2) * ((l : ℤ) ^ a - 1) =
          (x + m1 * ((l : ℤ) ^ a - 1)) - (x + m2 * ((l : ℤ) ^ a - 1)) := by ring
      rw [e]
      exact dvd_sub h1 h2
    rcases hlZ.dvd_or_dvd h3 with h | h
    · have := Int.eq_zero_of_abs_lt_dvd h hm
      linarith
    · exact absurd h hnotL
  have hdv : ∀ z : ℤ, padicValInt l z ≠ 0 → (l : ℤ) ∣ z := by
    intro z hz
    have h := (padicValInt_dvd_iff (p := l) 1 z).mpr (Or.inr (Nat.one_le_iff_ne_zero.mpr hz))
    simpa using h
  have hneg : ∀ z : ℤ, padicValInt l (-z) = padicValInt l z := fun z => by simp [padicValInt]
  have hpow : ∀ k : ℕ, ((l ^ k - 1 : ℕ) : ℤ) = (l : ℤ) ^ k - 1 := fun k => by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hl.pos)]
    push_cast
    ring
  have hper : ∀ c' ∈ Cc, (∑ n' ∈ Finset.range (2 * A'),
      if c' = c ∧ n' = n then 0
      else padicValInt l (((c : ℤ) + n * ((l : ℤ) ^ a - 1)) - ((c' : ℤ) + n' * ((l : ℤ) ^ a - 1)))) ≤
      if c' = c then 0 else r' := by
    intro c' hc'
    by_cases hcc : c' = c
    · subst hcc
      rw [if_pos rfl]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro n' hn'
      rw [Finset.mem_range] at hn'
      split_ifs with h
      · rfl
      · by_contra hne
        have h1 := hdv _ hne
        have hz : ((c' : ℤ) + n * ((l : ℤ) ^ a - 1)) - ((c' : ℤ) + n' * ((l : ℤ) ^ a - 1)) =
            0 + ((n : ℤ) - n') * ((l : ℤ) ^ a - 1) := by ring
        rw [hz] at h1
        have h2 := hsep 0 ((n : ℤ) - n') 0 (by rw [sub_zero, abs_lt]; constructor <;> omega) h1 (by simp)
        exact h ⟨rfl, by omega⟩
    · rw [if_neg hcc]
      obtain ⟨ρ, hρ1, hρr, hρd⟩ := hdiv c hc c' hc' (Ne.symm hcc)
      apply sum_le_of_unique
      · intro n' hn'
        rw [Finset.mem_range] at hn'
        rw [if_neg (fun h => hcc h.1)]
        refine le_trans ?_ hρr
        rcases lt_or_gt_of_ne hcc with hlt' | hgt
        · have hdN : (l ^ a - 1) ∣ (c - c') * (l ^ ρ - 1) := by
            rw [← Int.natCast_dvd_natCast, Nat.cast_mul, hpow, hpow, Nat.cast_sub hlt'.le]
            exact hρd
          have hD := padicValIntShiftLe l a (c - c') ρ ((n : ℤ) - n') hl ha (by omega)
            (lt_of_le_of_lt (Nat.sub_le _ _) (hlt c hc)) hρ1 hdN
            (by rw [abs_lt]; constructor <;> omega)
          have hz : ((c : ℤ) + n * ((l : ℤ) ^ a - 1)) - ((c' : ℤ) + n' * ((l : ℤ) ^ a - 1)) =
              ((c - c' : ℕ) : ℤ) + ((n : ℤ) - n') * ((l : ℤ) ^ a - 1) := by
            rw [Nat.cast_sub hlt'.le]
            ring
          rw [hz]
          exact hD
        · have hdN : (l ^ a - 1) ∣ (c' - c) * (l ^ ρ - 1) := by
            rw [← Int.natCast_dvd_natCast, Nat.cast_mul, hpow, hpow, Nat.cast_sub hgt.le]
            have e : ((c' : ℤ) - c) * ((l : ℤ) ^ ρ - 1) = -(((c : ℤ) - c') * ((l : ℤ) ^ ρ - 1)) := by ring
            rw [e]
            exact dvd_neg.mpr hρd
          have hD := padicValIntShiftLe l a (c' - c) ρ ((n' : ℤ) - n) hl ha (by omega)
            (lt_of_le_of_lt (Nat.sub_le _ _) (hlt c' hc')) hρ1 hdN
            (by rw [abs_lt]; constructor <;> omega)
          have hz : ((c : ℤ) + n * ((l : ℤ) ^ a - 1)) - ((c' : ℤ) + n' * ((l : ℤ) ^ a - 1)) =
              -(((c' - c : ℕ) : ℤ) + ((n' : ℤ) - n) * ((l : ℤ) ^ a - 1)) := by
            rw [Nat.cast_sub hgt.le]
            ring
          rw [hz, hneg]
          exact hD
      · intro i hi j hj hgi hgj
        rw [Finset.mem_range] at hi hj
        rw [if_neg (fun h => hcc h.1)] at hgi hgj
        have h1 := hdv _ hgi
        have h2 := hdv _ hgj
        have ez : ∀ k : ℕ, ((c : ℤ) + n * ((l : ℤ) ^ a - 1)) - ((c' : ℤ) + k * ((l : ℤ) ^ a - 1)) =
            ((c : ℤ) - c') + ((n : ℤ) - k) * ((l : ℤ) ^ a - 1) := fun k => by ring
        rw [ez] at h1 h2
        have := hsep _ _ _ (by rw [abs_lt]; constructor <;> omega) h1 h2
        omega
  calc (∑ c' ∈ Cc, ∑ n' ∈ Finset.range (2 * A'),
        if c' = c ∧ n' = n then 0
        else padicValInt l (((c : ℤ) + n * ((l : ℤ) ^ a - 1)) - ((c' : ℤ) + n' * ((l : ℤ) ^ a - 1))))
      ≤ ∑ c' ∈ Cc, (if c' = c then 0 else r') := Finset.sum_le_sum hper
    _ = (Cc.card - 1) * r' := by
      rw [← Finset.add_sum_erase Cc _ hc, if_pos rfl, zero_add,
        Finset.sum_congr rfl (fun x hx => if_neg (Finset.ne_of_mem_erase hx)), Finset.sum_const,
        smul_eq_mul, Finset.card_erase_of_mem hc]

end Formalism.IrreducibleCountingLemmas.WindowSums
