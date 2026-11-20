import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

/- English proof (translation)
Unfold `primeWeight`. Use `split_ifs`. Evaluate the numerical expressions. Establish `: (2 : ℝ) ≤ p` using `by exact_mod_cast hp.two_le`. Conclude with `div_nonneg zero_le_one (by linarith)`.
-/
theorem primeWeight_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ primeWeight p := by
  unfold primeWeight
  split_ifs
  · norm_num
  · have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    exact div_nonneg zero_le_one (by linarith)

/- English proof (translation)
Establish `h2 : (2 : ℝ) ≤ p` using `by exact_mod_cast hp.two_le`. Unfold `primeWeight`. Use `split_ifs with h`. Substitute `h` using the available equality. Evaluate the numerical expressions.

Rewrite using `[div_le_div_iff₀ (by linarith) (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem primeWeight_le {p : ℕ} (hp : p.Prime) : primeWeight p ≤ 4 / p := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold primeWeight
  split_ifs with h
  · subst h; norm_num
  · rw [div_le_div_iff₀ (by linarith) (by linarith)]
    linarith

/- English proof (translation)
Take `⟨CM, hCM⟩` from `hM`. Introduce `d hd`. Use `set T := d.natAbs.primeFactors with hT`. Use `set K1 : ℝ := ∑ p ∈ T, primeWeight p * Real.log p`. Use `set K2 : ℝ := ∑ p ∈ T, 2 * (padicValInt p d : ℝ) * Real.log p`.

Use `set A : ℝ := |4 * CM + K1 + K2|`. Establish `hl2 : 0 < Real.log 2` using `Real.log_pos (by norm_num)`. Use `⟨4 + A / Real.log 2, fun B hB S hS => ?_⟩` and prove the remaining obligations. Use `set P := (Finset.Iic ⌊B⌋₊).filter Nat.Prime`. Establish `hlogB : Real.log 2 ≤ Real.log B` using `Real.log_le_log (by norm_num) hB`.

Establish `hlog : ∀ p : ℕ, p.Prime → 0 ≤ Real.log p` using `fun p hp => Real.log_nonneg (by exact_mod_cast hp.one_lt.le)`. Establish `hTprime : ∀ p ∈ T, p.Prime` using `fun p hp => (Nat.mem_primeFactors.mp hp).1`. Establish `hPprime : ∀ p ∈ P, p.Prime` using `fun p hp => (Finset.mem_filter.mp hp).2`. Establish `hSsub : S ⊆ P ∪ T`. Introduce `p hp`.

Take `⟨hpp, hpB | hpd⟩` from `hS p hp`. Conclude with `Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr (Nat.le_floor hpB), hpp⟩)`. Conclude with `Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hpp, Int.natCast_dvd.mp hpd, Int.natAbs_ne_zero.mpr hd⟩)`. Establish `hW : ∑ p ∈ S, primeWeight p * Real.log p ≤ 4 * (Real.log B + CM) + K1`. Establish `hnn : ∀ p ∈ P ∪ T, 0 ≤ primeWeight p * Real.log p`.

Introduce `p hp`. Establish `hpp : p.Prime` using `(Finset.mem_union.mp hp).elim (hPprime p) (hTprime p)`. Conclude with `mul_nonneg (primeWeight_nonneg hpp) (hlog p hpp)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Finset.sum_union_inter]`.

Establish `: 0 ≤ ∑ p ∈ P ∩ T, primeWeight p * Real.log p` using `Finset.sum_nonneg fun p hp => hnn p (Finset.mem_union_left _ (Finset.mem_inter.mp hp).1)`. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ ≤ ∑ p ∈ P, 4 * (Real.log p / p) + K1 := by`. Establish `hsum : ∑ p ∈ P, primeWeight p * Real.log p ≤ ∑ p ∈ P, 4 * (Real.log p / p)`. Use `Finset.sum_le_sum fun p hp => ?_` and prove the remaining obligations.

Establish `hpp` using `hPprime p hp`. Establish `hw` using `mul_le_mul_of_nonneg_right (primeWeight_le hpp) (hlog p hpp)`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ ≤ 4 * (Real.log B + CM) + K1 := by`.

Rewrite using `[← Finset.mul_sum]`. Combine the linear relations using `[hCM B hB]`. Establish `hV : ∑ p ∈ S, 2 * (padicValInt p d : ℝ) * Real.log p ≤ K2`. Rewrite using `[← Finset.sum_filter_of_ne (p := fun p => p ∈ T)]`. Apply `Finset.sum_le_sum_of_subset_of_nonneg` to reduce the goal to its premises.

Introduce `p hp`. Conclude with `(Finset.mem_filter.mp hp).2`. Introduce `p hp _`. Conclude with `mul_nonneg (by positivity) (hlog p (hTprime p hp))`. Introduce `p hp hne`.

Assume the negation of the conclusion as `hpT`. Apply `hne` to reduce the goal to its premises. Establish `hpp` using `(hS p hp).1`. Establish `hnd : ¬ (p : ℤ) ∣ d` using `fun hpd => hpT (Nat.mem_primeFactors.mpr ⟨hpp, Int.natCast_dvd.mp hpd, Int.natAbs_ne_zero.mpr hd⟩)`. Rewrite using `[padicValInt.eq_zero_of_not_dvd hnd]`.

Simplify using the standard rewrite rules. Establish `hsplit : ∑ p ∈ S, (primeWeight p + 2 * padicValInt p d) * Real.log p = ∑ p ∈ S, primeWeight p * Real.log p + ∑ p ∈ S, 2 * (padicValInt p d : ℝ) * Real.log p`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun p _ => by ring`. Establish `hA : 4 * CM + K1 + K2 ≤ A` using `le_abs_self _`.

Establish `hA0 : 0 ≤ A` using `abs_nonneg _`. Establish `habs : A ≤ A / Real.log 2 * Real.log B`. Rewrite using `[div_mul_eq_mul_div, le_div_iff₀ hl2]`. Conclude with `mul_le_mul_of_nonneg_left hlogB hA0`. Rewrite using `[hsplit]`.

Use polynomial arithmetic with `[hW, hV, hA, habs]`.
-/
theorem SumCp.proof (hM : MertensUpper.Statement) : SumCp.Statement := by
  obtain ⟨CM, hCM⟩ := hM
  intro d hd
  set T := d.natAbs.primeFactors with hT
  set K1 : ℝ := ∑ p ∈ T, primeWeight p * Real.log p
  set K2 : ℝ := ∑ p ∈ T, 2 * (padicValInt p d : ℝ) * Real.log p
  set A : ℝ := |4 * CM + K1 + K2|
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨4 + A / Real.log 2, fun B hB S hS => ?_⟩
  set P := (Finset.Iic ⌊B⌋₊).filter Nat.Prime
  have hlogB : Real.log 2 ≤ Real.log B := Real.log_le_log (by norm_num) hB
  have hlog : ∀ p : ℕ, p.Prime → 0 ≤ Real.log p := fun p hp =>
    Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hTprime : ∀ p ∈ T, p.Prime := fun p hp => (Nat.mem_primeFactors.mp hp).1
  have hPprime : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have hSsub : S ⊆ P ∪ T := by
    intro p hp
    obtain ⟨hpp, hpB | hpd⟩ := hS p hp
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_Iic.mpr (Nat.le_floor hpB), hpp⟩)
    · exact Finset.mem_union_right _ (Nat.mem_primeFactors.mpr
        ⟨hpp, Int.natCast_dvd.mp hpd, Int.natAbs_ne_zero.mpr hd⟩)

  have hW : ∑ p ∈ S, primeWeight p * Real.log p ≤ 4 * (Real.log B + CM) + K1 := by
    have hnn : ∀ p ∈ P ∪ T, 0 ≤ primeWeight p * Real.log p := by
      intro p hp
      have hpp : p.Prime := (Finset.mem_union.mp hp).elim (hPprime p) (hTprime p)
      exact mul_nonneg (primeWeight_nonneg hpp) (hlog p hpp)
    calc ∑ p ∈ S, primeWeight p * Real.log p
        ≤ ∑ p ∈ P ∪ T, primeWeight p * Real.log p :=
          Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun p hp _ => hnn p hp)
      _ ≤ ∑ p ∈ P, primeWeight p * Real.log p + K1 := by
          rw [← Finset.sum_union_inter]
          have : 0 ≤ ∑ p ∈ P ∩ T, primeWeight p * Real.log p :=
            Finset.sum_nonneg fun p hp => hnn p (Finset.mem_union_left _ (Finset.mem_inter.mp hp).1)
          linarith
      _ ≤ ∑ p ∈ P, 4 * (Real.log p / p) + K1 := by
          have hsum : ∑ p ∈ P, primeWeight p * Real.log p ≤ ∑ p ∈ P, 4 * (Real.log p / p) := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hpp := hPprime p hp
            have hw := mul_le_mul_of_nonneg_right (primeWeight_le hpp) (hlog p hpp)
            calc primeWeight p * Real.log p ≤ 4 / p * Real.log p := hw
              _ = 4 * (Real.log p / p) := by ring
          linarith
      _ ≤ 4 * (Real.log B + CM) + K1 := by
          rw [← Finset.mul_sum]
          linarith [hCM B hB]

  have hV : ∑ p ∈ S, 2 * (padicValInt p d : ℝ) * Real.log p ≤ K2 := by
    rw [← Finset.sum_filter_of_ne (p := fun p => p ∈ T)]
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp; exact (Finset.mem_filter.mp hp).2
      · intro p hp _
        exact mul_nonneg (by positivity) (hlog p (hTprime p hp))
    · intro p hp hne
      by_contra hpT
      apply hne
      have hpp := (hS p hp).1
      have hnd : ¬ (p : ℤ) ∣ d := fun hpd => hpT (Nat.mem_primeFactors.mpr
        ⟨hpp, Int.natCast_dvd.mp hpd, Int.natAbs_ne_zero.mpr hd⟩)
      rw [padicValInt.eq_zero_of_not_dvd hnd]
      simp
  have hsplit : ∑ p ∈ S, (primeWeight p + 2 * padicValInt p d) * Real.log p
      = ∑ p ∈ S, primeWeight p * Real.log p + ∑ p ∈ S, 2 * (padicValInt p d : ℝ) * Real.log p := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hA : 4 * CM + K1 + K2 ≤ A := le_abs_self _
  have hA0 : 0 ≤ A := abs_nonneg _
  have habs : A ≤ A / Real.log 2 * Real.log B := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    exact mul_le_mul_of_nonneg_left hlogB hA0
  rw [hsplit]
  nlinarith [hW, hV, hA, habs]

end GroundTheory.Heights₂.Heights.Model
