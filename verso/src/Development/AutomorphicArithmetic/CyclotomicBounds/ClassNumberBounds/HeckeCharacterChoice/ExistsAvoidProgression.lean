import Mathlib

namespace KStar.Choice

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Supply the required witnesses or components. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem exists_avoid (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (bad : (p : ℕ) → Finset (ZMod p)) (hbad : ∀ p ∈ s, (bad p).card < p) (Y : ℤ) :
    ∃ u : ℤ, Y ≤ u ∧ u < Y + ∏ p ∈ s, (p : ℤ) ∧ ∀ p ∈ s, (u : ZMod p) ∉ bad p := by
  classical
  have hc : ∀ p : ℕ, ∃ c : ℕ, p ∈ s → (c : ZMod p) ∉ bad p := by
    intro p
    by_cases hp : p ∈ s
    · have : Fact p.Prime := ⟨hs p hp⟩
      have h1 : (bad p).card < (Finset.univ : Finset (ZMod p)).card := by
        rw [Finset.card_univ, ZMod.card]; exact hbad p hp
      obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card h1
      exact ⟨c.val, fun _ => by rwa [ZMod.natCast_zmod_val]⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose c hc using hc
  have hne : ∀ p ∈ s, id p ≠ 0 := fun p hp => (hs p hp).ne_zero
  have hco : Set.Pairwise (s : Set ℕ) (Function.onFun Nat.Coprime id) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (hs p hp) (hs q hq)).2 hpq
  obtain ⟨k, hk⟩ := Nat.chineseRemainderOfFinset c id s hne hco
  have hP : (0 : ℤ) < ∏ p ∈ s, (p : ℤ) :=
    Finset.prod_pos fun p hp => by exact_mod_cast (hs p hp).pos
  refine ⟨Y + ((k : ℤ) - Y) % ∏ p ∈ s, (p : ℤ), ?_, ?_, ?_⟩
  · have := Int.emod_nonneg ((k : ℤ) - Y) hP.ne'
    linarith
  · have := Int.emod_lt_of_pos ((k : ℤ) - Y) hP
    linarith
  · intro p hp
    have hd : (p : ℤ) ∣ ∏ p ∈ s, (p : ℤ) := Finset.dvd_prod_of_mem (fun p : ℕ => (p : ℤ)) hp
    have h0 : ((∏ p ∈ s, (p : ℤ) : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hd
    have h1 : ((Y + ((k : ℤ) - Y) % ∏ p ∈ s, (p : ℤ) : ℤ) : ZMod p) = (c p : ZMod p) := by
      rw [Int.emod_def, Int.cast_add, Int.cast_sub, Int.cast_mul, h0, Int.cast_sub,
        Int.cast_natCast, zero_mul, sub_zero, add_sub_cancel]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).2 (hk p hp)
    rw [h1]
    exact hc p hp

end KStar.Choice
