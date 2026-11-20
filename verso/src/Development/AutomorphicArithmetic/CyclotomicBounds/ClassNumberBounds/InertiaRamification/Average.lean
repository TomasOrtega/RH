import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.ConductorLocalPartDvdIff

namespace KStar.Ram

open DirichletCharacter

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
private theorem prime_dvd_finset_lcm {ι : Type*} {p : ℕ} (hp : p.Prime) (s : Finset ι)
    (c : ι → ℕ) : p ∣ s.lcm c ↔ ∃ i ∈ s, p ∣ c i := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [hp.ne_one]
  · intro a t ha ih
    rw [Finset.lcm_insert]
    change p ∣ Nat.lcm (c a) (t.lcm c) ↔ _
    rw [hp.dvd_lcm, ih]
    simp

variable {N : ℕ} [NeZero N] (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem ramIdx_eq_one_iff (X : Subgroup (DirichletCharacter ℂ N)) :
    (ramIdx l X = 1 ↔ ∀ ψ ∈ X, ¬ l ∣ ψ.conductor) ∧ (ramIdx l X = 1 ↔ ¬ l ∣ fieldCond X) ∧
      1 ≤ ramIdx l X := by
  have key : ramIdx l X = 1 ↔ ∀ ψ ∈ X, localPart N l ψ = 1 := by
    unfold ramIdx
    rw [Subgroup.card_eq_one, Subgroup.map_eq_bot_iff]
    exact ⟨fun h ψ hψ => h hψ, fun h ψ hψ => h ψ hψ⟩
  have e1 : ramIdx l X = 1 ↔ ∀ ψ ∈ X, ¬ l ∣ ψ.conductor := by
    rw [key]
    exact forall₂_congr fun ψ _ => (localPart_eq_one_iff l ψ).2
  refine ⟨e1, ?_, ?_⟩
  · rw [e1]
    unfold fieldCond
    rw [prime_dvd_finset_lcm (Fact.out)]
    simp
  · unfold ramIdx
    exact Nat.card_pos

end KStar.Ram
