import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.ConductorLocalPartDvdIff

namespace KStar.Ram

open DirichletCharacter

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using `[hp.ne_one]`. Introduce `a t ha ih`. Rewrite using `[Finset.lcm_insert]`. Express the relevant statement in the definitionally equal form `p ∣ Nat.lcm (c a) (t.lcm c) ↔ _`.

Rewrite using `[hp.dvd_lcm, ih]`. Simplify using the standard rewrite rules.
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
Establish `key : ramIdx l X = 1 ↔ ∀ ψ ∈ X, localPart N l ψ = 1`. Unfold `ramIdx`. Rewrite using `[Subgroup.card_eq_one, Subgroup.map_eq_bot_iff]`. Conclude with `⟨fun h ψ hψ => h hψ, fun h ψ hψ => h ψ hψ⟩`. Establish `e1 : ramIdx l X = 1 ↔ ∀ ψ ∈ X, ¬ l ∣ ψ.conductor`.

Rewrite using `[key]`. Conclude with `forall₂_congr fun ψ _ => (localPart_eq_one_iff l ψ).2`. Use `⟨e1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e1]`. Unfold `fieldCond`.

Rewrite using `[prime_dvd_finset_lcm (Fact.out)]`. Simplify using the standard rewrite rules. Unfold `ramIdx`. Conclude with `Nat.card_pos`.
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
