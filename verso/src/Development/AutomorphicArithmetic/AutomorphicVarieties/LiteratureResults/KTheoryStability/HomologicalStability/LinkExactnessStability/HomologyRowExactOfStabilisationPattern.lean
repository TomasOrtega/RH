import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PermRepSingle

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab.Row

/- English proof (translation)
Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem hMap_zero' {k G : Type} [CommRing k] [Group G] (A B : Rep k G) (n : ℕ) :
    hMap (0 : A ⟶ B) n = 0 := by
  simp [hMap, groupHomology.map]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Fix the arbitrary inputs or assume the hypotheses. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem main : ∀ (k G : Type) [CommRing k] [Group G] (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p),
    (∀ p, d (p + 1) ≫ d p = 0) → ∀ (M : ℕ → ℕ → ModuleCat.{0} k)
    (e : ∀ p q, M p q ⟶ groupHomology (C p) q) (s : ∀ p q, M (p + 1) q ⟶ M p q) (T : ℕ),
    (∀ p q, p ≤ T → IsIso (e p q)) →
    (∀ p q, p + 1 ≤ T → e (p + 1) q ≫ hMap (d p) q = if Even p then s p q ≫ e p q else 0) →
    ∀ p q, p + 2 ≤ T → (Even p → Function.Injective (s p q).hom) →
    (Odd p → Function.Surjective (s (p + 1) q).hom) →
    Function.Exact (hMap (d (p + 1)) q).hom (hMap (d p) q).hom := by
  intro k G _ _ C d hd M e s T hiso hrel p q hp hinj hsurj
  have bij : ∀ p q, p ≤ T → Function.Bijective (e p q).hom := fun p q h =>
    (ConcreteCategory.isIso_iff_bijective (e p q)).1 (hiso p q h)
  have rel : ∀ p q, p + 1 ≤ T → ∀ m, (hMap (d p) q).hom ((e (p + 1) q).hom m) =
      (if Even p then s p q ≫ e p q else 0).hom m :=
    fun p q h m => congrArg (fun f => ModuleCat.Hom.hom f m) (hrel p q h)
  intro y
  obtain ⟨m, rfl⟩ := (bij (p + 1) q (by omega)).2 y
  rcases Nat.even_or_odd p with hev | hod
  · have hnot : ¬ Even (p + 1) := by
      rw [Nat.even_add_one]
      exact not_not.2 hev
    rw [rel p q (by omega), if_pos hev]
    constructor
    · intro h0
      have h1 : (s p q).hom m = 0 := by
        apply (bij p q (by omega)).1
        rw [map_zero]
        exact h0
      have h2 : m = 0 := by
        apply hinj hev
        rw [h1, map_zero]
      exact ⟨0, by rw [h2, map_zero, map_zero]⟩
    · rintro ⟨z, hz⟩
      obtain ⟨w, rfl⟩ := (bij (p + 2) q hp).2 z
      have hw := rel (p + 1) q (by omega) w
      rw [if_neg hnot] at hw
      have hm : (e (p + 1) q).hom m = 0 := by
        rw [← hz]
        exact hw
      have hm0 : m = 0 := (bij (p + 1) q (by omega)).1 (by rw [hm, map_zero])
      rw [hm0, map_zero]
  · have hnot : ¬ Even p := Nat.not_even_iff_odd.2 hod
    have hev1 : Even (p + 1) := hod.add_one
    rw [rel p q (by omega), if_neg hnot]
    constructor
    · intro _
      obtain ⟨w, hw⟩ := hsurj hod m
      refine ⟨(e (p + 2) q).hom w, ?_⟩
      rw [rel (p + 1) q (by omega), if_pos hev1, ← hw]
      rfl
    · intro _
      rfl

end GlobalTheory.HomStab.Row

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
/- English proof (translation)
Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem _root_.GlobalTheory.T.homology_row_exact_of_stabilisation_pattern : ∀ (k G : Type) [CommRing k] [Group G] (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → ∀ (M : ℕ → ℕ → ModuleCat.{0} k) (e : ∀ p q, M p q ⟶ groupHomology (C p) q) (s : ∀ p q, M (p + 1) q ⟶ M p q) (T : ℕ), (∀ p q, p ≤ T → IsIso (e p q)) → (∀ p q, p + 1 ≤ T → e (p + 1) q ≫ hMap (d p) q = if Even p then s p q ≫ e p q else 0) → ∀ p q, p + 2 ≤ T → (Even p → Function.Injective (s p q).hom) → (Odd p → Function.Surjective (s (p + 1) q).hom) → Function.Exact (hMap (d (p + 1)) q).hom (hMap (d p) q).hom := by
  first
  | exact @GlobalTheory.HomStab.Row.main
  | exact @GlobalTheory.HomStab.Row.hMap_zero'
end
