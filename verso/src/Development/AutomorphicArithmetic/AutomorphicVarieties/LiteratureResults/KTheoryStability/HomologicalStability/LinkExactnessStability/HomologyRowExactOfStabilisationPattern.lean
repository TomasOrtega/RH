import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PermRepSingle

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab.Row

/- English proof (translation)
Simplify using `[hMap, groupHomology.map]`. Both sides reduce to the same expression.
-/
theorem hMap_zero' {k G : Type} [CommRing k] [Group G] (A B : Rep k G) (n : ℕ) :
    hMap (0 : A ⟶ B) n = 0 := by
  simp [hMap, groupHomology.map]
  rfl

/- English proof (translation)
Introduce `k G _ _ C d hd M e s T hiso hrel p q hp hinj hsurj`. Establish `bij : ∀ p q, p ≤ T → Function.Bijective (e p q).hom` using `fun p q h => (ConcreteCategory.isIso_iff_bijective (e p q)).1 (hiso p q h)`. Establish `rel : ∀ p q, p + 1 ≤ T → ∀ m, (hMap (d p) q).hom ((e (p + 1) q).hom m) = (if Even p then s p q ≫ e p q else 0).hom m` using `fun p q h m => congrArg (fun f => ModuleCat.Hom.hom f m) (hrel p q h)`. Introduce `y`. Take `⟨m, rfl⟩` from `(bij (p + 1) q (by omega)).2 y`.

Break down `Nat.even_or_odd p with hev | hod` into its components or cases. Establish `hnot : ¬ Even (p + 1)`. Rewrite using `[Nat.even_add_one]`. Conclude with `not_not.2 hev`. Rewrite using `[rel p q (by omega), if_pos hev]`.

Prove the components needed by the constructor for the conclusion. Introduce `h0`. Establish `h1 : (s p q).hom m = 0`. Apply `(bij p q (by omega)).1` to reduce the goal to its premises. Rewrite using `[map_zero]`.

Conclude with `h0`. Establish `h2 : m = 0`. Apply `hinj hev` to reduce the goal to its premises. Rewrite using `[h1, map_zero]`. Conclude with `⟨0, by rw [h2, map_zero, map_zero]⟩`.

Introduce and unpack `⟨z, hz⟩`. Take `⟨w, rfl⟩` from `(bij (p + 2) q hp).2 z`. Establish `hw` using `rel (p + 1) q (by omega) w`. Rewrite `hw` using `[if_neg hnot]`. Establish `hm : (e (p + 1) q).hom m = 0`.

Rewrite using `[← hz]`. Conclude with `hw`. Establish `hm0 : m = 0` using `(bij (p + 1) q (by omega)).1 (by rw [hm, map_zero])`. Rewrite using `[hm0, map_zero]`. Establish `hnot : ¬ Even p` using `Nat.not_even_iff_odd.2 hod`.

Establish `hev1 : Even (p + 1)` using `hod.add_one`. Rewrite using `[rel p q (by omega), if_neg hnot]`. Prove the components needed by the constructor for the conclusion. Introduce `_`. Take `⟨w, hw⟩` from `hsurj hod m`.

Use `⟨(e (p + 2) q).hom w, ?_⟩` and prove the remaining obligations. Rewrite using `[rel (p + 1) q (by omega), if_pos hev1, ← hw]`. Both sides reduce to the same expression. Introduce `_`. Both sides reduce to the same expression.
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
Use `first`. Consider the case `exact @GlobalTheory.HomStab.Row.main`. Consider the case `exact @GlobalTheory.HomStab.Row.hMap_zero'`.
-/
theorem _root_.GlobalTheory.T.homology_row_exact_of_stabilisation_pattern : ∀ (k G : Type) [CommRing k] [Group G] (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → ∀ (M : ℕ → ℕ → ModuleCat.{0} k) (e : ∀ p q, M p q ⟶ groupHomology (C p) q) (s : ∀ p q, M (p + 1) q ⟶ M p q) (T : ℕ), (∀ p q, p ≤ T → IsIso (e p q)) → (∀ p q, p + 1 ≤ T → e (p + 1) q ≫ hMap (d p) q = if Even p then s p q ≫ e p q else 0) → ∀ p q, p + 2 ≤ T → (Even p → Function.Injective (s p q).hom) → (Odd p → Function.Surjective (s (p + 1) q).hom) → Function.Exact (hMap (d (p + 1)) q).hom (hMap (d p) q).hom := by
  first
  | exact @GlobalTheory.HomStab.Row.main
  | exact @GlobalTheory.HomStab.Row.hMap_zero'
end
