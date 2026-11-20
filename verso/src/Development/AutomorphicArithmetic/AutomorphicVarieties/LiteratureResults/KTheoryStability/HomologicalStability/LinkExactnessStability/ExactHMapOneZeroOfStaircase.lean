import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PermRepSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsSyzygyFactorization
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SurjectiveHMapZeroOfStaircase

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab.StairMid

variable {k G : Type} [CommRing k] [Group G]

def shC (C : ℕ → Rep k G) (Z : Rep k G) : ℕ → Rep k G
  | 0 => Z
  | n + 1 => C (n + 2)

def shD (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p) (Z : Rep k G) (b : C 2 ⟶ Z) :
    ∀ p, shC C Z (p + 1) ⟶ shC C Z p
  | 0 => b
  | p + 1 => d (p + 2)

/- English proof (translation)
Introduce `k G _ _ i C d hd hs hex hH`. Take `⟨Z, ι, hι, b, hse, hbι, hbs, hdb, hexb⟩` from `GlobalTheory.T.exists_syzygy_factorization k G C d hd hs (hex 0 (by omega))`. Establish `hfun : ∀ {A B : Rep k G} (f : A ⟶ B), hMap f i = (groupHomology.functor k G i).map f` using `fun f => rfl`. Establish `hsurj : Function.Surjective (hMap b i).hom`. Use `GlobalTheory.T.surjective_hMap_zero_of_staircase k G i (shC C Z) (shD C d Z b) ?_ hbs ?_ ?_` and prove the remaining obligations.

Introduce `p`. Consider the cases of `p with`. Consider the case `zero => exact hdb`. Consider the case `succ p => exact hd (p + 2)`. Introduce `p hp`.

Consider the cases of `p with`. Consider the case `zero => exact hexb (hex 1 (by omega))`. Consider the case `succ p => exact hex (p + 2) (by omega)`. Introduce `p q hp hpq`. Take `⟨r, rfl⟩ : ∃ r, p = r + 1` from `⟨p - 1, by omega⟩`.

Conclude with `hH (r + 2) q (by omega) (by omega)`. Establish `hles` using `(ShortComplex.moduleCat_exact_iff _).1 (groupHomology.mapShortComplex₂_exact hse i)`. Establish `hcomp : hMap (d 1) i = hMap b i ≫ hMap ι i`. Rewrite using `[hfun, hfun, hfun, ← hbι]`. Conclude with `(groupHomology.functor k G i).map_comp b ι`.

Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨y, hy⟩` from `hles x hx`. Take `⟨z, rfl⟩` from `hsurj y`.

Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[hcomp]`. Conclude with `hy`. Introduce and unpack `⟨z, rfl⟩`. Establish `h0 : hMap (d 1) i ≫ hMap (d 0) i = 0`.

Establish `e` using `(groupHomology.functor k G i).map_comp (d 1) (d 0)`. Rewrite `e` using `[hd 0, Functor.map_zero]`. Rewrite using `[hfun, hfun]`. Conclude with `e.symm`. Rewrite using `[← ModuleCat.comp_apply, h0]`.

Both sides reduce to the same expression.
-/
theorem main : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i + 1 → Function.Exact (d (p + 1)).hom (d p).hom) → (∀ p q, 2 ≤ p → p + q = i + 1 → Function.Exact (hMap (d (p + 1)) q).hom (hMap (d p) q).hom) → Function.Exact (hMap (d 1) i).hom (hMap (d 0) i).hom := by
  intro k G _ _ i C d hd hs hex hH
  obtain ⟨Z, ι, hι, b, hse, hbι, hbs, hdb, hexb⟩ := GlobalTheory.T.exists_syzygy_factorization k G C d hd hs (hex 0 (by omega))
  have hfun : ∀ {A B : Rep k G} (f : A ⟶ B), hMap f i = (groupHomology.functor k G i).map f := fun f => rfl
  have hsurj : Function.Surjective (hMap b i).hom := by
    refine GlobalTheory.T.surjective_hMap_zero_of_staircase k G i (shC C Z) (shD C d Z b) ?_ hbs ?_ ?_
    · intro p
      cases p with
      | zero => exact hdb
      | succ p => exact hd (p + 2)
    · intro p hp
      cases p with
      | zero => exact hexb (hex 1 (by omega))
      | succ p => exact hex (p + 2) (by omega)
    · intro p q hp hpq
      obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
      exact hH (r + 2) q (by omega) (by omega)
  have hles := (ShortComplex.moduleCat_exact_iff _).1 (groupHomology.mapShortComplex₂_exact hse i)
  have hcomp : hMap (d 1) i = hMap b i ≫ hMap ι i := by
    rw [hfun, hfun, hfun, ← hbι]
    exact (groupHomology.functor k G i).map_comp b ι
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hles x hx
    obtain ⟨z, rfl⟩ := hsurj y
    refine ⟨z, ?_⟩
    rw [hcomp]
    exact hy
  · rintro ⟨z, rfl⟩
    have h0 : hMap (d 1) i ≫ hMap (d 0) i = 0 := by
      have e := (groupHomology.functor k G i).map_comp (d 1) (d 0)
      rw [hd 0, Functor.map_zero] at e
      rw [hfun, hfun]
      exact e.symm
    rw [← ModuleCat.comp_apply, h0]
    rfl

end GlobalTheory.HomStab.StairMid

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.HomStab.StairMid.main`.
-/
theorem _root_.GlobalTheory.T.exact_hMap_one_zero_of_staircase : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i + 1 → Function.Exact (d (p + 1)).hom (d p).hom) → (∀ p q, 2 ≤ p → p + q = i + 1 → Function.Exact (hMap (d (p + 1)) q).hom (hMap (d p) q).hom) → Function.Exact (hMap (d 1) i).hom (hMap (d 0) i).hom := by
  first
  | exact @GlobalTheory.HomStab.StairMid.main
end
