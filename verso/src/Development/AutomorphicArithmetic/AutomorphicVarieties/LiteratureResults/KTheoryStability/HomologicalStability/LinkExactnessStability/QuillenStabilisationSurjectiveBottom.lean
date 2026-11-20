import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PermRepSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SurjectiveHMapZeroOfStaircase
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.HomologyRowExactOfStabilisationPattern

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

/- English proof (translation)
Introduce `k G _ _ i C d hd hs hex M e s hiso hsq hinj hsur`. Establish `hsurjH : Function.Surjective (hMap (d 0) i).hom`. Use `GlobalTheory.T.surjective_hMap_zero_of_staircase k G i C d hd hs hex ?_` and prove the remaining obligations. Introduce `p q hp hpq`. Use `GlobalTheory.T.homology_row_exact_of_stabilisation_pattern k G C d hd M e s (i + 2) hiso hsq p q (by omega) ?_ ?_` and prove the remaining obligations.

Introduce `hev`. Conclude with `hinj p q hev (by obtain ⟨r, hr⟩ := hev; omega) hpq`. Introduce `hodd`. Conclude with `hsur (p + 1) q hodd.add_one (by omega) (by omega)`. Establish `h0 : e 1 i ≫ hMap (d 0) i = s 0 i ≫ e 0 i`.

Establish `hev : Even 0` using `⟨0, rfl⟩`. Rewrite using `[hsq 0 i (by omega)]`. Conclude with `if_pos hev`. Use `haveI := hiso 0 i (by omega)`. Use `haveI := hiso 1 i (by omega)`.

Establish `b0` using `ConcreteCategory.bijective_of_isIso (e 0 i)`. Establish `b1` using `ConcreteCategory.bijective_of_isIso (e 1 i)`. Introduce `y`. Take `⟨w, hw⟩` from `hsurjH (e 0 i y)`. Take `⟨x, rfl⟩` from `b1.2 w`.

Use `⟨x, b0.1 ?_⟩` and prove the remaining obligations. Rewrite using `[← hw]`. Establish `h1` using `congrArg (fun f : M 1 i ⟶ groupHomology (C 0) i => f.hom x) h0`. Simplify using `using h1.symm`.
-/
theorem stab_surj_bottom : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i → Function.Exact (d (p + 1)).hom (d p).hom) → ∀ (M : ℕ → ℕ → ModuleCat.{0} k) (e : ∀ p q, M p q ⟶ groupHomology (C p) q) (s : ∀ p q, M (p + 1) q ⟶ M p q), (∀ p q, p ≤ i + 2 → IsIso (e p q)) → (∀ p q, p + 1 ≤ i + 2 → e (p + 1) q ≫ hMap (d p) q = if Even p then s p q ≫ e p q else 0) → (∀ p q, Even p → 2 ≤ p → p + q = i → Function.Injective (s p q).hom) → (∀ p q, Even p → 2 ≤ p → p + q = i + 1 → Function.Surjective (s p q).hom) → Function.Surjective (s 0 i).hom := by
  intro k G _ _ i C d hd hs hex M e s hiso hsq hinj hsur
  have hsurjH : Function.Surjective (hMap (d 0) i).hom := by
    refine GlobalTheory.T.surjective_hMap_zero_of_staircase k G i C d hd hs hex ?_
    intro p q hp hpq
    refine GlobalTheory.T.homology_row_exact_of_stabilisation_pattern k G C d hd M e s (i + 2) hiso hsq p q (by omega) ?_ ?_
    · intro hev
      exact hinj p q hev (by obtain ⟨r, hr⟩ := hev; omega) hpq
    · intro hodd
      exact hsur (p + 1) q hodd.add_one (by omega) (by omega)
  have h0 : e 1 i ≫ hMap (d 0) i = s 0 i ≫ e 0 i := by
    have hev : Even 0 := ⟨0, rfl⟩
    rw [hsq 0 i (by omega)]
    exact if_pos hev
  haveI := hiso 0 i (by omega)
  haveI := hiso 1 i (by omega)
  have b0 := ConcreteCategory.bijective_of_isIso (e 0 i)
  have b1 := ConcreteCategory.bijective_of_isIso (e 1 i)
  intro y
  obtain ⟨w, hw⟩ := hsurjH (e 0 i y)
  obtain ⟨x, rfl⟩ := b1.2 w
  refine ⟨x, b0.1 ?_⟩
  rw [← hw]
  have h1 := congrArg (fun f : M 1 i ⟶ groupHomology (C 0) i => f.hom x) h0
  simpa using h1.symm

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.HomStab.stab_surj_bottom`.
-/
theorem _root_.GlobalTheory.T.quillen_stabilisation_surjective_bottom : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i → Function.Exact (d (p + 1)).hom (d p).hom) → ∀ (M : ℕ → ℕ → ModuleCat.{0} k) (e : ∀ p q, M p q ⟶ groupHomology (C p) q) (s : ∀ p q, M (p + 1) q ⟶ M p q), (∀ p q, p ≤ i + 2 → IsIso (e p q)) → (∀ p q, p + 1 ≤ i + 2 → e (p + 1) q ≫ hMap (d p) q = if Even p then s p q ≫ e p q else 0) → (∀ p q, Even p → 2 ≤ p → p + q = i → Function.Injective (s p q).hom) → (∀ p q, Even p → 2 ≤ p → p + q = i + 1 → Function.Surjective (s p q).hom) → Function.Surjective (s 0 i).hom := by
  first
  | exact @GlobalTheory.HomStab.stab_surj_bottom
end
