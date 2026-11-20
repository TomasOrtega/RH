import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PermRepSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExactHMapOneZeroOfStaircase
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.HomologyRowExactOfStabilisationPattern

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory

/- English proof (translation)
Introduce `k G _ _ i C d hdd hsurj hex M e s hiso hcomm hinj hsur`. Establish `hE : Function.Exact (hMap (d 1) i).hom (hMap (d 0) i).hom`. Use `T.exact_hMap_one_zero_of_staircase k G i C d hdd hsurj hex ?_` and prove the remaining obligations. Introduce `p q hp hpq`. Use `T.homology_row_exact_of_stabilisation_pattern k G C d hdd M e s (i + 3) hiso hcomm p q (by omega) ?_ ?_` and prove the remaining obligations.

Introduce `hev`. Conclude with `hinj p q hev hp hpq`. Introduce `hodd`. Establish `h3 : 3 ≤ p`. Take `⟨m, rfl⟩` from `hodd`.

Use linear arithmetic over natural numbers and integers. Conclude with `hsur (p + 1) q (by simpa using hodd.add_one) (by omega) (by omega)`. Establish `h0` using `hcomm 0 i (by omega)`. Establish `h1` using `hcomm 1 i (by omega)`. Simplify using `only [Even.zero, if_true] at h0`.

Establish `h1' : e 2 i ≫ hMap (d 1) i = 0`. Simplify using `using h1`. Use `haveI := hiso 1 i (by omega)`. Use `haveI := hiso 2 i (by omega)`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `x hx`. Establish `hx1 : (hMap (d 0) i).hom ((e 1 i).hom x) = 0`. Use `congrArg (fun f => f.hom x) h0` as an intermediate fact. Simplify using `only [ModuleCat.hom_comp, LinearMap.comp_apply] at this`. Rewrite using `[this, hx, map_zero]`.

Take `⟨y, hy⟩` from `(hE _).mp hx1`. Establish `hy2 : y = (e 2 i).hom ((inv (e 2 i)).hom y)`. Rewrite using `[← LinearMap.comp_apply, ← ModuleCat.hom_comp, IsIso.inv_hom_id]`. Both sides reduce to the same expression. Establish `hzero : (e 1 i).hom x = 0`.

Rewrite using `[← hy, hy2]`. Use `congrArg (fun f => f.hom ((inv (e 2 i)).hom y)) h1'` as an intermediate fact. Simplify using `only [ModuleCat.hom_comp, LinearMap.comp_apply] at this`. Rewrite using `[this]`. Both sides reduce to the same expression.

Establish `: x = (inv (e 1 i)).hom ((e 1 i).hom x)`. Rewrite using `[← LinearMap.comp_apply, ← ModuleCat.hom_comp, IsIso.hom_inv_id]`. Both sides reduce to the same expression. Rewrite using `[this, hzero, map_zero]`.
-/
theorem injective_stabilisation_bottom_of_rows_exact : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i + 1 → Function.Exact (d (p + 1)).hom (d p).hom) → ∀ (M : ℕ → ℕ → ModuleCat.{0} k) (e : ∀ p q, M p q ⟶ groupHomology (C p) q) (s : ∀ p q, M (p + 1) q ⟶ M p q), (∀ p q, p ≤ i + 3 → IsIso (e p q)) → (∀ p q, p + 1 ≤ i + 3 → e (p + 1) q ≫ hMap (d p) q = if Even p then s p q ≫ e p q else 0) → (∀ p q, Even p → 2 ≤ p → p + q = i + 1 → Function.Injective (s p q).hom) → (∀ p q, Even p → 4 ≤ p → p + q = i + 2 → Function.Surjective (s p q).hom) → Function.Injective (s 0 i).hom := by
  intro k G _ _ i C d hdd hsurj hex M e s hiso hcomm hinj hsur
  have hE : Function.Exact (hMap (d 1) i).hom (hMap (d 0) i).hom := by
    refine T.exact_hMap_one_zero_of_staircase k G i C d hdd hsurj hex ?_
    intro p q hp hpq
    refine T.homology_row_exact_of_stabilisation_pattern k G C d hdd M e s (i + 3) hiso hcomm p q (by omega) ?_ ?_
    · intro hev
      exact hinj p q hev hp hpq
    · intro hodd
      have h3 : 3 ≤ p := by
        obtain ⟨m, rfl⟩ := hodd
        omega
      exact hsur (p + 1) q (by simpa using hodd.add_one) (by omega) (by omega)
  have h0 := hcomm 0 i (by omega)
  have h1 := hcomm 1 i (by omega)
  simp only [Even.zero, if_true] at h0
  have h1' : e 2 i ≫ hMap (d 1) i = 0 := by
    simpa using h1
  haveI := hiso 1 i (by omega)
  haveI := hiso 2 i (by omega)
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hx1 : (hMap (d 0) i).hom ((e 1 i).hom x) = 0 := by
    have := congrArg (fun f => f.hom x) h0
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    rw [this, hx, map_zero]
  obtain ⟨y, hy⟩ := (hE _).mp hx1
  have hy2 : y = (e 2 i).hom ((inv (e 2 i)).hom y) := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, IsIso.inv_hom_id]
    rfl
  have hzero : (e 1 i).hom x = 0 := by
    rw [← hy, hy2]
    have := congrArg (fun f => f.hom ((inv (e 2 i)).hom y)) h1'
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    rw [this]
    rfl
  have : x = (inv (e 1 i)).hom ((e 1 i).hom x) := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, IsIso.hom_inv_id]
    rfl
  rw [this, hzero, map_zero]

end GlobalTheory

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.injective_stabilisation_bottom_of_rows_exact`.
-/
theorem _root_.GlobalTheory.T.quillen_stabilisation_injective_bottom : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i + 1 → Function.Exact (d (p + 1)).hom (d p).hom) → ∀ (M : ℕ → ℕ → ModuleCat.{0} k) (e : ∀ p q, M p q ⟶ groupHomology (C p) q) (s : ∀ p q, M (p + 1) q ⟶ M p q), (∀ p q, p ≤ i + 3 → IsIso (e p q)) → (∀ p q, p + 1 ≤ i + 3 → e (p + 1) q ≫ hMap (d p) q = if Even p then s p q ≫ e p q else 0) → (∀ p q, Even p → 2 ≤ p → p + q = i + 1 → Function.Injective (s p q).hom) → (∀ p q, Even p → 4 ≤ p → p + q = i + 2 → Function.Surjective (s p q).hom) → Function.Injective (s 0 i).hom := by
  first
  | exact @GlobalTheory.injective_stabilisation_bottom_of_rows_exact
end
