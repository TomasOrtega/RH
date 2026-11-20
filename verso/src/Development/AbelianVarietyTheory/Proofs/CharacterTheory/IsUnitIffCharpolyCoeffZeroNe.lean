import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

open Polynomial in

/- English proof (translation)
Use `haveI : Finite V := Module.finite_of_finite F`. Use `haveI : Finite (Module.End F V) := Finite.of_injective (fun g : Module.End F V => (g : V → V)) DFunLike.coe_injective`. Use `set S := {P : F[X] | P.Monic ∧ P.natDegree = Module.finrank F V ∧ P.coeff 0 ≠ 0} with hS`. Use `set I := S ∩ Set.range (fun g : Module.End F V => LinearMap.charpoly g) with hI`. Establish `hunit : ∀ g : Module.End F V, IsUnit g ↔ LinearMap.charpoly g ∈ S`.

Introduce `g`. Simplify using `only [hS, Set.mem_setOf_eq, LinearMap.charpoly_monic, LinearMap.charpoly_natDegree, true_and]`. Rewrite using `[LinearMap.isUnit_iff_isUnit_det, LinearMap.det_eq_sign_charpoly_coeff, isUnit_iff_ne_zero]`. Simplify using the standard rewrite rules. Establish `hset : {g : Module.End F V | IsUnit g} = ⋃ P ∈ I, {g : Module.End F V | LinearMap.charpoly g = P}`.

Use extensionality with `g`. Simplify using `only [Set.mem_setOf_eq, Set.mem_iUnion, hI, Set.mem_inter_iff, Set.mem_range, exists_prop]`. Rewrite using `[hunit]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `⟨_, ⟨h, g, rfl⟩, rfl⟩`. Introduce and unpack `⟨P, ⟨hP, _⟩, rfl⟩`. Conclude with `hP`. Establish `hsupp : S ∩ Function.support (fun P => _root_.GlobalTheory.CuspGL.mass φ P * star (s P)) = I ∩ Function.support (fun P => _root_.GlobalTheory.CuspGL.mass φ P * star (s P))`. Use extensionality with `P`.

Simplify using `only [hI, Set.mem_inter_iff, Function.mem_support]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hPS, hne⟩`. Use `⟨⟨hPS, ?_⟩, hne⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hr`.

Apply `hne` to reduce the goal to its premises. Establish `hempty : {g : Module.End F V | LinearMap.charpoly g = P} = ∅`. Use extensionality with `g`. Simplify using `only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]`. Conclude with `fun h => hr ⟨g, h⟩`.

Unfold `_root_.GlobalTheory.CuspGL.mass`. Simplify using `[hempty]`. Introduce and unpack `⟨⟨hPS, _⟩, hne⟩`. Conclude with `⟨hPS, hne⟩`. Rewrite using `[finsum_mem_inter_support_eq _ S I hsupp]`.

Unfold `_root_.GlobalTheory.CuspGL.ipGL _root_.GlobalTheory.CuspGL.mass`. Rewrite using `[hset, finsum_mem_biUnion ?_ ((Set.finite_range _).subset Set.inter_subset_right) (fun _ _ => Set.toFinite _)]`. Use `finsum_mem_congr rfl fun P _ => ?_` and prove the remaining obligations. Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _), finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _), Finset.sum_mul]`. Use `Finset.sum_congr rfl fun g hg => ?_` and prove the remaining obligations.

Rewrite `hg` using `[Set.Finite.mem_toFinset]`. Use `show φ g * star (s (LinearMap.charpoly g)) = _`. Rewrite using `[show LinearMap.charpoly g = P from hg]`. Introduce `P _ Q _ hPQ`. Conclude with `Set.disjoint_left.2 fun g hP hQ => hPQ (hP.symm.trans hQ)`.
-/
theorem _root_.GlobalTheory.CuspGL.ipGL_charpoly_eq_finsum_mass (F : Type) [Field F] [Finite F]
    (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (φ : Module.End F V → ℂ) (s : F[X] → ℂ) :
    _root_.GlobalTheory.CuspGL.ipGL φ (fun g => s (LinearMap.charpoly g)) =
      ∑ᶠ P ∈ {P : F[X] | P.Monic ∧ P.natDegree = Module.finrank F V ∧ P.coeff 0 ≠ 0},
        _root_.GlobalTheory.CuspGL.mass φ P * star (s P) := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Module.End F V) :=
    Finite.of_injective (fun g : Module.End F V => (g : V → V)) DFunLike.coe_injective
  set S := {P : F[X] | P.Monic ∧ P.natDegree = Module.finrank F V ∧ P.coeff 0 ≠ 0} with hS
  set I := S ∩ Set.range (fun g : Module.End F V => LinearMap.charpoly g) with hI
  have hunit : ∀ g : Module.End F V, IsUnit g ↔ LinearMap.charpoly g ∈ S := by
    intro g
    simp only [hS, Set.mem_setOf_eq, LinearMap.charpoly_monic, LinearMap.charpoly_natDegree,
      true_and]
    rw [LinearMap.isUnit_iff_isUnit_det, LinearMap.det_eq_sign_charpoly_coeff, isUnit_iff_ne_zero]
    simp
  have hset : {g : Module.End F V | IsUnit g} =
      ⋃ P ∈ I, {g : Module.End F V | LinearMap.charpoly g = P} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, hI, Set.mem_inter_iff, Set.mem_range,
      exists_prop]
    rw [hunit]
    constructor
    · intro h
      exact ⟨_, ⟨h, g, rfl⟩, rfl⟩
    · rintro ⟨P, ⟨hP, _⟩, rfl⟩
      exact hP
  have hsupp : S ∩ Function.support (fun P => _root_.GlobalTheory.CuspGL.mass φ P * star (s P)) =
      I ∩ Function.support (fun P => _root_.GlobalTheory.CuspGL.mass φ P * star (s P)) := by
    ext P
    simp only [hI, Set.mem_inter_iff, Function.mem_support]
    constructor
    · rintro ⟨hPS, hne⟩
      refine ⟨⟨hPS, ?_⟩, hne⟩
      by_contra hr
      apply hne
      have hempty : {g : Module.End F V | LinearMap.charpoly g = P} = ∅ := by
        ext g
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hr ⟨g, h⟩
      unfold _root_.GlobalTheory.CuspGL.mass
      simp [hempty]
    · rintro ⟨⟨hPS, _⟩, hne⟩
      exact ⟨hPS, hne⟩
  rw [finsum_mem_inter_support_eq _ S I hsupp]
  unfold _root_.GlobalTheory.CuspGL.ipGL _root_.GlobalTheory.CuspGL.mass
  rw [hset, finsum_mem_biUnion ?_ ((Set.finite_range _).subset Set.inter_subset_right)
    (fun _ _ => Set.toFinite _)]
  · refine finsum_mem_congr rfl fun P _ => ?_
    rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _),
      finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _), Finset.sum_mul]
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [Set.Finite.mem_toFinset] at hg
    show φ g * star (s (LinearMap.charpoly g)) = _
    rw [show LinearMap.charpoly g = P from hg]
  · intro P _ Q _ hPQ
    exact Set.disjoint_left.2 fun g hP hQ => hPQ (hP.symm.trans hQ)

end GlobalTheory.CuspGL
