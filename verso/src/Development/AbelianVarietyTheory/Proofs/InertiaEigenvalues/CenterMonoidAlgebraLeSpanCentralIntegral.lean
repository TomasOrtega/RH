import Mathlib

namespace GlobalTheory.GroupAlg.ClassSum

open MonoidAlgebra

variable {G : Type} [Group G] [Fintype G]

noncomputable def classSum [DecidableEq (ConjClasses G)] (C : ConjClasses G) : MonoidAlgebra ℤ G :=
  ∑ h, single h (if ConjClasses.mk h = C then (1 : ℤ) else 0)

/- English proof (translation)
Simplify using `[classSum, coeff_sum, coeff_single, Finsupp.finset_sum_apply, Finsupp.single_apply]`.
-/
theorem coeff_classSum [DecidableEq (ConjClasses G)] (C : ConjClasses G) (y : G) :
    (classSum C).coeff y = if ConjClasses.mk y = C then 1 else 0 := by
  classical
  simp [classSum, coeff_sum, coeff_single, Finsupp.finset_sum_apply, Finsupp.single_apply]

/- English proof (translation)
Proceed by induction on `a using MonoidAlgebra.induction_on with`. Consider the case `of k`. Apply `MonoidAlgebra.ext` to reduce the goal to its premises. Use extensionality with `x`. Simplify using `only [MonoidAlgebra.of_apply, coeff_mul_single_apply, coeff_single_mul_apply, coeff_classSum, mul_one, one_mul]`.

Establish `: ConjClasses.mk (x * k⁻¹) = ConjClasses.mk (k⁻¹ * x)`. Rewrite using `[ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]`. Conclude with `⟨k⁻¹, by group⟩`. Rewrite using `[this]`. Consider the case `add x y hx hy => rw [add_mul, mul_add, hx, hy]`.

Consider the case `smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]`.
-/
theorem classSum_comm [DecidableEq (ConjClasses G)] (C : ConjClasses G) (a : MonoidAlgebra ℤ G) :
    classSum C * a = a * classSum C := by
  induction a using MonoidAlgebra.induction_on with
  | of k =>
    apply MonoidAlgebra.ext
    ext x
    simp only [MonoidAlgebra.of_apply, coeff_mul_single_apply, coeff_single_mul_apply, coeff_classSum,
      mul_one, one_mul]
    have : ConjClasses.mk (x * k⁻¹) = ConjClasses.mk (k⁻¹ * x) := by
      rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
      exact ⟨k⁻¹, by group⟩
    rw [this]
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

/- English proof (translation)
Rewrite `hz` using `[Subalgebra.mem_center_iff]`. Take `⟨g, rfl⟩` from `isConj_iff.mp hab`. Establish `h` using `congrArg (fun w => w.coeff (g * a)) (hz (single g (1 : R)))`. Simplify using `only [coeff_mul_single_apply, coeff_single_mul_apply, one_mul, mul_one, inv_mul_cancel_left] at h`. Conclude with `h`.
-/
theorem coeff_conj_eq {R : Type} [CommRing R] (z : MonoidAlgebra R G)
    (hz : z ∈ Subalgebra.center R (MonoidAlgebra R G)) {a b : G} (hab : IsConj a b) :
    z.coeff a = z.coeff b := by
  rw [Subalgebra.mem_center_iff] at hz
  obtain ⟨g, rfl⟩ := isConj_iff.mp hab
  have h := congrArg (fun w => w.coeff (g * a)) (hz (single g (1 : R)))
  simp only [coeff_mul_single_apply, coeff_single_mul_apply, one_mul, mul_one, inv_mul_cancel_left] at h
  exact h

/- English proof (translation)
Use `haveI := Fintype.ofFinite G`. Use `haveI : Fintype (ConjClasses G) := Fintype.ofFinite _`. Set `rep : ConjClasses G → G` to `fun C => C.exists_rep.choose`. Establish `hrep : ∀ C, ConjClasses.mk (rep C) = C` using `fun C => C.exists_rep.choose_spec`. Establish `hmap : ∀ (C : ConjClasses G) (x : G), (MonoidAlgebra.mapRingHom G (Int.castRingHom R) (classSum C)).coeff x = if ConjClasses.mk x = C then 1 else 0`.

Introduce `C x`. Simplify using `[classSum, map_sum, MonoidAlgebra.mapRangeRingHom_single, coeff_sum, coeff_single, Finsupp.finset_sum_apply, Finsupp.single_apply, apply_ite (Int.cast : ℤ → R)]`. Establish `hz' : z = ∑ C, z.coeff (rep C) • MonoidAlgebra.mapRingHom G (Int.castRingHom R) (classSum C)`. Apply `MonoidAlgebra.ext` to reduce the goal to its premises. Use extensionality with `x`.

Rewrite using `[coeff_sum, Finsupp.finset_sum_apply]`. Simplify using `only [coeff_smul, Finsupp.smul_apply, hmap, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Use `coeff_conj_eq z hz ?_` and prove the remaining obligations. Rewrite using `[← ConjClasses.mk_eq_mk_iff_isConj, hrep]`. Rewrite using `[hz']`.

Use `Submodule.sum_mem _ fun C _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨classSum C, ?_, rfl⟩)` and prove the remaining obligations. Conclude with `classSum_comm C`.
-/
theorem mem_span (R G : Type) [CommRing R] [Group G] [Finite G] (z : MonoidAlgebra R G)
    (hz : z ∈ Subalgebra.center R (MonoidAlgebra R G)) :
    z ∈ Submodule.span R ((MonoidAlgebra.mapRingHom G (Int.castRingHom R)) ''
      {c : MonoidAlgebra ℤ G | ∀ a, c * a = a * c}) := by
  classical
  haveI := Fintype.ofFinite G
  haveI : Fintype (ConjClasses G) := Fintype.ofFinite _
  let rep : ConjClasses G → G := fun C => C.exists_rep.choose
  have hrep : ∀ C, ConjClasses.mk (rep C) = C := fun C => C.exists_rep.choose_spec
  have hmap : ∀ (C : ConjClasses G) (x : G),
      (MonoidAlgebra.mapRingHom G (Int.castRingHom R) (classSum C)).coeff x =
        if ConjClasses.mk x = C then 1 else 0 := by
    intro C x
    simp [classSum, map_sum, MonoidAlgebra.mapRangeRingHom_single, coeff_sum, coeff_single,
      Finsupp.finset_sum_apply, Finsupp.single_apply, apply_ite (Int.cast : ℤ → R)]
  have hz' : z = ∑ C, z.coeff (rep C) • MonoidAlgebra.mapRingHom G (Int.castRingHom R) (classSum C) := by
    apply MonoidAlgebra.ext
    ext x
    rw [coeff_sum, Finsupp.finset_sum_apply]
    simp only [coeff_smul, Finsupp.smul_apply, hmap, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    refine coeff_conj_eq z hz ?_
    rw [← ConjClasses.mk_eq_mk_iff_isConj, hrep]
  rw [hz']
  refine Submodule.sum_mem _ fun C _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨classSum C, ?_, rfl⟩)
  exact classSum_comm C

end GlobalTheory.GroupAlg.ClassSum

/- English proof (translation)
Introduce `R G _ _ _ z hz` and use `GlobalTheory.GroupAlg.ClassSum.mem_span R G z hz`.
-/
theorem GlobalTheory.GroupAlg.center_mem_span_classSums : ∀ (R G : Type) [CommRing R] [Group G] [Finite G] (z : MonoidAlgebra R G), z ∈ Subalgebra.center R (MonoidAlgebra R G) → z ∈ Submodule.span R ((MonoidAlgebra.mapRingHom G (Int.castRingHom R)) '' {c : MonoidAlgebra ℤ G | ∀ a, c * a = a * c}) :=
  fun R G _ _ _ z hz => GlobalTheory.GroupAlg.ClassSum.mem_span R G z hz
