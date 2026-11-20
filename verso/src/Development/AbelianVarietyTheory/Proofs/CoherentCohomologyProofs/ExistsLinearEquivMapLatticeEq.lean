import Mathlib

universe u_1 u_2 u_3

namespace GlobalTheory.LatticeLinearEquivBasis

open Module

/- English proof (translation)
Establish `h : Set.range (fun i => (b i : V)) = A.subtype '' Set.range b`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[h, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]`.
-/
theorem span_range_basis_coe {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]
    {ι : Type*} (A : Submodule R V) (b : Basis ι R A) :
    Submodule.span R (Set.range fun i => (b i : V)) = A := by
  have h : Set.range (fun i => (b i : V)) = A.subtype '' Set.range b := by
    rw [← Set.range_comp]; rfl
  rw [h, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]

/- English proof (translation)
Introduce `R _ _ _ K _ _ _ V _ _ _ _ A B _ _`. Set `bA` to `Free.chooseBasis R A`. Set `bB` to `Free.chooseBasis R B`. Set `eA` to `bA.extendOfIsLattice K`. Set `eB` to `bB.extendOfIsLattice K`.

Set `e` to `eA.indexEquiv eB`. Use `⟨eA.equiv eB e, ?_⟩` and prove the remaining obligations. Establish `hA` using `span_range_basis_coe A bA`. Establish `hB` using `span_range_basis_coe B bB`. It suffices to establish `h : Submodule.map ((eA.equiv eB e : V ≃ₗ[K] V).toLinearMap.restrictScalars R) (Submodule.span R (Set.range fun i => (bA i : V))) = Submodule.span R (Set.range fun j => (bB j : V)) by`.

Rewrite `h` using `[hA, hB]`. Conclude with `h`. Rewrite using `[Submodule.map_span]`. Use `congr 1`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨i, rfl⟩, rfl⟩`. Use `⟨e i, ?_⟩` and prove the remaining obligations. Establish `h1 : (bA i : V) = eA i` using `(bA.extendOfIsLattice_apply K i).symm`. Establish `h2 : (bB (e i) : V) = eB (e i)` using `(bB.extendOfIsLattice_apply K (e i)).symm`.

Simplify using `only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]`. Rewrite using `[h1, h2, Basis.equiv_apply]`. Introduce and unpack `⟨j, rfl⟩`. Use `⟨(bA (e.symm j) : V), ⟨e.symm j, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `h1 : (bA (e.symm j) : V) = eA (e.symm j)` using `(bA.extendOfIsLattice_apply K _).symm`.

Establish `h2 : (bB j : V) = eB j` using `(bB.extendOfIsLattice_apply K j).symm`. Simplify using `only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]`. Rewrite using `[h1, h2, Basis.equiv_apply, Equiv.apply_symm_apply]`.
-/
theorem exists_linearEquiv_map_lattice_eq : ∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDomain R] [IsDiscreteValuationRing R] (K : Type u_2) [inst_3 : Field K] [inst_4 : Algebra R K] [IsFractionRing R K] {V : Type u_3} [inst_6 : AddCommGroup V] [inst_7 : Module K V] [inst_8 : Module R V] [inst_9 : IsScalarTower R K V] (A B : Submodule R V) [Submodule.IsLattice K A] [Submodule.IsLattice K B], Exists fun (g : LinearEquiv (RingHom.id K) V V) ↦ Eq (Submodule.map (LinearMap.restrictScalars R (LinearEquiv.toLinearMap g)) A) B := by
  intro R _ _ _ K _ _ _ V _ _ _ _ A B _ _
  let bA := Free.chooseBasis R A
  let bB := Free.chooseBasis R B
  let eA := bA.extendOfIsLattice K
  let eB := bB.extendOfIsLattice K
  let e := eA.indexEquiv eB
  refine ⟨eA.equiv eB e, ?_⟩
  have hA := span_range_basis_coe A bA
  have hB := span_range_basis_coe B bB
  suffices h : Submodule.map ((eA.equiv eB e : V ≃ₗ[K] V).toLinearMap.restrictScalars R)
      (Submodule.span R (Set.range fun i => (bA i : V))) =
      Submodule.span R (Set.range fun j => (bB j : V)) by
    rw [hA, hB] at h; exact h
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    refine ⟨e i, ?_⟩
    have h1 : (bA i : V) = eA i := (bA.extendOfIsLattice_apply K i).symm
    have h2 : (bB (e i) : V) = eB (e i) := (bB.extendOfIsLattice_apply K (e i)).symm
    simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
    rw [h1, h2, Basis.equiv_apply]
  · rintro ⟨j, rfl⟩
    refine ⟨(bA (e.symm j) : V), ⟨e.symm j, rfl⟩, ?_⟩
    have h1 : (bA (e.symm j) : V) = eA (e.symm j) := (bA.extendOfIsLattice_apply K _).symm
    have h2 : (bB j : V) = eB j := (bB.extendOfIsLattice_apply K j).symm
    simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
    rw [h1, h2, Basis.equiv_apply, Equiv.apply_symm_apply]

end GlobalTheory.LatticeLinearEquivBasis
