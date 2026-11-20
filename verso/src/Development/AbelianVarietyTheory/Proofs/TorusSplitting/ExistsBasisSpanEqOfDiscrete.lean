import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Transference

open Module Submodule

namespace GlobalTheory

/- English proof (translation)
Establish `: IsZLattice ℝ M` using `⟨hM⟩`. Use `ZLattice.module_free ℝ M` as an intermediate fact. Use `ZLattice.module_finite ℝ M` as an intermediate fact. Set `b1` to `(Module.Free.chooseBasis ℤ M).ofZLatticeBasis ℝ M`. Establish `hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ M) = N`.

Rewrite using `[← finrank_eq_card_basis b1]`. Simplify using the standard rewrite rules. Use `⟨b1.reindex (Fintype.equivFinOfCardEq hcard), ?_⟩` and prove the remaining obligations. Rewrite using `[Basis.range_reindex]`. Conclude with `Basis.ofZLatticeBasis_span ℝ M _`.
-/
theorem exists_basis_span_eq_of_discrete {N : ℕ} (M : Submodule ℤ (EuclideanSpace ℝ (Fin N)))
    [DiscreteTopology M] (hM : span ℝ (M : Set (EuclideanSpace ℝ (Fin N))) = ⊤) :
    ∃ b : Basis (Fin N) ℝ (EuclideanSpace ℝ (Fin N)), span ℤ (Set.range b) = M := by
  have : IsZLattice ℝ M := ⟨hM⟩
  have := ZLattice.module_free ℝ M
  have := ZLattice.module_finite ℝ M
  let b1 := (Module.Free.chooseBasis ℤ M).ofZLatticeBasis ℝ M
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ M) = N := by
    rw [← finrank_eq_card_basis b1]
    simp
  refine ⟨b1.reindex (Fintype.equivFinOfCardEq hcard), ?_⟩
  rw [Basis.range_reindex]
  exact Basis.ofZLatticeBasis_span ℝ M _

/- English proof (translation)
Set `w : Fin N → EuclideanSpace ℝ (Fin N)` to `fun j => (InnerProductSpace.toDual ℝ _).symm (LinearMap.toContinuousLinearMap (b.coord j))`. Establish `hw : ∀ j y, inner ℝ (w j) y = b.repr y j` using `fun j y => by`. Simplify using `[w, InnerProductSpace.toDual_symm_apply]`. Establish `hli : LinearIndependent ℝ w`. Rewrite using `[Fintype.linearIndependent_iff]`.

Introduce `g hg i`. Use `congrArg (fun x => inner ℝ x (b i)) hg` as an intermediate fact. Simplify `this` using `[sum_inner, real_inner_smul_left, hw, Finsupp.single_apply]`. Use `⟨basisOfLinearIndependentOfCardEqFinrank' _ hli (by simp), fun j y => ?_⟩` and prove the remaining obligations. Rewrite using `[coe_basisOfLinearIndependentOfCardEqFinrank', hw]`.
-/
theorem exists_inner_dual_basis {N : ℕ} (b : Basis (Fin N) ℝ (EuclideanSpace ℝ (Fin N))) :
    ∃ d : Basis (Fin N) ℝ (EuclideanSpace ℝ (Fin N)), ∀ j y, inner ℝ (d j) y = b.repr y j := by
  let w : Fin N → EuclideanSpace ℝ (Fin N) := fun j =>
    (InnerProductSpace.toDual ℝ _).symm (LinearMap.toContinuousLinearMap (b.coord j))
  have hw : ∀ j y, inner ℝ (w j) y = b.repr y j := fun j y => by
    simp [w, InnerProductSpace.toDual_symm_apply]
  have hli : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := congrArg (fun x => inner ℝ x (b i)) hg
    simpa [sum_inner, real_inner_smul_left, hw, Finsupp.single_apply] using this
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' _ hli (by simp), fun j y => ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank', hw]

/- English proof (translation)
Introduce `N M _ hM lam hlam hmin`. Take `⟨b, rfl⟩` from `exists_basis_span_eq_of_discrete M hM`. Take `⟨d, hd⟩` from `exists_inner_dual_basis b`. Take `⟨y, hli, hint, hy⟩` from `ReciprocityTheory.ChartRestriction.G.T0.transference_dual d lam hlam (by`. Introduce `x hx hx0`.

Use `hmin x (fun y hy => ?_) hx0` and prove the remaining obligations. Take `⟨c, rfl⟩` from `(mem_span_range_iff_exists_fun ℤ).1 hx`. Take `⟨e, rfl⟩` from `(mem_span_range_iff_exists_fun ℤ).1 hy`. Use `⟨∑ j, c j * e j, ?_⟩` and prove the remaining obligations. Simplify using `[sum_inner, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hd, Finsupp.single_apply])`.

Use `⟨y, fun i => ?_, hli, hy⟩` and prove the remaining obligations. Rewrite using `[b.mem_span_iff_repr_mem ℤ]`. Introduce `j`. Take `⟨m, hm⟩` from `hint i j`. Conclude with `⟨m, by rw [← hd, real_inner_comm, hm]; simp⟩`.
-/
theorem transference_discrete_lattice :
    ∀ (N : ℕ) (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))), DiscreteTopology M →
      Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin N))) = ⊤ → ∀ lam : ℝ, 0 < lam →
      (∀ z : EuclideanSpace ℝ (Fin N), (∀ y ∈ M, ∃ k : ℤ, inner ℝ z y = (k : ℝ)) → z ≠ 0 →
        lam ≤ ‖z‖) →
      ∃ v : Fin N → EuclideanSpace ℝ (Fin N), (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧
        ∀ j, ‖v j‖ ≤ (N : ℝ) ^ 2 / lam := by
  intro N M _ hM lam hlam hmin
  obtain ⟨b, rfl⟩ := exists_basis_span_eq_of_discrete M hM
  obtain ⟨d, hd⟩ := exists_inner_dual_basis b
  obtain ⟨y, hli, hint, hy⟩ := ReciprocityTheory.ChartRestriction.G.T0.transference_dual d lam hlam (by
    intro x hx hx0
    refine hmin x (fun y hy => ?_) hx0
    obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hx
    obtain ⟨e, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hy
    refine ⟨∑ j, c j * e j, ?_⟩
    simp [sum_inner, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hd,
      Finsupp.single_apply])
  refine ⟨y, fun i => ?_, hli, hy⟩
  rw [b.mem_span_iff_repr_mem ℤ]
  intro j
  obtain ⟨m, hm⟩ := hint i j
  exact ⟨m, by rw [← hd, real_inner_comm, hm]; simp⟩

end GlobalTheory
