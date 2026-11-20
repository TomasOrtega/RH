import Mathlib
import Formalism.PeriodIntegrals.SameFormAllLevels
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TraceFormEquality.ExistsSumEqOne

noncomputable section

namespace PI.Dv.HermitianFormEquivalence

open PI.Dv

section Forms

variable {K : Type} [Field K] {σ : K →+* ℂ} {G : Type} [Group G] [Fintype G] {T : GoodSet K G}
  {EE : Type} [AddCommGroup EE] [Module ℂ EE] {ρE : Representation ℂ G EE}

/- English proof (translation)
Rewrite using `[asAlg_apply, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smulₛₗ, map_smul, M.j_eq, M.io_eq]`.
-/
lemma io_j_asAlg (M : GMap K σ G T EE ρE) (a : MonoidAlgebra K G) (x : M.VK) :
    M.io (M.j (M.rhoK.asAlgebraHom a x)) = ∑ g : G, σ (a.coeff g) • ρE g (M.io (M.j x)) := by
  rw [asAlg_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [LinearMap.map_smulₛₗ, map_smul, M.j_eq, M.io_eq]

/- English proof (translation)
Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩`. Use `⟨M.io (M.j x), ⟨x, by simp⟩, ?_⟩` and prove the remaining obligations. Conclude with `(io_j_asAlg M a x).symm`.

Introduce and unpack `⟨_, ⟨x, rfl⟩, rfl⟩`. Use `⟨x, ?_⟩` and prove the remaining obligations. Simplify using `only [map_one, Module.End.one_apply]`. Conclude with `io_j_asAlg M a x`.
-/
lemma form_eq_image (M : GMap K σ G T EE ρE) (a : MonoidAlgebra K G) :
    M.form a = (fun z => ∑ g : G, σ (a.coeff g) • ρE g z) '' M.form 1 := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨M.io (M.j x), ⟨x, by simp⟩, ?_⟩
    exact (io_j_asAlg M a x).symm
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨x, ?_⟩
    simp only [map_one, Module.End.one_apply]
    exact io_j_asAlg M a x

/- English proof (translation)
Use `set A := AddSubgroup.closure {z | ∃ g, ∃ y ∈ M.form (eps P0), z = ρE g y}`. Establish `key : ∀ (d : MonoidAlgebra K G) (y : M.VK), M.io (M.j (M.rhoK.asAlgebraHom d (M.rhoK.asAlgebraHom (eps P0) y))) ∈ A`. Introduce `d y`. Establish `hs : ∀ g, d.coeff g • M.rhoK g (M.rhoK.asAlgebraHom (eps P0) y) = M.rhoK g (M.rhoK.asAlgebraHom (eps P0) (d.coeff g • y))` using `fun g => by`. Rewrite using `[map_smul, map_smul]`.

Rewrite using `[asAlg_apply, Finset.sum_congr rfl (fun g _ => hs g), map_sum, map_sum]`. Use `AddSubgroup.sum_mem _ fun g _ => AddSubgroup.subset_closure ?_` and prove the remaining obligations. Use `⟨g, M.io (M.j (M.rhoK.asAlgebraHom (eps P0) (d.coeff g • y))), ⟨d.coeff g • y, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[M.j_eq, M.io_eq]`. Apply `Set.Subset.antisymm` to reduce the goal to its premises.

Introduce and unpack `_ ⟨x, rfl⟩`. Take `⟨n, a, b, h⟩` from `eG_mem T P0 hM`. Establish `hx : x = M.rhoK.asAlgebraHom (eG T) x` using `by rw [M.good]; rfl`. Simplify using `only [map_one, Module.End.one_apply]`. Rewrite using `[hx, h, map_sum, LinearMap.sum_apply, map_sum, map_sum]`.

Use `AddSubgroup.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Simplify using `only [map_mul, Module.End.mul_apply]`. Conclude with `key _ _`. Introduce `z hz`. Set `f : M.VK →+ EE` to `(M.io.toAddMonoidHom).comp M.j.toAddMonoidHom`.

Establish `hA : A ≤ f.range`. Rewrite using `[AddSubgroup.closure_le]`. Introduce and unpack `_ ⟨g, _, ⟨y, rfl⟩, rfl⟩`. Use `⟨M.rhoK g (M.rhoK.asAlgebraHom (eps P0) y), ?_⟩` and prove the remaining obligations. Simplify using `[f, M.j_eq, M.io_eq]`.

Take `⟨x, rfl⟩` from `hA hz`. Conclude with `⟨x, by simp [f]⟩`.
-/
lemma form_one_eq (M : GMap K σ G T EE ρE) (P0 : Pair K G) (hM : M1 T P0) :
    M.form 1 = (AddSubgroup.closure {z | ∃ g, ∃ y ∈ M.form (eps P0), z = ρE g y} : Set EE) := by
  set A := AddSubgroup.closure {z | ∃ g, ∃ y ∈ M.form (eps P0), z = ρE g y}
  have key : ∀ (d : MonoidAlgebra K G) (y : M.VK),
      M.io (M.j (M.rhoK.asAlgebraHom d (M.rhoK.asAlgebraHom (eps P0) y))) ∈ A := by
    intro d y
    have hs : ∀ g, d.coeff g • M.rhoK g (M.rhoK.asAlgebraHom (eps P0) y) =
        M.rhoK g (M.rhoK.asAlgebraHom (eps P0) (d.coeff g • y)) := fun g => by
      rw [map_smul, map_smul]
    rw [asAlg_apply, Finset.sum_congr rfl (fun g _ => hs g), map_sum, map_sum]
    refine AddSubgroup.sum_mem _ fun g _ => AddSubgroup.subset_closure ?_
    refine ⟨g, M.io (M.j (M.rhoK.asAlgebraHom (eps P0) (d.coeff g • y))), ⟨d.coeff g • y, rfl⟩, ?_⟩
    rw [M.j_eq, M.io_eq]
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨n, a, b, h⟩ := eG_mem T P0 hM
    have hx : x = M.rhoK.asAlgebraHom (eG T) x := by rw [M.good]; rfl
    simp only [map_one, Module.End.one_apply]
    rw [hx, h, map_sum, LinearMap.sum_apply, map_sum, map_sum]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    simp only [map_mul, Module.End.mul_apply]
    exact key _ _
  · intro z hz
    let f : M.VK →+ EE := (M.io.toAddMonoidHom).comp M.j.toAddMonoidHom
    have hA : A ≤ f.range := by
      rw [AddSubgroup.closure_le]
      rintro _ ⟨g, _, ⟨y, rfl⟩, rfl⟩
      refine ⟨M.rhoK g (M.rhoK.asAlgebraHom (eps P0) y), ?_⟩
      simp [f, M.j_eq, M.io_eq]
    obtain ⟨x, rfl⟩ := hA hz
    exact ⟨x, by simp [f]⟩

end Forms

end PI.Dv.HermitianFormEquivalence
