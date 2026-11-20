import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstAndFinite
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

/- English proof (translation)
Unfold `firstAndFinite`. Apply `Algebra.adjoin_mono` to reduce the goal to its premises. Apply `Set.union_subset_union_right` to reduce the goal to its premises. Apply `Set.iUnion_mono` to reduce the goal to its premises. Introduce `i`.

Conclude with `Set.image_mono (by exact_mod_cast h)`.
-/
theorem firstAndFinite_mono (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ)
    {F G : Finset A} (h : F ⊆ G) : firstAndFinite R A k F ≤ firstAndFinite R A k G := by
  unfold firstAndFinite
  apply Algebra.adjoin_mono
  apply Set.union_subset_union_right
  apply Set.iUnion_mono
  intro i
  exact Set.image_mono (by exact_mod_cast h)

/- English proof (translation)
Simplify using `only [PiTensorProduct.singleAlgHom_apply]`. Use `map_prod (PiTensorProduct.tprodMonoidHom R (A := fun _ : Fin (k + 1) => A)) (fun u => MonoidHom.mulSingle (fun _ : Fin (k + 1) => A) u (f u)) Finset.univ` as an intermediate fact. Use `Eq.trans ?_ this` and prove the remaining obligations. Simplify using `only [MonoidHom.mulSingle_apply]`. Rewrite using `[Finset.univ_prod_mulSingle]`.

Both sides reduce to the same expression.
-/
theorem tprod_eq_prod_singleAlgHom (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ)
    (f : Fin (k + 1) → A) :
    PiTensorProduct.tprod R f = ∏ i, PiTensorProduct.singleAlgHom (R := R) (A := fun _ : Fin (k + 1) => A) i (f i) := by
  classical
  simp only [PiTensorProduct.singleAlgHom_apply]
  have := map_prod (PiTensorProduct.tprodMonoidHom R (A := fun _ : Fin (k + 1) => A))
    (fun u => MonoidHom.mulSingle (fun _ : Fin (k + 1) => A) u (f u)) Finset.univ
  refine Eq.trans ?_ this
  simp only [MonoidHom.mulSingle_apply]
  rw [Finset.univ_prod_mulSingle]
  rfl

/- English proof (translation)
Proceed by induction on `x using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r f`. Use `⟨Finset.univ.image f, ?_⟩` and prove the remaining obligations. Use `Subalgebra.smul_mem _ ?_ r` and prove the remaining obligations. Rewrite using `[tprod_eq_prod_singleAlgHom]`.

Use `Subalgebra.prod_mem _ fun i _ => ?_` and prove the remaining obligations. Apply `Algebra.subset_adjoin` to reduce the goal to its premises. Use `Or.inr (Set.mem_iUnion.2 ⟨i, f i, by simp, rfl⟩)` and prove the remaining obligations. Consider the case `add x y hx hy`. Take `⟨F, hF⟩` from `hx`.

Take `⟨G, hG⟩` from `hy`. Conclude with `⟨F ∪ G, Subalgebra.add_mem _ (firstAndFinite_mono R A k Finset.subset_union_left hF) (firstAndFinite_mono R A k Finset.subset_union_right hG)⟩`.
-/
theorem exists_finset_mem_firstAndFinite (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ)
    (x : PiTensorProduct R (fun _ : Fin (k + 1) => A)) : ∃ F : Finset A, x ∈ firstAndFinite R A k F := by
  classical
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    refine ⟨Finset.univ.image f, ?_⟩
    refine Subalgebra.smul_mem _ ?_ r
    rw [tprod_eq_prod_singleAlgHom]
    refine Subalgebra.prod_mem _ fun i _ => ?_
    apply Algebra.subset_adjoin
    refine Or.inr (Set.mem_iUnion.2 ⟨i, f i, by simp, rfl⟩)
  | add x y hx hy =>
    obtain ⟨F, hF⟩ := hx
    obtain ⟨G, hG⟩ := hy
    exact ⟨F ∪ G, Subalgebra.add_mem _ (firstAndFinite_mono R A k Finset.subset_union_left hF)
      (firstAndFinite_mono R A k Finset.subset_union_right hG)⟩

end GlobalTheory.EtC
