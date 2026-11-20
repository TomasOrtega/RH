import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.Mem.PureSep

/- English proof (translation)
Proceed by induction. Treat this case separately. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression.
-/
theorem exists_finite_subspaces {ι : Type} {E : ι → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
    (x : ⨂[ℂ] i, E i) : ∃ W : ∀ i, Submodule ℂ (E i), (∀ i, FiniteDimensional ℂ (W i)) ∧
      ∃ y : ⨂[ℂ] i, W i, PiTensorProduct.map (fun i => (W i).subtype) y = x := by
  classical
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    refine ⟨fun i => ℂ ∙ m i, fun i => inferInstance,
      r • PiTensorProduct.tprod ℂ (fun i => (⟨m i, Submodule.mem_span_singleton_self _⟩ : ℂ ∙ m i)), ?_⟩
    rw [map_smul, PiTensorProduct.map_tprod]
    rfl
  | add a b ha hb =>
    obtain ⟨W₁, h₁, y₁, rfl⟩ := ha
    obtain ⟨W₂, h₂, y₂, rfl⟩ := hb
    refine ⟨fun i => W₁ i ⊔ W₂ i, fun i => by have := h₁ i; have := h₂ i; infer_instance,
      PiTensorProduct.map (fun i => Submodule.inclusion (le_sup_left : W₁ i ≤ W₁ i ⊔ W₂ i)) y₁ +
        PiTensorProduct.map (fun i => Submodule.inclusion (le_sup_right : W₂ i ≤ W₁ i ⊔ W₂ i)) y₂, ?_⟩
    rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp,
      ← PiTensorProduct.map_comp]
    rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the hypotheses and unpack their components. Introduce a local definition for the expression.

Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Proceed by induction. Treat this case separately. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Treat this case separately. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. A detailed English derivation is pending.
-/
theorem exists_ellT_ne_zero : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (x : SmT M), x ≠ 0 → ∃ w : M.Vec, ellT M (fun τ => (w τ : M.H τ)) (inclT M x) ≠ 0 := by
  classical
  intro D V S M x hx
  obtain ⟨W, hW, y, rfl⟩ := exists_finite_subspaces x
  have hy : y ≠ 0 := by
    rintro rfl
    exact hx (map_zero _)
  let ob : ∀ τ, OrthonormalBasis (Fin (Module.finrank ℂ (W τ))) ℂ (W τ) := fun τ =>
    haveI := hW τ; stdOrthonormalBasis ℂ (W τ)
  let B := Basis.piTensorProduct (fun τ => (ob τ).toBasis)
  obtain ⟨k, hk⟩ : ∃ k, B.repr y k ≠ 0 := by
    by_contra h
    push_neg at h
    apply hy
    apply B.repr.injective
    ext k
    simp [h k]
  refine ⟨fun τ => ((ob τ (k τ) : W τ) : M.sm τ), ?_⟩
  have key : ∀ y' : ⨂[ℂ] τ, W τ,
      ellT M (fun τ => (((ob τ (k τ) : W τ) : M.sm τ) : M.H τ))
        (inclT M (PiTensorProduct.map (fun τ => (W τ).subtype) y')) = B.repr y' k := by
    intro y'
    induction y' using PiTensorProduct.induction_on with
    | smul_tprod r z =>
      unfold ellT inclT
      simp only [map_smul, PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod, Finsupp.smul_apply, B,
        Basis.piTensorProduct_repr_tprod_apply, MultilinearMap.compLinearMap_apply,
        MultilinearMap.mkPiAlgebra_apply, innerₛₗ_apply_apply, smul_eq_mul]
      congr 1
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
      rfl
    | add a b ha hb =>
      simp only [map_add, Finsupp.add_apply] at ha hb ⊢
      rw [ha, hb]
  exact fun h => hk ((key y).symm.trans h)

end GlobalTheory.Mem.PureSep
