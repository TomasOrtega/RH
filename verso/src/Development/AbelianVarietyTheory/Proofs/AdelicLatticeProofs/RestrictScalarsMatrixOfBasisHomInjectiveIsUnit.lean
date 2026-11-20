import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem res_mulVec_repr {R A β κ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β]
    [Fintype κ] (b : Module.Basis β R A) (g : Matrix κ κ A) (v : κ → A) :
    res b g *ᵥ (fun p : κ × β => b.repr (v p.1) p.2) = fun p : κ × β => b.repr ((g *ᵥ v) p.1) p.2 := by
  funext p
  simp only [Matrix.mulVec, dotProduct, res, Matrix.of_apply, Fintype.sum_prod_type, map_sum,
    Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := congrFun (Algebra.leftMulMatrix_mulVec_repr b (g p.1 j) (v j)) p.2
  simpa [Matrix.mulVec, dotProduct] using h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Apply function extensionality and compare values at an arbitrary argument. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. A detailed English derivation is pending.
-/
theorem res_one_mul_injective_isUnit :
    ∀ (R A β κ : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β] [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A), res b (1 : Matrix κ κ A) = 1 ∧ (∀ g h : Matrix κ κ A, res b (g * h) = res b g * res b h) ∧ Function.Injective (fun g : Matrix κ κ A => res b g) ∧ ∀ g : Matrix κ κ A, IsUnit (res b g).det → IsUnit g := by
  intro R A β κ _ _ _ _ _ _ _ b
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext ⟨i, k⟩ ⟨j, l⟩
    by_cases h : i = j
    · subst h
      simp [res, Matrix.one_apply]
    · simp [res, Matrix.one_apply, h]
  · intro g h
    ext ⟨i, k⟩ ⟨j, l⟩
    simp only [res, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type, map_sum, map_mul,
      Matrix.sum_apply]
  · intro g h hgh
    ext i j
    apply Algebra.leftMulMatrix_injective b
    ext k l
    exact congrFun (congrFun hgh (i, k)) (j, l)
  · intro g hg
    rw [← Matrix.mulVec_surjective_iff_isUnit]
    intro w
    have hs : Function.Surjective (res b g).mulVec :=
      Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hg)
    obtain ⟨u, hu⟩ := hs (fun p : κ × β => b.repr (w p.1) p.2)
    refine ⟨fun i => b.equivFun.symm (fun k => u (i, k)), ?_⟩
    have h := res_mulVec_repr b g (fun i => b.equivFun.symm (fun k => u (i, k)))
    have hu' : (fun p : κ × β => b.repr (b.equivFun.symm (fun k => u (p.1, k))) p.2) = u := by
      funext p
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [hu', hu] at h
    funext i
    apply b.repr.injective
    ext k
    exact (congrFun h (i, k)).symm

end GlobalTheory.ClassFin
