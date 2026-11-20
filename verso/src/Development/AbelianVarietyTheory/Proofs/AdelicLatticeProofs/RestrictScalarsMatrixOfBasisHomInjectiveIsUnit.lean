import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

/- English proof (translation)
Use function extensionality and compare the values at `p`. Simplify using `only [Matrix.mulVec, dotProduct, res, Matrix.of_apply, Fintype.sum_prod_type, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `h` using `congrFun (Algebra.leftMulMatrix_mulVec_repr b (g p.1 j) (v j)) p.2`. Simplify `h` using `[Matrix.mulVec, dotProduct]`.
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
Introduce `R A β κ _ _ _ _ _ _ _ b`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `⟨i, k⟩ ⟨j, l⟩`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using `[res, Matrix.one_apply]`. Simplify using `[res, Matrix.one_apply, h]`. Introduce `g h`. Use extensionality with `⟨i, k⟩ ⟨j, l⟩`. Simplify using `only [res, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type, map_sum, map_mul, Matrix.sum_apply]`.

Introduce `g h hgh`. Use extensionality with `i j`. Apply `Algebra.leftMulMatrix_injective b` to reduce the goal to its premises. Use extensionality with `k l`. Conclude with `congrFun (congrFun hgh (i, k)) (j, l)`.

Introduce `g hg`. Rewrite using `[← Matrix.mulVec_surjective_iff_isUnit]`. Introduce `w`. Establish `hs : Function.Surjective (res b g).mulVec` using `Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hg)`. Take `⟨u, hu⟩` from `hs (fun p : κ × β => b.repr (w p.1) p.2)`.

Use `⟨fun i => b.equivFun.symm (fun k => u (i, k)), ?_⟩` and prove the remaining obligations. Establish `h` using `res_mulVec_repr b g (fun i => b.equivFun.symm (fun k => u (i, k)))`. Establish `hu' : (fun p : κ × β => b.repr (b.equivFun.symm (fun k => u (p.1, k))) p.2) = u`. Use function extensionality and compare the values at `p`. Rewrite using `[← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]`.

Rewrite `h` using `[hu', hu]`. Use function extensionality and compare the values at `i`. Apply `b.repr.injective` to reduce the goal to its premises. Use extensionality with `k`. Conclude with `(congrFun h (i, k)).symm`.
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
