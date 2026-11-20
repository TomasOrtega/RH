import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEval
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.CCRFock

/- English proof (translation)
Simplify using `[GlobalTheory.CCRFock.polMap]`.
-/
theorem polMap_tprod_eq_prod_rename_mulX (W Λ : Type) [Fintype W] [DecidableEq W] (q : W → MvPolynomial Λ ℂ) :
    GlobalTheory.CCRFock.polMap W Λ (PiTensorProduct.tprod ℂ q) =
      ∏ v, MvPolynomial.rename (Prod.mk v) (q v) := by
  simp [GlobalTheory.CCRFock.polMap]

/- English proof (translation)
Introduce `W Λ _ _ w l`. Apply `PiTensorProduct.ext` to reduce the goal to its premises. Apply `MultilinearMap.ext` to reduce the goal to its premises. Introduce `p`. Establish `h : GlobalTheory.RealLift.atPl (V` using `fun _ : W => MvPolynomial Λ ℂ) w (LinearMap.mulLeft ℂ (MvPolynomial.X l)) (PiTensorProduct.tprod ℂ p) = PiTensorProduct.tprod ℂ (Function.update p w (MvPolynomial.X l * p w)) := by`.

Unfold `GlobalTheory.RealLift.atPl`. Rewrite using `[PiTensorProduct.map_tprod]`. Use `congr 1`. Use function extensionality and compare the values at `v`. Distinguish the cases in `hv : v = w`.

Substitute `hv` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne hv]`. Simplify using `only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, h, polMap_tprod_eq_prod_rename_mulX, LinearMap.mulLeft_apply]`. Rewrite using `[Fintype.prod_eq_mul_prod_compl w, Fintype.prod_eq_mul_prod_compl w (fun v => MvPolynomial.rename (Prod.mk v) (p v)), ← mul_assoc]`.

Use `congr 1`. Simplify using the standard rewrite rules. Use `Finset.prod_congr rfl fun v hv => ?_` and prove the remaining obligations. Establish `hv' : v ≠ w` using `by simpa using hv`. Rewrite using `[Function.update_of_ne hv']`.
-/
theorem polMap_comp_atPl_mulLeft_X : ∀ (W Λ : Type) [Fintype W] [DecidableEq W] (w : W) (l : Λ),
    GlobalTheory.CCRFock.polMap W Λ ∘ₗ GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial Λ ℂ) w
                 (LinearMap.mulLeft ℂ (MvPolynomial.X l)) =
      LinearMap.mulLeft ℂ (MvPolynomial.X (w, l)) ∘ₗ GlobalTheory.CCRFock.polMap W Λ := by
  intro W Λ _ _ w l
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro p
  have h : GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial Λ ℂ) w
        (LinearMap.mulLeft ℂ (MvPolynomial.X l)) (PiTensorProduct.tprod ℂ p) =
      PiTensorProduct.tprod ℂ (Function.update p w (MvPolynomial.X l * p w)) := by
    unfold GlobalTheory.RealLift.atPl
    rw [PiTensorProduct.map_tprod]
    congr 1
    funext v
    by_cases hv : v = w
    · subst hv; simp
    · simp [Function.update_of_ne hv]
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, h, polMap_tprod_eq_prod_rename_mulX,
    LinearMap.mulLeft_apply]
  rw [Fintype.prod_eq_mul_prod_compl w, Fintype.prod_eq_mul_prod_compl w
    (fun v => MvPolynomial.rename (Prod.mk v) (p v)), ← mul_assoc]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun v hv => ?_
    have hv' : v ≠ w := by simpa using hv
    rw [Function.update_of_ne hv']

end GlobalTheory.CCRFock
