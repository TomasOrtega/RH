import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open GlobalTheory.DualPairCheck
open scoped TensorProduct

namespace GlobalTheory.OrientedAdjoint

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Introduce `h`. Take `⟨v, hv, h0⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h`. Apply `hv` to reduce the goal to its premises. Establish `: V.frame.equivFun.symm v = 0`. Apply `V.nondeg.2` to reduce the goal to its premises.

Introduce `x`. Establish `hx : x = ∑ i, V.frame.repr x i • V.frame i` using `(V.frame.sum_repr x).symm`. Rewrite using `[hx, map_sum, LinearMap.sum_apply]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Establish `h1 : ∑ j, V.gram i j * v j = 0` using `congr_fun h0 i`.

Establish `h2 : V.hT (V.frame i) (V.frame.equivFun.symm v) = ∑ j, V.gram i j * v j`. Rewrite using `[Module.Basis.equivFun_symm_apply, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul, mul_comm]`. Both sides reduce to the same expression.

Rewrite using `[LinearMap.map_smulₛₗ, LinearMap.smul_apply, h2, h1, smul_zero]`. Conclude with `V.frame.equivFun.symm.injective (this.trans (map_zero _).symm)`.
-/
theorem gram_det_ne (V : HSp D) : V.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have : V.frame.equivFun.symm v = 0 := by
    apply V.nondeg.2
    intro x
    have hx : x = ∑ i, V.frame.repr x i • V.frame i := (V.frame.sum_repr x).symm
    rw [hx, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h1 : ∑ j, V.gram i j * v j = 0 := congr_fun h0 i
    have h2 : V.hT (V.frame i) (V.frame.equivFun.symm v) = ∑ j, V.gram i j * v j := by
      rw [Module.Basis.equivFun_symm_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]; rfl
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, h2, h1, smul_zero]
  exact V.frame.equivFun.symm.injective (this.trans (map_zero _).symm)

/- English proof (translation)
Rewrite using `[← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (gram_det_ne V))]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem gram_mul_inv (V : HSp D) : V.gram.map (incA D) * V.gram⁻¹.map (incA D) = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (gram_det_ne V))]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
Use extensionality with `i j`. Conclude with `(cA_incA _).trans (congrArg (incA D) (gram_star V j i))`.
-/
theorem gram_conj (V : HSp D) : ((V.gram.map (incA D)).map (cA D))ᵀ = V.gram.map (incA D) := by
  ext i j
  exact (cA_incA _).trans (congrArg (incA D) (gram_star V j i))

section Generic
variable {A : Type} [CommRing A] {m n : ℕ}

/- English proof (translation)
Establish `h' : Pi * P = 1` using `mul_eq_one_comm.1 h`. Establish `h2 : P * (Pi.map σ)ᵀ = 1`. Rewrite using `[← hP, ← Matrix.transpose_mul, ← Matrix.map_mul, h', Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem inv_conj (σ : A →+* A) (P Pi : Matrix (Fin n) (Fin n) A) (h : P * Pi = 1) (hP : (P.map σ)ᵀ = P) :
    (Pi.map σ)ᵀ = Pi := by
  have h' : Pi * P = 1 := mul_eq_one_comm.1 h
  have h2 : P * (Pi.map σ)ᵀ = 1 := by
    rw [← hP, ← Matrix.transpose_mul, ← Matrix.map_mul, h',
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  calc _ = (Pi * P) * (Pi.map σ)ᵀ := by rw [h', Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, h2, Matrix.mul_one]

end Generic

end GlobalTheory.OrientedAdjoint

end
