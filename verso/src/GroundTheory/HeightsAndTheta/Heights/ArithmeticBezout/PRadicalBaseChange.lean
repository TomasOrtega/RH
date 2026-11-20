import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsBaseChange
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ReducedTensorPerfect
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open TensorProduct

noncomputable section

/- English proof (translation)
Introduce `K L _ _ _ σ ι I hI`. Set `: Algebra K L` to `σ.toAlgebra`. Rewrite `hI`, the goal using `[Ideal.isRadical_iff_quotient_reduced]`. Establish `h1 : IsReduced (L ⊗[K] (MvPolynomial ι K ⧸ I))` using `isReduced_tensorProduct_of_perfectField K L _`. Set `e1` to `Algebra.TensorProduct.tensorQuotientEquiv (R := K) L (MvPolynomial ι K) L I`.

Set `e2 : L ⊗[K] MvPolynomial ι K ≃ₐ[L] MvPolynomial ι L` to `MvPolynomial.algebraTensorAlgEquiv K L`. Establish `hmap : I.map (MvPolynomial.map σ) = (I.map (Algebra.TensorProduct.includeRight (R` using `K) (A := L))).map (e2 : L ⊗[K] MvPolynomial ι K →+* MvPolynomial ι L) := by`. Rewrite using `[← Ideal.map_coe (Algebra.TensorProduct.includeRight (R := K) (A := L)), Ideal.map_map]`. Use `congr 1`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises.

Introduce `r`. Simplify using `[e2, MvPolynomial.algebraTensorAlgEquiv_tmul, RingHom.algebraMap_toAlgebra]`. Introduce `i`. Simplify using `[e2, MvPolynomial.algebraTensorAlgEquiv_tmul]`. Set `e3` to `Ideal.quotientEquivAlg (I.map (Algebra.TensorProduct.includeRight (R := K) (A := L))) (I.map (MvPolynomial.map σ)) e2 hmap`.

Conclude with `isReduced_of_injective (e1.toRingEquiv.trans e3.toRingEquiv).symm (RingEquiv.injective _)`.
-/
theorem RadicalBaseChange.proof : RadicalBaseChange.Statement := by
  intro K L _ _ _ σ ι I hI
  let : Algebra K L := σ.toAlgebra
  rw [Ideal.isRadical_iff_quotient_reduced] at hI ⊢
  have h1 : IsReduced (L ⊗[K] (MvPolynomial ι K ⧸ I)) :=
    isReduced_tensorProduct_of_perfectField K L _
  let e1 := Algebra.TensorProduct.tensorQuotientEquiv (R := K) L (MvPolynomial ι K) L I
  let e2 : L ⊗[K] MvPolynomial ι K ≃ₐ[L] MvPolynomial ι L := MvPolynomial.algebraTensorAlgEquiv K L
  have hmap : I.map (MvPolynomial.map σ) =
      (I.map (Algebra.TensorProduct.includeRight (R := K) (A := L))).map
        (e2 : L ⊗[K] MvPolynomial ι K →+* MvPolynomial ι L) := by
    rw [← Ideal.map_coe (Algebra.TensorProduct.includeRight (R := K) (A := L)), Ideal.map_map]
    congr 1
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [e2, MvPolynomial.algebraTensorAlgEquiv_tmul, RingHom.algebraMap_toAlgebra]
    · intro i
      simp [e2, MvPolynomial.algebraTensorAlgEquiv_tmul]
  let e3 := Ideal.quotientEquivAlg (I.map (Algebra.TensorProduct.includeRight (R := K) (A := L)))
    (I.map (MvPolynomial.map σ)) e2 hmap
  exact isReduced_of_injective (e1.toRingEquiv.trans e3.toRingEquiv).symm (RingEquiv.injective _)

end

end GroundTheory.Heights₂.Heights
