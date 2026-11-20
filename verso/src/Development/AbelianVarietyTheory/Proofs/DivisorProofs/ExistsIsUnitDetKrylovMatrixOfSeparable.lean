import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrylovApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeftMulMatrixTransfer
open Matrix Polynomial

namespace GlobalTheory.LeviDesc.Krylov

/- English proof (translation)
Take `⟨v, hv⟩` from `GlobalTheory.ClassParam.exists_cyclic_field y hs`. Conclude with `⟨v, isUnit_iff_ne_zero.2 hv⟩`.
-/
theorem exists_isUnit_det_krylov_of_separable {F : Type} [Field F] {r : ℕ}
    (y : Matrix (Fin r) (Fin r) F) (hs : y.charpoly.Separable) :
    ∃ e : Fin r → F, IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y e).det := by
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field y hs
  exact ⟨v, isUnit_iff_ne_zero.2 hv⟩

/- English proof (translation)
The claim follows from `@exists_isUnit_det_krylov_of_separable`.
-/
example : ∀ {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F), y.charpoly.Separable → ∃ e : Fin r → F, IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y e).det :=
  @exists_isUnit_det_krylov_of_separable

end GlobalTheory.LeviDesc.Krylov
