import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
open GlobalTheory.LKTrip

namespace GlobalTheory

/- English proof (translation)
Introduce `p _ F _ _`. Use `haveI : Algebra.FormallyUnramified ℚ F := Algebra.FormallyUnramified.of_isSeparable ℚ F`. Use `haveI : Algebra.FormallyUnramified ℚ_[p] (TensorProduct ℚ ℚ_[p] F) := Algebra.FormallyUnramified.base_change ℚ_[p]`. Conclude with `Algebra.FormallyUnramified.isReduced_of_field ℚ_[p] (TensorProduct ℚ ℚ_[p] F)`.
-/
theorem padic_tensor_numberField_isReduced :
    ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F],
      IsReduced (TensorProduct ℚ ℚ_[p] F) := by
  intro p _ F _ _
  haveI : Algebra.FormallyUnramified ℚ F := Algebra.FormallyUnramified.of_isSeparable ℚ F
  haveI : Algebra.FormallyUnramified ℚ_[p] (TensorProduct ℚ ℚ_[p] F) :=
    Algebra.FormallyUnramified.base_change ℚ_[p]
  exact Algebra.FormallyUnramified.isReduced_of_field ℚ_[p] (TensorProduct ℚ ℚ_[p] F)

end GlobalTheory
