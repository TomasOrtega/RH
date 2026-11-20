import Formalism.EllipticTorsion.UnitCancel
import Formalism.EllipticTorsion.EllipticTorsionProofs.IntegralPSBserSubOne

universe u

noncomputable section

namespace Formalism.ELL

open Formalism.G

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules.
-/
theorem unit_cancellation : Formalism.ELL.UnitCancel.{u} := by
  intro p _ K _ _ _ _ σ G b hb h
  obtain ⟨u, rfl⟩ := hb
  have := Formalism.ELL.N_padic_integer_smul p K σ _ h ((u⁻¹ : (ℤ_[p])ˣ) : ℤ_[p])
  convert this using 1
  rw [smul_smul, ← map_mul, ← PadicInt.coe_mul, ← Units.val_mul, inv_mul_cancel]
  simp

end Formalism.ELL
