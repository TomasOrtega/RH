import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.CycDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GabLim
import ReciprocityTheory.ClassFieldTheory.LocalClassField.NormOpen

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p}

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem finiteDimensional_base_field : FiniteDimensional ℚ_[p] (Q0 p) := inferInstance

/- English proof (translation)
Rewrite using `[eK_mul_fK p (Q0 p) finiteDimensional_base_field]`. Conclude with `IntermediateField.finrank_bot`.
-/
theorem ramification_mul_inertia_base_field : eK p (Q0 p) * fK p (Q0 p) = 1 := by
  rw [eK_mul_fK p (Q0 p) finiteDimensional_base_field]
  exact IntermediateField.finrank_bot

/- English proof (translation)
Rewrite using `[qK_eq_pow_fK p (Q0 p) finiteDimensional_base_field, Nat.eq_one_of_mul_eq_one_left ramification_mul_inertia_base_field, pow_one]`.
-/
theorem residue_cardinality_base_field : qK p (Q0 p) = p := by
  rw [qK_eq_pow_fK p (Q0 p) finiteDimensional_base_field, Nat.eq_one_of_mul_eq_one_left ramification_mul_inertia_base_field, pow_one]

/- English proof (translation)
Establish `h : ‖z‖ ^ n = 1` using `by rw [← norm_pow, hz, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg z) hn).1 h`.
-/
theorem norm_eq_one_of_pow {n : ℕ} (hn : n ≠ 0) {z : PadicAlgCl p} (hz : z ^ n = 1) : ‖z‖ = 1 := by
  have h : ‖z‖ ^ n = 1 := by rw [← norm_pow, hz, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) hn).1 h

end ReciprocityTheory.DiscreteGroups.LocalClassField
