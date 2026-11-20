import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem mahler_C_mul_of_norm_eq_one {n k : ℕ} (h : HermNorm n) (c : ℂ) (hc : ‖c‖ = 1)
    (g : MvPolynomial (Fin k × Fin n) ℂ) : mahler h k (C c * g) = mahler h k g := by
  have hfun : (fun v : Fin k × Fin n → ℂ => Real.log ‖eval v (C c * g)‖) =
      fun v => Real.log ‖eval v g‖ := by
    funext v
    rw [eval_mul, eval_C, norm_mul, hc, one_mul]
  unfold mahler
  rw [hfun]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem specFirst_C_mul {n k : ℕ} (c : ℂ) (f : MvPolynomial (Fin (k + 1) × Fin n) ℂ) (u : Fin n → ℂ) :
    specFirst (C c * f) u = C c * specFirst f u := by
  unfold specFirst
  rw [map_mul, bind₁_C_right]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem SpecFirstSwapMahler.proof (h1 : SpecFirstRename.Statement) (h2 : ChowCycleSwap.Statement) :
    SpecFirstSwapMahler.Statement := by
  intro n e h Z f u u' hf
  obtain ⟨c, hc2, hren⟩ := h2 ℂ n (e + 1 + 1) Z f hf (Equiv.swap 0 1)
  have hc : ‖c‖ = 1 := by
    have hsq : ‖c‖ ^ 2 = 1 := by rw [← norm_pow, hc2, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) two_ne_zero).1 hsq
  have key : specFirst (specFirst f u) u' = C c * specFirst (specFirst f u') u := by
    rw [← h1 n e f u' u, hren, specFirst_C_mul, specFirst_C_mul]
  rw [key, mahler_C_mul_of_norm_eq_one h c hc]

end

end GroundTheory.Heights₂.Heights
