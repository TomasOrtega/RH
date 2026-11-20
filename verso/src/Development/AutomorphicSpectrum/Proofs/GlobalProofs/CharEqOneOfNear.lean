import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralIndicatorCharOfTrivial
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqOneOfPowNear

open Filter Topology

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem eq_one_of_pow_near (z : ℂ) (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 :=
  _root_.UpperTheory.Reformulated.B.EqOneOfPowNear.eq_one_of_pow_near z h

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem char_eq_one_of_near {G : Type} [AddCommGroup G] (H : AddSubgroup G) (χ : G → ℂ) (h0 : χ 0 = 1)
    (hχ : ∀ x y, χ (x + y) = χ x * χ y) (hs : ∀ x ∈ H, ‖χ x - 1‖ < 1 / 2) {x : G} (hx : x ∈ H) :
    χ x = 1 := by
  have hn : ∀ n : ℕ, χ (n • x) = χ x ^ n := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih => rw [succ_nsmul, hχ, ih, pow_succ]
  refine eq_one_of_pow_near _ fun n => ?_
  rw [← hn]
  exact hs _ (H.nsmul_mem hx n)

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
