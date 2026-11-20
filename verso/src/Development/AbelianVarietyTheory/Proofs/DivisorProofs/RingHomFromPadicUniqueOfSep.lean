import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.

A detailed English derivation is pending.
-/
theorem padicInt_ringHom_ext_of_separated (p : ℕ) [Fact p.Prime] (R : Type) [Ring R]
    (hsep : ∀ x : R, (∀ n : ℕ, ∃ y : R, x = (p : R) ^ n * y) → x = 0) :
    ∀ f g : ℤ_[p] →+* R, f = g := by
  intro f g
  ext c
  have key : f c - g c = 0 := by
    apply hsep
    intro n
    have h := PadicInt.appr_spec n c
    rw [Ideal.mem_span_singleton'] at h
    obtain ⟨c', hc'⟩ := h
    refine ⟨f c' - g c', ?_⟩
    have hc : c = (c.appr n : ℤ_[p]) + c' * (p : ℤ_[p]) ^ n := by rw [hc']; ring
    rw [hc, map_add, map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast,
      map_natCast, map_natCast]
    have hcomm1 : f c' * (p : R) ^ n = (p : R) ^ n * f c' := ((Nat.cast_commute p (f c')).pow_left n).symm
    have hcomm2 : g c' * (p : R) ^ n = (p : R) ^ n * g c' := ((Nat.cast_commute p (g c')).pow_left n).symm
    rw [hcomm1, hcomm2, mul_sub]
    abel
  exact sub_eq_zero.mp key

end GlobalTheory
