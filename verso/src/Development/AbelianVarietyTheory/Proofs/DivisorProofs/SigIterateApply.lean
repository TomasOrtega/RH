import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedExtFrobeniusIterateDegreeEqSelfStatement
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKLoc

namespace GlobalTheory.LKLoc

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rfl`. Consider the case `succ k ih`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]`. Both sides reduce to the same expression.
-/
theorem sig_iterate_apply (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r k : ℕ)
    (g : GL (Fin n) (Kn p K r)) (i j : Fin n) :
    (((⇑(sig p K n r))^[k] g : GL (Fin n) (Kn p K r)) : Matrix (Fin n) (Fin n) (Kn p K r)) i j
      = (⇑(frobR p K r))^[k] ((g : Matrix (Fin n) (Fin n) (Kn p K r)) i j) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    rfl

/- English proof (translation)
Introduce `p _ K hK n r hr g`. Use extensionality with `i j`. Rewrite using `[sig_iterate_apply]`. Rewrite using `[GlobalTheory.T.unramifiedExtFrobenius_iterate_degree_eq_self p K hK r hr]`.
-/
theorem sig_iterate_r : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
    FiniteDimensional ℚ_[p] K → ∀ (n r : ℕ), 0 < r → ∀ g : GL (Fin n) (Kn p K r),
    (⇑(sig p K n r))^[r] g = g := by
  intro p _ K hK n r hr g
  ext i j
  rw [sig_iterate_apply]
  rw [GlobalTheory.T.unramifiedExtFrobenius_iterate_degree_eq_self p K hK r hr]

end GlobalTheory.LKLoc
