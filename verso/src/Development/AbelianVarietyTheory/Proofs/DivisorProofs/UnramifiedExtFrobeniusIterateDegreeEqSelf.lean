import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKLoc

namespace GlobalTheory.LKLoc

/- English proof (translation)
Introduce `p _ K hK r hr x`. Establish `hit : ∀ (i : ℕ) (y : Kn p K r), (((⇑(frobR p K r))^[i] y : Kn p K r) : PadicAlgCl p) = (frobK p K ^ i) (y : PadicAlgCl p)`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => intro y`.

Both sides reduce to the same expression. Consider the case `succ i ih`. Introduce `y`. Rewrite using `[Function.iterate_succ_apply', pow_succ', AlgEquiv.mul_apply, ← ih]`. Both sides reduce to the same expression.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hit]`. Conclude with `(IsFrobOn.pow_fixes_iff p K hK hr ((isFrob_frobK hK).isFrobOn r) r).2 dvd_rfl _ x.2`.
-/
theorem frobR_iterate_self : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
    FiniteDimensional ℚ_[p] K → ∀ (r : ℕ), 0 < r → ∀ x : Kn p K r, (⇑(frobR p K r))^[r] x = x := by
  intro p _ K hK r hr x
  have hit : ∀ (i : ℕ) (y : Kn p K r),
      (((⇑(frobR p K r))^[i] y : Kn p K r) : PadicAlgCl p) = (frobK p K ^ i) (y : PadicAlgCl p) := by
    intro i
    induction i with
    | zero => intro y; rfl
    | succ i ih =>
      intro y
      rw [Function.iterate_succ_apply', pow_succ', AlgEquiv.mul_apply, ← ih]
      rfl
  apply Subtype.ext
  rw [hit]
  exact (IsFrobOn.pow_fixes_iff p K hK hr ((isFrob_frobK hK).isFrobOn r) r).2 dvd_rfl _ x.2

end GlobalTheory.LKLoc
