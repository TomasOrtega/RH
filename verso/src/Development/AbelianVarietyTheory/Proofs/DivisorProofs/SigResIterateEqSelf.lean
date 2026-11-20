import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicTensorUnramifiedFrobTwistIterateDegreeStatement
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes

namespace GlobalTheory.LKRes

/- English proof (translation)
Proceed by induction on `k generalizing g with`. Consider the case `zero => rfl`. Consider the case `succ k ih`. Rewrite using `[Function.iterate_succ_apply, Function.iterate_succ_apply, ih]`. Both sides reduce to the same expression.
-/
theorem sigRes_iterate_val (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (n r k : ℕ) (g : GL (Fin n) (KQ p K r)) (i j : Fin n) :
    (((⇑(sigRes p K n r))^[k] g : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) i j =
      (⇑(sigKQ p K r))^[k] ((g : Matrix (Fin n) (Fin n) (KQ p K r)) i j) := by
  induction k generalizing g with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    rfl

/- English proof (translation)
Introduce `p _ K n r hr g`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Rewrite using `[sigRes_iterate_val]`. Conclude with `GlobalTheory.T.padicTensorUnramifiedFrobTwist_iterate_degree p K r hr _`.
-/
theorem sigRes_iterate_eq_self : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ), 0 < r → ∀ g : GL (Fin n) (KQ p K r), (⇑(sigRes p K n r))^[r] g = g := by
  intro p _ K n r hr g
  apply Units.ext
  ext i j
  rw [sigRes_iterate_val]
  exact GlobalTheory.T.padicTensorUnramifiedFrobTwist_iterate_degree p K r hr _

end GlobalTheory.LKRes
