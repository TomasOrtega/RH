import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset

noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS

/- English proof (translation)
Proceed by induction on `m generalizing a b with`. Consider the case `zero`. Simplify using `only [epow]`. Use `split_ifs`. Conclude with `Commute.one_right T`.

Conclude with `Commute.zero_right T`. Consider the case `succ m ih`. Simplify using `only [epow]`. Conclude with `Commute.sum_right _ _ _ fun c _ => Commute.mul_right (hT a c) (ih c b)`.
-/
theorem commute_epow_of_units {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (T : Module.End ℂ V)
    (hT : ∀ a b, T * E a b = E a b * T) (m : ℕ) (a b : Fin n) :
    Commute T (epow E m a b) := by
  induction m generalizing a b with
  | zero =>
    simp only [epow]
    split_ifs
    · exact Commute.one_right T
    · exact Commute.zero_right T
  | succ m ih =>
    simp only [epow]
    exact Commute.sum_right _ _ _ fun c _ => Commute.mul_right (hT a c) (ih c b)

/- English proof (translation)
Introduce `n V _ _ E T hT m`. Establish `h : Commute T (gelA E m)` using `Commute.sum_right _ _ _ fun a _ => commute_epow_of_units E T hT m a a`. Conclude with `h.eq.symm`.
-/
theorem gelA_commute_of_units : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (T : Module.End ℂ V),
    (∀ a b, T * E a b = E a b * T) → ∀ m : ℕ, gelA E m * T = T * gelA E m := by
  intro n V _ _ E T hT m
  have h : Commute T (gelA E m) :=
    Commute.sum_right _ _ _ fun a _ => commute_epow_of_units E T hT m a a
  exact h.eq.symm

end GlobalTheory.CompanionTheory.ModelS
