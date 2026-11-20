import Formalism.FlagUnipotentLattices.FlagUnipotentLattice
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.OperatorHilbertSchmidtNorm

open MeasureTheory NumberField Matrix
open scoped InnerProductSpace

namespace Formalism.HermitianLatticeCounting.P

open Formalism.HermitianLatticeCounting.S7

/- English proof (translation)
Introduce `E _ _ g`. Establish `h1 : Ideal.absNorm (Ideal.span {(g : 𝓞 E)}) = g ^ Module.finrank ℚ E`. Rewrite using `[Ideal.absNorm_span_singleton]`. Establish `: (g : 𝓞 E) = algebraMap ℤ (𝓞 E) (g : ℤ)` using `by simp`. Rewrite using `[this, Algebra.norm_algebraMap, RingOfIntegers.rank]`.

Simplify using `[Int.natAbs_pow]`. Rewrite using `[← h1]`. Both sides reduce to the same expression.
-/
theorem residueRing_card_eq : Formalism.HermitianLatticeCounting.S7.ResidueRingCard := by
  intro E _ _ g
  have h1 : Ideal.absNorm (Ideal.span {(g : 𝓞 E)}) = g ^ Module.finrank ℚ E := by
    rw [Ideal.absNorm_span_singleton]
    have : (g : 𝓞 E) = algebraMap ℤ (𝓞 E) (g : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank]
    simp [Int.natAbs_pow]
  rw [← h1]
  rfl

end Formalism.HermitianLatticeCounting.P
