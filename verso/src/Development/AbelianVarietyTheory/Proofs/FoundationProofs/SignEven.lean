import Mathlib
import Formalism.JacquetSubsetSums.JacquetSubsetSum
import Formalism.JacquetSubsetSums.SeparationTR

namespace GlobalTheory

/- English proof (translation)
Introduce `p q h`. Apply `Even.neg_one_pow` to reduce the goal to its premises. Rewrite using `[Nat.even_mul]`. Break down `Nat.even_or_odd p with hp | hp` into its components or cases. Conclude with `Or.inl hp`.

Use `right`. Break down `Nat.even_or_odd q with hq | hq` into its components or cases. Conclude with `hq`. Conclude with `absurd (hp.add_odd hq) (Nat.not_even_iff_odd.mpr h)`.
-/
theorem signEven : Formalism.PacketSums.SignEven := by
  intro p q h
  apply Even.neg_one_pow
  rw [Nat.even_mul]
  rcases Nat.even_or_odd p with hp | hp
  · exact Or.inl hp
  · right
    rcases Nat.even_or_odd q with hq | hq
    · exact hq
    · exact absurd (hp.add_odd hq) (Nat.not_even_iff_odd.mpr h)

end GlobalTheory
