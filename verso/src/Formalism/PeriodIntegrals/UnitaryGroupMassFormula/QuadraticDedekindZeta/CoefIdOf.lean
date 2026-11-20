import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticDedekindZeta.Development

open NumberField ArithmeticFunction LSeries
open scoped ArithmeticFunction.zeta

namespace PI.ClassNumImQ.ZetaNonvanishing₂

/- English proof (translation)
Unfold `cnt`. Rewrite using `[Nat.card_eq_one_iff_exists]`. Conclude with `⟨⟨⊤, by simp⟩, fun y => Subtype.ext (Ideal.absNorm_eq_one_iff.mp y.2)⟩`.
-/
theorem cnt_one (K : Type) [Field K] [NumberField K] : cnt K 1 = 1 := by
  unfold cnt
  rw [Nat.card_eq_one_iff_exists]
  exact ⟨⟨⊤, by simp⟩, fun y => Subtype.ext (Ideal.absNorm_eq_one_iff.mp y.2)⟩

end PI.ClassNumImQ.ZetaNonvanishing₂
