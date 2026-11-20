import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

By extensionality, compare the relevant components. Both sides reduce to the same expression. By extensionality, compare the relevant components. Both sides reduce to the same expression.
-/
theorem splits_of_conjugates_mem :
    ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l),
      (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Loc.Om l) (x : ↥K.1), τ x ∈ LL.1) →
      ∀ _ft : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1),
        Formalism.WeaklyAdmissibleFiltrations.Splits (Qp := ℚ_[l]) (K := ↥K.1) ↥LL.1 := by
  intro l _ K LL h ft
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  refine ⟨LL.2, ?_⟩
  rw [← AlgHom.card ℚ_[l] ↥K.1 (Loc.Om l), ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun σ => LL.1.val.comp σ
      invFun := fun τ => τ.codRestrict LL.1.toSubalgebra (h τ)
      left_inv := fun σ => ?_
      right_inv := fun τ => ?_ }
  · ext x; rfl
  · ext x; rfl

end GlobalTheory
