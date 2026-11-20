import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem good_conjugates_mem : ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (s : ℕ),
    Loc.Good K s LL → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Loc.Om l) (x : ↥K.1), τ x ∈ LL.1 := by
  intro l _ K LL s h τ x
  unfold Loc.Good at h
  obtain ⟨-, -, hle, hall⟩ := h

  let σ := τ.liftNormal (Loc.Om l)
  have hσ : σ (algebraMap K.1 (Loc.Om l) x) = τ x := by
    rw [AlgHom.liftNormal_commutes]
    rfl
  have hx := hall ((σ : Loc.Om l →ₐ[ℚ_[l]] Loc.Om l).comp (Loc.Ks K s).val) ⟨x, hle x.2⟩
  rw [← hσ]
  exact hx

end GlobalTheory
