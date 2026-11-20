import Mathlib
import Formalism.RealPlaceAnalysis.StatementE
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.CapelliCentralStatement

open Formalism.REAL ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

namespace GlobalTheory.CompanionTheory.RgExhHecke

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem capEntry_eq_Tm {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (x : ℂ) (a b : Fin n) : capEntry E x a b = Tm E x a b := by
  unfold capEntry Tm
  exact add_comm _ _

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem qdet_eq_capelliC {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (x : ℂ) : qdet E x = capelliC E x := by
  unfold qdet qminor capelliC cminor
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [capEntry_eq_Tm, zsmul_eq_mul]

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem qdetEq : ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (E : Fin n → Fin n → Module.End ℂ M) (x : ℂ), qdet E x = capelliC E x :=
  fun _ _ _ _ E x => qdet_eq_capelliC E x

end GlobalTheory.CompanionTheory.RgExhHecke
