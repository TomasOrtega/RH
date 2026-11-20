import Mathlib
import Formalism.RealPlaceAnalysis.StatementE
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.CapelliCentralStatement

open Formalism.REAL ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

namespace GlobalTheory.CompanionTheory.RgExhHecke

/- English proof (translation)
Apply the tactic sequence `unfold capEntry Tm`. Conclude with `add_comm _ _`.
-/
theorem capEntry_eq_Tm {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (x : ℂ) (a b : Fin n) : capEntry E x a b = Tm E x a b := by
  unfold capEntry Tm
  exact add_comm _ _

/- English proof (translation)
Unfold `qdet qminor capelliC cminor`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Simplify using `only [capEntry_eq_Tm, zsmul_eq_mul]`.
-/
theorem qdet_eq_capelliC {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (x : ℂ) : qdet E x = capelliC E x := by
  unfold qdet qminor capelliC cminor
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [capEntry_eq_Tm, zsmul_eq_mul]

/- English proof (translation)
Introduce `_ _ _ _ E x` and use `qdet_eq_capelliC E x`.
-/
theorem qdetEq : ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (E : Fin n → Fin n → Module.End ℂ M) (x : ℂ), qdet E x = capelliC E x :=
  fun _ _ _ _ E x => qdet_eq_capelliC E x

end GlobalTheory.CompanionTheory.RgExhHecke
