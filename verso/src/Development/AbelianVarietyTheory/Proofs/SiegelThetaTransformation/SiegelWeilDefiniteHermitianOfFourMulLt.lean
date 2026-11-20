import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelWeilFormulaDegreeSuccStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

/- English proof (translation)
Introduce `E _ _ _ Ψ hΨ n N hn`. Proceed by induction on `N with`. Consider the case `zero`. Introduce `_ M R φ _ Z _`. Rewrite using `[Base.swd_zero, Base.swDiff_deg_zero]`.

Consider the case `succ N ih`. Introduce `h`. Conclude with `GlobalTheory.T.siegelWeil_formula_degree_succ E Ψ hΨ n N hn h (ih (by omega))`.
-/
theorem siegel_weil_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * N < n → SWAt Ψ n N := by
  intro E _ _ _ Ψ hΨ n N hn
  induction N with
  | zero =>
    intro _ M R φ _ Z _
    rw [Base.swd_zero, Base.swDiff_deg_zero]
  | succ N ih =>
    intro h
    exact GlobalTheory.T.siegelWeil_formula_degree_succ E Ψ hΨ n N hn h (ih (by omega))

end GlobalTheory.SW
