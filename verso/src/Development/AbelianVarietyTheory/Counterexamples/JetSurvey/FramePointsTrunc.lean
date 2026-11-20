import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpChartOf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpActOf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.LinEig
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqH
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeBeta
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDJet
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExpPiecesCheck

/- English proof (translation)
The claim follows from `LinEig.linEig_holds`.
-/
theorem linEig : LinEigSt := LinEig.linEig_holds

/- English proof (translation)
The claim follows from `expChartOf_of (expActOf_of linEig)`.
-/
theorem expChartOf : ExpChartOfSt := expChartOf_of (expActOf_of linEig)

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c S _ _ _ y x _ e e' he he' a`. Take `⟨β, hg, hr, hc⟩` from `he.coc a`. Take `⟨β', hg', hr', hc'⟩` from `he'.coc a`. Take `rfl` from `betaUniq_of_global GlobalTheory.SemiRigid.globalFns E H Dw l Xo a β β' hg hg' hr hr'`. Conclude with `⟨β, hg, hr, hc, hc'⟩`.
-/
theorem commonCoc : CommonCocSt := by
  intro E _ _ _ H Dw l Xo c S _ _ _ y x _ e e' he he' a
  obtain ⟨β, hg, hr, hc⟩ := he.coc a
  obtain ⟨β', hg', hr', hc'⟩ := he'.coc a
  obtain rfl := betaUniq_of_global GlobalTheory.SemiRigid.globalFns E H Dw l Xo a β β' hg hg' hr hr'
  exact ⟨β, hg, hr, hc, hc'⟩

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]

end

/- English proof (translation)
Assemble the required witnesses or components as `⟨expChartOf, linEig, commonCoc⟩`.
-/
theorem three_hold : ExpChartOfSt ∧ LinEigSt ∧ CommonCocSt := ⟨expChartOf, linEig, commonCoc⟩

end GlobalTheory.ExpPiecesCheck
