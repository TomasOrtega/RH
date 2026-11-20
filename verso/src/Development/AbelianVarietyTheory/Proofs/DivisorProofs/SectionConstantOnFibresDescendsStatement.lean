import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionConstantOnFibresDescends
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CoverDesc.section_descends` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSectionConstantOnFibresDescends.lean&line=250#L250)
-/
theorem _root_.GlobalTheory.T.section_constant_on_fibres_descends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ g ∈ sec d.Xo₂ d.c₂ a n, FibConst d g → ∃ f ∈ sec Xo c a n, Pull d f g := by
  first | exact @GlobalTheory.CoverDesc.section_descends | exact GlobalTheory.CoverDesc.section_descends | (intros; apply GlobalTheory.CoverDesc.section_descends <;> assumption)
