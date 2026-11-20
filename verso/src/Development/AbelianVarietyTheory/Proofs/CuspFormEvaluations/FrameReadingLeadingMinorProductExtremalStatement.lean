import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameReadingLeadingMinorProductExtremal
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LetAct
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.FrameRead
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FrameReadHw.cof_pG` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCuspFormEvaluations%2FFrameReadingLeadingMinorProductExtremal.lean&line=255#L255)
-/
theorem _root_.GlobalTheory.T.frameReading_leadingMinorProduct_extremal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)), IsEnum H pl → Dw.p + Dw.q ≤ n → ∀ (l : Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (s : Ix → ℤ) (lam : Ix → DomWeight n), (∀ τ, Antitone fun i => a (τ, i)) → WtIs Dw pl a s lam → ∃ ε : ℤˣ, cof Dw pl c.F n (pG (Dw := Dw) c a n) = ((ε : ℤ) : c.F) • (detFac Dw pl c.F a s lam * ten fun t => extremal c.F n (lam t)) := by
  first | exact @GlobalTheory.FrameReadHw.cof_pG | exact GlobalTheory.FrameReadHw.cof_pG | (intros; apply GlobalTheory.FrameReadHw.cof_pG <;> assumption)
