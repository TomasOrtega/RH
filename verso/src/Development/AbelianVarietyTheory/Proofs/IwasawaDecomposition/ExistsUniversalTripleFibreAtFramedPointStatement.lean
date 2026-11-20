import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniversalTripleFibreAtFramedPoint
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KeyFourth.exists_tied` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsUniversalTripleFibreAtFramedPoint.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.exists_universalTripleFibre_at_framedPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (S : Type) [CommRing S] [Nontrivial S] [Algebra c.F S] (y : FrPt Xo c S), 1 ≤ Dw.p + Dw.q → ∃ Φ : FibKey Xo S y.x, Tied e y.s y.u Φ := by
  first | exact @GlobalTheory.KeyFourth.exists_tied | exact GlobalTheory.KeyFourth.exists_tied | (intros; apply GlobalTheory.KeyFourth.exists_tied <;> assumption)
