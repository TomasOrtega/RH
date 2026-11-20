import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KroneckerCharacterPeriodFormula
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FKroneckerCharacterPeriodFormula.lean&line=104#L104)
-/
theorem _root_.GlobalTheory.T.kronecker_character_period_formula : FlatDegree → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) [NumberField c.F] (N : LogNorms c.F) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → IsFlatGen U τ φ FU i → (∀ s, HasInfNorm U τ φ s (N.inf s)) → (∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), HasFinNorm U τ φ p κ (N.fin p κ)) → N.IsAdelic ∧ N.deg = ((D.p : ℝ) - D.q) / 2 * (GlobalTheory.CM.logOm E χ).re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.TopLL.degree_frames | exact GlobalTheory.CompanionTheory.Ar.Fl.TopLL.degree_frames | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.TopLL.degree_frames <;> assumption)
