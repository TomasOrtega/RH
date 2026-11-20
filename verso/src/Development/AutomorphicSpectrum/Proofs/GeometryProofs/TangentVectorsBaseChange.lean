import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.WeilBound.CoreStatements.SesquilinearFractions.GFrameBC
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `PositivityTheory.Xgf.tangent_vectors_base_change` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FWeilBound%2FCoreStatements%2FSesquilinearFractions%2FGFrameBC.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.CompanionTheory.Relay.tangent_vectors_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (F F' : Type) [Field F] [Field F'] (f : F →+* F') (x : Sp F ⟶ S) (x' : Sp F' ⟶ S) (τ : 𝓞 E →+* F) (n : ℕ) (v : Fin n → (epsAt x ⟶ t.G)), x' = spMap f ≫ x → (∃ v' : Fin n → (epsAt x' ⟶ t.G), ∀ k, (v' k).left = spMap (dualMap f) ≫ (v k).left) ∧ ∀ v' : Fin n → (epsAt x' ⟶ t.G), (∀ k, (v' k).left = spMap (dualMap f) ≫ (v k).left) → (IsEigFrame t.act x τ v ↔ IsEigFrame t.act x' (f.comp τ) v') := by
  first | exact @PositivityTheory.Xgf.tangent_vectors_base_change | exact PositivityTheory.Xgf.tangent_vectors_base_change
