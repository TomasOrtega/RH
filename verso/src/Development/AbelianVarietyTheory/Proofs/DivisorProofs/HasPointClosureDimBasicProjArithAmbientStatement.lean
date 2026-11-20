import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPointClosureDimBasicProjArithAmbient
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MixHt.hasDim_basic` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHasPointClosureDimBasicProjArithAmbient.lean&line=119#L119)
-/
theorem _root_.GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p → (∃ m : ℕ, ∀ x : X, ∃ d ≤ m, HasDim x d) ∧ (∀ (x : X) (d d' : ℕ), HasDim x d → HasDim x d' → d = d') ∧ (∀ x : X, HasDim x 0 ↔ IsClosed ({x} : Set X)) ∧ (∀ x : X, IsClosed ({x} : Set X) → Finite (X.residueField x)) ∧ (∀ (Y : Scheme.{0}) (i : Y ⟶ X) [IsClosedImmersion i] (y : Y) (d : ℕ), HasDim (i y) d ↔ HasDim y d) ∧ ∀ (Y : Scheme.{0}) [IsIntegral Y] (d : ℕ), HasDim (genericPoint Y) d ↔ topologicalKrullDim Y = d := by
  first | exact @GlobalTheory.MixHt.hasDim_basic | exact GlobalTheory.MixHt.hasDim_basic | (intros; apply GlobalTheory.MixHt.hasDim_basic <;> assumption)
