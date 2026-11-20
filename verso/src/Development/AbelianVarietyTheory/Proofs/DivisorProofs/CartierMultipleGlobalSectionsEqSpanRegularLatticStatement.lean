import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierMultipleGlobalSectionsEqSpanRegularLattic
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Desc.sec_eq_spanBy_N` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCartierMultipleGlobalSectionsEqSpanRegularLattic.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.cartierMultipleGlobalSections_eq_span_regularLattice : ∀ (σ : Setup) (k : ℕ), Sec σ.D k = spanBy (GlobalTheory.Desc.cst σ.A.hom) (σ.N k) := by
  first | exact @GlobalTheory.Desc.sec_eq_spanBy_N | exact GlobalTheory.Desc.sec_eq_spanBy_N | (intros; apply GlobalTheory.Desc.sec_eq_spanBy_N <;> assumption)
