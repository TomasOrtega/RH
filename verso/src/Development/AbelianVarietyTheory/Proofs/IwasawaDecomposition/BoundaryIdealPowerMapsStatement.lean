import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryIdealPowerMaps
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FBoundaryIdealPowerMaps.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.boundary_ideal_power_maps : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : GlobalTheory.EffCartierData Y.X) (k : ℕ) (ρ : gen Y ⟶ gen X),
    Y.jQ ≫ ρ = X.jQ → GlobalTheory.IsAmpleLB (polOf Y k BY) → (∀ x ∈ BY.idealSheaf.support, x ∉ abLocus Y.t.G) →
    ∃ n : ℕ, 0 < n ∧ (((BY.idealSheaf ^ n).comap (genι Y)).map (ρ ≫ genι X)).comap (ρ ≫ genι X) =
      (BY.idealSheaf ^ n).comap (genι Y) := by
  first | exact @GlobalTheory.TorRef.relGen_multiple | exact GlobalTheory.TorRef.relGen_multiple | (intros; apply GlobalTheory.TorRef.relGen_multiple <;> assumption)
