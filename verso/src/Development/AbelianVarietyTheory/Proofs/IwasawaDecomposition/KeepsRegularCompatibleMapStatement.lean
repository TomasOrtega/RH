import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeepsRegularCompatibleMap
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FKeepsRegularCompatibleMap.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.keepsRegular_compatible_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X) (DX : GlobalTheory.EffCartierData X.X), Z.j ≫ π = X.j → DX.KeepsRegular π := by
  first | exact @GlobalTheory.TorRef.keepsRegular_of_comp_j | exact GlobalTheory.TorRef.keepsRegular_of_comp_j | (intros; apply GlobalTheory.TorRef.keepsRegular_of_comp_j <;> assumption)
