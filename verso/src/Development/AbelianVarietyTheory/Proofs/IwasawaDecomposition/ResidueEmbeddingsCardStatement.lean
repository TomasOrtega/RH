import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueEmbeddingsCard
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FResidueEmbeddingsCard.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.residue_embeddings_card : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (x : Y.X), IsClosed ({x} : Set Y.X) → Nat.card (M.X.residueField (M.j x) →+* ℂ) = Module.finrank ℚ F * Nat.card {y : AlgPt Y // below y.1 = x} := by
  first | exact @GlobalTheory.TrueGeo.ResidueCard.main | exact GlobalTheory.TrueGeo.ResidueCard.main | (intros; apply GlobalTheory.TrueGeo.ResidueCard.main <;> assumption)
