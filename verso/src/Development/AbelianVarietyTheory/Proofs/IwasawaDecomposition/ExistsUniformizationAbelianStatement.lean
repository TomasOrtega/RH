import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformizationAbelian
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasConesIff
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsUniformizationAbelian.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.exists_uniformization_abelian : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)), IsCN R → PolAt t (jK R) → ThetaNZ t.G t.PP.L → (∀ x, x ∈ abLocus t.G) → ∃ P : PELUnif (maximalIdeal R) t, P.TorsionIso ∧ Subsingleton P.D.toPre.X := by
  first | exact @GlobalTheory.GenFan.exists_pelUnif_torsionIso_subsingleton_of_abLocus | exact GlobalTheory.GenFan.exists_pelUnif_torsionIso_subsingleton_of_abLocus | (intros; apply GlobalTheory.GenFan.exists_pelUnif_torsionIso_subsingleton_of_abLocus <;> assumption)
