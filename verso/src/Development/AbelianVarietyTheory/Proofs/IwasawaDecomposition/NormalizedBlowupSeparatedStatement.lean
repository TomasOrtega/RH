import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalizedBlowupSeparated
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FNormalizedBlowupSeparated.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.normalized_blowup_separated : ∀ (K : Type) [Field K] [NumberField K] (X X' N : Scheme.{0}) (s : X ⟶ Sp (𝓞 K)) (J : X.IdealSheafData) (b : X' ⟶ X)
    (ν : N ⟶ X'), IsProjOver s → FinalTheorems.Blowup b J → IsFinite ν → IsLocallyNoetherian N ∧ IsSeparated (ν ≫ b ≫ s) := by
  first | exact @GlobalTheory.TorRef.blowup_finite_noeth_sep | exact GlobalTheory.TorRef.blowup_finite_noeth_sep | (intros; apply GlobalTheory.TorRef.blowup_finite_noeth_sep <;> assumption)
