import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCartierOnNormalizedBlowup
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.effCartier_comap_blowup_normal` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsCartierOnNormalizedBlowup.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.exists_cartier_on_normalized_blowup : ∀ (K : Type) [Field K] [NumberField K] (X X' N : Scheme.{0}) (s : X ⟶ Sp (𝓞 K)) (J : X.IdealSheafData)
    (b : X' ⟶ X) (ν : N ⟶ X'), IsProjOver s → Dense ((J.support : Set X)ᶜ) → FinalTheorems.Blowup b J → IsFinite ν →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N → IsIso (ν ∣_ (b ⁻¹ᵁ J.support.compl)) →
    Dense ((ν ⁻¹ᵁ (b ⁻¹ᵁ J.support.compl) : N.Opens) : Set N) →
    ∃ EX : GlobalTheory.EffCartierData N, EX.idealSheaf = J.comap (ν ≫ b) := by
  first | exact @GlobalTheory.effCartier_comap_blowup_normal | exact GlobalTheory.effCartier_comap_blowup_normal | (intros; apply GlobalTheory.effCartier_comap_blowup_normal <;> assumption)
