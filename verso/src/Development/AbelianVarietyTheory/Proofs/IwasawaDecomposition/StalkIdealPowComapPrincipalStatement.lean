import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkIdealPowComapPrincipal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FStalkIdealPowComapPrincipal.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.stalk_ideal_pow_comap_principal : ∀ {Y V : Scheme.{0}} (D : EffCartierData Y) (n : ℕ) (g : V ⟶ Y) (v : V), (FinalTheorems.stalkId ((D.idealSheaf ^ n).comap g) v).IsPrincipal := by
  first | exact @GlobalTheory.PrincStalk.stalkId_comap_pow_isPrincipal | exact GlobalTheory.PrincStalk.stalkId_comap_pow_isPrincipal | (intros; apply GlobalTheory.PrincStalk.stalkId_comap_pow_isPrincipal <;> assumption)
