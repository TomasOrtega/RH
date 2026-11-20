import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LineBundleIsoOfGenericIsoNormalLocalBase
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FLineBundleIsoOfGenericIsoNormalLocalBase.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.lineBundleIso_of_generic_iso_normal_local_base : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsNoetherianRing R → IsIntegrallyClosed R → ∀ (H : Scheme.{0}) (p : H ⟶ Sp R) (e : Sp R ⟶ H), Smooth p → QuasiCompact p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → ∀ L M : LB H, L.IsLB → M.IsLB → LBIso (L.pull (pullback.fst p (jK R))) (M.pull (pullback.fst p (jK R))) → LBIso L M := by
  first | exact @GlobalTheory.lbIso_of_generic_normal_local | exact GlobalTheory.lbIso_of_generic_normal_local | (intros; apply GlobalTheory.lbIso_of_generic_normal_local <;> assumption)
