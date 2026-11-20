import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetBundleTrivialOnFibers
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DetTriv.detOm_trivial_of_point` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FDetBundleTrivialOnFibers.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.det_bundle_trivial_on_fibers : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (ρ : gen Y ⟶ gen X)
    (hY : (GlobalTheory.FlagMod.detOm Y).IsLB), Y.jQ ≫ ρ = X.jQ →
    ∀ (W : Scheme.{0}) (K : Type) [Field K] (g : W ⟶ gen Y) (a : W ⟶ Sp K) (y0 : Sp K ⟶ gen X), g ≫ ρ = a ≫ y0 →
    GlobalTheory.CechPic.pull (g ≫ genι Y) (GlobalTheory.CechPic.cls _ hY) = 0 := by
  first | exact @GlobalTheory.DetTriv.detOm_trivial_of_point | exact GlobalTheory.DetTriv.detOm_trivial_of_point | (intros; apply GlobalTheory.DetTriv.detOm_trivial_of_point <;> assumption)
