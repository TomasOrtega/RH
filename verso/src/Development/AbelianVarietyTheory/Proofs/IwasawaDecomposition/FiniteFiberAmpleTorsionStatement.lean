import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteFiberAmpleTorsion
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FFiniteFiberAmpleTorsion.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.finite_fiber_ample_torsion : ∀ {S S' T : Scheme.{0}} (q : S ⟶ T) (h : S ⟶ S') (L : LB S'), IsProper q → IsAffineHom h →
    ∀ hA : GlobalTheory.IsAmpleLB L, ∀ t : T,
    (∃ m : ℕ, 0 < m ∧ GlobalTheory.CechPic.pull (q.fiberι t ≫ h) (m • GlobalTheory.CechPic.cls L hA.isLB) = 0) → (q ⁻¹' {t}).Finite := by
  first | exact @GlobalTheory.FibreFinite.finite_preimage | exact GlobalTheory.FibreFinite.finite_preimage | (intros; apply GlobalTheory.FibreFinite.finite_preimage <;> assumption)
