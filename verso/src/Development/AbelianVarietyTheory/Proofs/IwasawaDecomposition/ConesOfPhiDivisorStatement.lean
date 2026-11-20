import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConesOfPhiDivisor
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TorRef.RefineCones.hasCones_coneO` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FConesOfPhiDivisor.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.cones_of_phi_divisor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : GMod Xo c) (g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E)) (EX : EffCartierData Z.X) (N : ℕ), Module.finrank ℚ E * min D.p D.q ≤ g → IsPolFan id g φs → Refines H (min D.p D.q) φs 𝒩 φ → HasCones (ConeZ E φs) Z → 0 < N → IsPhiDiv (comb 0 φ N φ) Z EX → HasCones (ConeO H φ) Z := by
  first | exact @GlobalTheory.TorRef.RefineCones.hasCones_coneO | exact GlobalTheory.TorRef.RefineCones.hasCones_coneO | (intros; apply GlobalTheory.TorRef.RefineCones.hasCones_coneO <;> assumption)
