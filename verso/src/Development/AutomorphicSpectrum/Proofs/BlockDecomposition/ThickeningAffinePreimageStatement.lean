import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningAffinePreimage
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FThickeningAffinePreimage.lean&line=96#L96)
-/
theorem _root_.GlobalTheory.T.thickening_affine_preimage : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (L : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e))) (hL : ∀ e, (L e).IsLB ∧ (w e).IsGen) (e : ℕ) (V : (Y (e + 1)).left.Opens) (V' : (Y e).left.Opens) (h : β e ⁻¹ᵁ V = V'), IsAffineOpen V → Function.Surjective (redL I Y β hβ L w hL e V V' h.ge) ∧ LinearMap.ker (redL I Y β hβ L w hL e V V' h.ge) = I ^ (e + 1) • ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.redL_surjective_ker | exact GlobalTheory.CompanionTheory.FormalAlg.Lift.redL_surjective_ker | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.Lift.redL_surjective_ker <;> assumption)
