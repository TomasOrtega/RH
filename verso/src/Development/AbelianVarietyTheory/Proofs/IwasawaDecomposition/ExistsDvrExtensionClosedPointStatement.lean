import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDvrExtensionClosedPoint
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartMem
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsDvrExtensionClosedPoint.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.exists_dvr_extension_closed_point : ∀ (X : Scheme.{0}) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ X), IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ (χ : Sp W ⟶ X), χ (closedPoint W) = ξ (closedPoint R) → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (f : W →+* V) (ψ : R →+* V), CDvr V ∧ Function.Injective f ∧ IsLocalHom f ∧ IsLocalHom ψ ∧ Irreducible (f ϖ) ∧ spMap f ≫ χ = spMap ψ ≫ ξ := by
  first | exact @GlobalTheory.TraitLift.exists_lift | exact GlobalTheory.TraitLift.exists_lift | (intros; apply GlobalTheory.TraitLift.exists_lift <;> assumption)
