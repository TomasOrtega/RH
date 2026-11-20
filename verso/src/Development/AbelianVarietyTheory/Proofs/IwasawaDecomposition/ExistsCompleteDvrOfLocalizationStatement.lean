import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompleteDvrOfLocalization
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PrimeTrait.exists_cdvr_of_localization_atPrime` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsCompleteDvrOfLocalization.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_complete_dvr_of_localization : ∀ {R : Type} [CommRing R] [IsDomain R] [CharZero R] (Q : Ideal R) [Q.IsPrime], IsDiscreteValuationRing (Localization.AtPrime Q) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (ϖ : W) (g : R →+* W), CDvr W ∧ Irreducible ϖ ∧ Function.Injective g ∧ (∀ r, r ∉ Q → IsUnit (g r)) ∧ ∃ π ∈ Q, Associated (g π) ϖ := by
  first | exact @GlobalTheory.PrimeTrait.exists_cdvr_of_localization_atPrime | exact GlobalTheory.PrimeTrait.exists_cdvr_of_localization_atPrime | (intros; apply GlobalTheory.PrimeTrait.exists_cdvr_of_localization_atPrime <;> assumption)
