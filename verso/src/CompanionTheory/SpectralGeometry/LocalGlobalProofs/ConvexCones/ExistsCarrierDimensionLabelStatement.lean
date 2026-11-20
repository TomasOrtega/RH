import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantCarrierDimPolyFan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsCarrierDimensionLabel
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FConvexCones%2FExistsCarrierDimensionLabel.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.exists_carrier_dimension_label : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (ψ : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q ψ → IsTwG w0 ψ → ∃ lab : InvFun O, IsTwG w0 lab ∧ IsCarrierDim bar q ψ lab := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.CarrierDimension.exists_isCarrierDim | exact GlobalTheory.CompanionTheory.Ar.Fan.CarrierDimension.exists_isCarrierDim | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.CarrierDimension.exists_isCarrierDim <;> assumption)
