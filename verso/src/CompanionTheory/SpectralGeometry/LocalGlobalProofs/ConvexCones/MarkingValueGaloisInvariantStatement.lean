import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MarkingValueGaloisInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedFormIndicatorValueInvariantHostFixingAut
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkValEqZeroOrOne
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Fan.TwistedForm.markVal_twist` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FConvexCones%2FMarkingValueGaloisInvariant.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.marking_value_galois_invariant : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (ψ lab : InvFun O) (i : ℕ), IsTwG w0 ψ → IsTwG w0 lab → ∀ σ : O ≃+* O, σ w0 = w0 → ∀ (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ), markVal bar ψ lab i n (fun a b => B (fun j => σ (a j)) (fun j => σ (b j))) = markVal bar ψ lab i n B := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.TwistedForm.markVal_twist | exact GlobalTheory.CompanionTheory.Ar.Fan.TwistedForm.markVal_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.TwistedForm.markVal_twist <;> assumption)
