import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TensorQuotientQuantumDeterminantEigen
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasCharSub
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantAntiHomomorphismStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CommutingLocallyNilpotentCommonKernelStatement
open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL GlobalTheory.CompanionTheory.RgTransport
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FTensorQuotientQuantumDeterminantEigen.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.tensor_quotient_quantum_determinant_eigen : StepChar → TensDecomp → ∀ {m : ℕ} (M : GMod m) (χ : Fin m → ℂ), HasChar M χ → ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin m → Fin m → Module.End ℂ V), GlRel E → ∀ Φ : (Fin m → M.V) →ₗ[ℂ] V, (∀ a b u, Φ (tensE M a b u) = E a b (Φ u)) → Φ ≠ 0 → ∃ r, ∃ w ∈ LinearMap.range Φ, w ≠ 0 ∧ ∀ Y : ℂ, qdet E (Y + ((m : ℂ) - 1) / 2) w = Formalism.QuantumDeterminants.capP (χ + Pi.single r 1) Y • w := by
  first | exact @GlobalTheory.CompanionTheory.RgTransport.Raise.exists_raised | exact GlobalTheory.CompanionTheory.RgTransport.Raise.exists_raised | (intros; apply GlobalTheory.CompanionTheory.RgTransport.Raise.exists_raised <;> assumption)
