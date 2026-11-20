import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteRestrictedProductQuotient
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutOfLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelFamInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousPairProjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsBisExtra
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.FinActS.finite_cosets_of_components_mem` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFiniteRestrictedProductQuotient.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.finite_restricted_product_quotient : ∀ {ι Γ : Type} [Group Γ] {Hl : ι → Type} [∀ i, Group (Hl i)] (p : ∀ i, Γ →* Hl i) (V : ∀ i, Subgroup (Hl i)) (Q : ∀ i, Set (Hl i))
    (hQ : ∀ i, ∀ x ∈ Q i, ∀ u ∈ V i, x * u ∈ Q i)
    (hQf : ∀ i, {q : Hl i ⧸ V i | q.out ∈ Q i}.Finite)
    (hQV : ∀ᶠ i in cofinite, Q i ⊆ V i),
    {q : Γ ⧸ (⨅ i, (V i).comap (p i)) | ∀ i, p i q.out ∈ Q i}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.FinActS.finite_cosets_of_components_mem | exact GlobalTheory.CompanionTheory.FinActS.finite_cosets_of_components_mem | (intros; apply GlobalTheory.CompanionTheory.FinActS.finite_cosets_of_components_mem <;> assumption)
