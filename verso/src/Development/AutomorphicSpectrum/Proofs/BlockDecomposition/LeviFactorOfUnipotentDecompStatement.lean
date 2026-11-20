import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviFactorOfUnipotentDecomp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLeviFactorOfUnipotentDecomp.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.levi_factor_of_unipotent_decomp : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ} (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s)) (c : GL (Fin (r + s)) (Af E)), c ∈ KO E (r + s) → unip u * lev (Ad E) r s m = cf (r + s) k c → ∃ (k₁ : Kinf E r) (c₁ : GL (Fin r) (Af E)) (k₂ : Kinf E s) (c₂ : GL (Fin s) (Af E)), c₁ ∈ KO E r ∧ c₂ ∈ KO E s ∧ m = (cf r k₁ c₁, cf s k₂ c₂) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.LeviCf.levi_cf_integral | exact GlobalTheory.CompanionTheory.LimV.LeviCf.levi_cf_integral | (intros; apply GlobalTheory.CompanionTheory.LimV.LeviCf.levi_cf_integral <;> assumption)
