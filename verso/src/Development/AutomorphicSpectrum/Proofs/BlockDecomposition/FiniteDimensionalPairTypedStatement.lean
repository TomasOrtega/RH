import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalPairTyped
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemProdSpanInfStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalProdSpanStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LimV.FdPair.finiteDimensional_pairSpace_inf_typeHF` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFiniteDimensionalPairTyped.lean&line=76#L76)
-/
theorem _root_.GlobalTheory.T.finiteDimensional_pair_typed : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E))) (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)), FiniteDimensional ℂ (typed U₁ K₁ W₁) → FiniteDimensional ℂ (typed U₂ K₂ W₂) → FiniteDimensional ℂ ((pairSpace U₁ U₂ ⊓ typeHF K₁ K₂ W₁ W₂ : Submodule ℂ (H E a b → ℂ))) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.FdPair.finiteDimensional_pairSpace_inf_typeHF | exact GlobalTheory.CompanionTheory.LimV.FdPair.finiteDimensional_pairSpace_inf_typeHF | (intros; apply GlobalTheory.CompanionTheory.LimV.FdPair.finiteDimensional_pairSpace_inf_typeHF <;> assumption)
