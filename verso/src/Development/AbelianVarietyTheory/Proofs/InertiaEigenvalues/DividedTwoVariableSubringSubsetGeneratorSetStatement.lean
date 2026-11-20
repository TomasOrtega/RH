import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedTwoVariableSubringSubsetGeneratorSet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNeZeroPs
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CrysPrism.PPd_subset_PPSet` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FDividedTwoVariableSubringSubsetGeneratorSet.lean&line=98#L98)
-/
theorem _root_.GlobalTheory.T.dividedTwoVariableSubring_subset_generatorSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ PPd t K e, F ∈ PPSet t K e := by
  first | exact @GlobalTheory.CrysPrism.PPd_subset_PPSet | exact GlobalTheory.CrysPrism.PPd_subset_PPSet | (intros; apply GlobalTheory.CrysPrism.PPd_subset_PPSet <;> assumption)
