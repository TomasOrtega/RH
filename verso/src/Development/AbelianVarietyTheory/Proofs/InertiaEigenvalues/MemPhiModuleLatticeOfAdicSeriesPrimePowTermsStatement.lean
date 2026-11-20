import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemPhiModuleLatticeOfAdicSeriesPrimePowTerms
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BK.PhiMod.mem_MM_of_series` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FMemPhiModuleLatticeOfAdicSeriesPrimePowTerms.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.mem_phiModuleLattice_of_adic_series_prime_pow_terms : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι), ∀ (w : Vec K a ι) (t : ℕ → Vec K a ι), (∀ n, ∃ v ∈ P.MM, t n = (l : K) ^ n • v) → (∀ m, w - ∑ n ∈ Finset.range m, t n ∈ uPow K a ι m) → w ∈ P.MM := by
  first | exact @GlobalTheory.BK.PhiMod.mem_MM_of_series | exact GlobalTheory.BK.PhiMod.mem_MM_of_series | (intros; apply GlobalTheory.BK.PhiMod.mem_MM_of_series <;> assumption)
