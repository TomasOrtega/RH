import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIInfKerSemilinearStandardBasis
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
open Module
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BadCount.finrank_iInf_ker_semilinear` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFinrankIInfKerSemilinearStandardBasis.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.finrank_iInf_ker_semilinear_standardBasis : ∀ (K V ι : Type) [Field K] [AddCommGroup V] [Module ℂ V] [Finite ι] (σ : K →+* ℂ) (N : ℕ) (f : (Fin N → K) →ₛₗ[σ] V), (LinearIndependent ℂ fun k => f (Pi.single k 1)) → Submodule.span ℂ (Set.range f) = ⊤ → ∀ (a : ι → (Fin N → K) →ₗ[K] (Fin N → K)) (a' : ι → V →ₗ[ℂ] V), (∀ i v, a' i (f v) = f (a i v)) → finrank ℂ (⨅ i, LinearMap.ker (a' i) : Submodule ℂ V) = finrank K (⨅ i, LinearMap.ker (a i) : Submodule K (Fin N → K)) := by
  first | exact @GlobalTheory.BadCount.finrank_iInf_ker_semilinear | exact GlobalTheory.BadCount.finrank_iInf_ker_semilinear | (intros; apply GlobalTheory.BadCount.finrank_iInf_ker_semilinear <;> assumption)
