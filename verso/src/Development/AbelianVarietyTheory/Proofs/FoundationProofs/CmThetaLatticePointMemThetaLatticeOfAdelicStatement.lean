import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaLatticePointMemThetaLatticeOfAdelic
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NormSum.pt_mem_La_of_adelic` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FCmThetaLatticePointMemThetaLatticeOfAdelic.lean&line=118#L118)
-/
theorem _root_.GlobalTheory.T.cmThetaLatticePoint_mem_thetaLattice_of_adelic : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → ∀ (N N' : ℕ) (g : GA D N) (g' : GA D N') (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → ∀ z : Matrix (Fin N') (Fin N) D.host.E, (∀ i j, ((((g' : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) * ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) i j ∈ IhE D cc) → pt D (tor0 D cc δ) δ z ∈ La D (tor0 D cc δ) L₁ L₁' := by
  first | exact @GlobalTheory.NormSum.pt_mem_La_of_adelic | exact GlobalTheory.NormSum.pt_mem_La_of_adelic | (intros; apply GlobalTheory.NormSum.pt_mem_La_of_adelic <;> assumption)
