import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.PderivIterEqPderivListOfDifferentiableOn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPeriodPairIdealCurveLattice

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

namespace GlobalTheory.ConjugateLattice

/- English proof (translation)
Introduce `D _ cc δ hc M ρ h2 h3`. Take `⟨L, h⟩` from `GlobalTheory.CurveLattice.exists_periodPair_lamOf D cc δ hc`. Generalize the expression as in `lamOf D cc δ = Λ at h h2 h3`. Take `⟨-, -, hd, -, -, -, hex⟩` from `GlobalTheory.LatticeInvariants.invariants_dictionary L Λ h`. Establish `hne : ρ (TaylorLogMetric.liftM M (g2 Λ)) ^ 3 - 27 * ρ (TaylorLogMetric.liftM M (g3 Λ)) ^ 2 ≠ 0`.

Establish `e : ρ (TaylorLogMetric.liftM M (g2 Λ)) ^ 3 - 27 * ρ (TaylorLogMetric.liftM M (g3 Λ)) ^ 2 = ρ (TaylorLogMetric.liftM M (g2 Λ) ^ 3 - 27 * TaylorLogMetric.liftM M (g3 Λ) ^ 2)`. Simplify using `only [map_sub, map_mul, map_pow, map_ofNat]`. Rewrite using `[e, map_ne_zero]`. Introduce `h0`. Apply `hd` to reduce the goal to its premises.

Use `congrArg (fun y : M => (y : ℂ)) h0` as an intermediate fact. Simplify using `only [TaylorLogMetric.liftM, dif_pos h2, dif_pos h3] at this`. Conclude with `this`. Take `⟨L', ha, hb⟩` from `hex _ _ hne`. Take `⟨e2, e3, -, -, -, hun, -⟩` from `GlobalTheory.LatticeInvariants.invariants_dictionary L' L'.lattice.toAddSubgroup (fun _ => Iff.rfl)`.

Establish `hs` using `Classical.epsilon_spec (p := fun Λ' : AddSubgroup ℂ => g2 Λ' = ρ (TaylorLogMetric.liftM M (g2 Λ)) ∧ g3 Λ' = ρ (TaylorLogMetric.liftM M (g3 Λ))) ⟨_, e2.trans ha, e3.trans hb⟩`. Establish `hL : lamConj M ρ Λ = L'.lattice.toAddSubgroup` using `hun _ (hs.1.trans (e2.trans ha).symm) (hs.2.trans (e3.trans hb).symm)`. Use `⟨L'.ω₁, L'.ω₂, L'.indep, ?_⟩` and prove the remaining obligations. Rewrite using `[hL]`. Use extensionality with `z`.

Rewrite using `[Submodule.mem_toAddSubgroup, PeriodPair.mem_lattice, AddSubgroup.mem_closure_pair]`. Simplify using `only [zsmul_eq_mul]`.
-/
theorem lamConj_eq_closure_pair : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), g2 (lamOf D cc δ) ∈ M → g3 (lamOf D cc δ) ∈ M → ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ lamConj M ρ (lamOf D cc δ) = AddSubgroup.closure {w₁, w₂} := by
  intro D _ cc δ hc M ρ h2 h3
  obtain ⟨L, h⟩ := GlobalTheory.CurveLattice.exists_periodPair_lamOf D cc δ hc
  generalize lamOf D cc δ = Λ at h h2 h3
  obtain ⟨-, -, hd, -, -, -, hex⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L Λ h
  have hne : ρ (TaylorLogMetric.liftM M (g2 Λ)) ^ 3 - 27 * ρ (TaylorLogMetric.liftM M (g3 Λ)) ^ 2 ≠ 0 := by
    have e : ρ (TaylorLogMetric.liftM M (g2 Λ)) ^ 3 - 27 * ρ (TaylorLogMetric.liftM M (g3 Λ)) ^ 2 =
        ρ (TaylorLogMetric.liftM M (g2 Λ) ^ 3 - 27 * TaylorLogMetric.liftM M (g3 Λ) ^ 2) := by
      simp only [map_sub, map_mul, map_pow, map_ofNat]
    rw [e, map_ne_zero]
    intro h0
    apply hd
    have := congrArg (fun y : M => (y : ℂ)) h0
    simp only [TaylorLogMetric.liftM, dif_pos h2, dif_pos h3] at this
    exact this
  obtain ⟨L', ha, hb⟩ := hex _ _ hne
  obtain ⟨e2, e3, -, -, -, hun, -⟩ :=
    GlobalTheory.LatticeInvariants.invariants_dictionary L' L'.lattice.toAddSubgroup (fun _ => Iff.rfl)
  have hs := Classical.epsilon_spec (p := fun Λ' : AddSubgroup ℂ =>
    g2 Λ' = ρ (TaylorLogMetric.liftM M (g2 Λ)) ∧ g3 Λ' = ρ (TaylorLogMetric.liftM M (g3 Λ))) ⟨_, e2.trans ha, e3.trans hb⟩
  have hL : lamConj M ρ Λ = L'.lattice.toAddSubgroup :=
    hun _ (hs.1.trans (e2.trans ha).symm) (hs.2.trans (e3.trans hb).symm)
  refine ⟨L'.ω₁, L'.ω₂, L'.indep, ?_⟩
  rw [hL]
  ext z
  rw [Submodule.mem_toAddSubgroup, PeriodPair.mem_lattice, AddSubgroup.mem_closure_pair]
  simp only [zsmul_eq_mul]

end GlobalTheory.ConjugateLattice
