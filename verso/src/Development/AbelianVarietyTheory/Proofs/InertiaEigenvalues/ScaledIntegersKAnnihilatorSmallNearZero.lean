import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmallDualLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

/- English proof (translation)
Introduce `F E _ _ _ _ hU A ψ hψ U hUmem`. Use `haveI : IsUltrametricDist F := hU.ultraF`. Use `haveI : LocallyCompactSpace F := hU.lcF`. Use `haveI : ContinuousSMul F A.K := IsModuleTopology.toContinuousSMul F A.K`. Establish `hfacts` using `GlobalTheory.T.etaleHermitianPair_structure_facts F E A`.

Establish `hnd : (Algebra.traceForm F A.K).Nondegenerate` using `hfacts.2.2.1`. Establish `hOKopen : IsOpen A.OK` using `hfacts.2.2.2.2.2.2.2.2.2.1`. Take `⟨R, hR⟩` from `hfacts.2.2.2.2.2.2.2.2.2.2.2`. Establish `h0 : (0 : A.K) ∈ A.OK` using `by rw [← hR]; exact R.zero_mem`. Take `⟨-, hsmall⟩` from `GlobalTheory.JR.exists_small_dual_lattices F ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm F (S := A.K)) hnd`.

Take `⟨M, N, hMU, -, -, -, hNc, -, hM⟩` from `hsmall U hUmem`. Establish `hev : ∀ᶠ c in 𝓝 (0 : F), ∀ y ∈ (N : Set A.K), c • y ∈ A.OK`. Use `hNc.eventually_forall_of_forall_eventually fun y _ => ?_` and prove the remaining obligations. Establish `hc : ContinuousAt (fun p : F × A.K => p.1 • p.2) ((0 : F), y)` using `continuous_smul.continuousAt`. Establish `: A.OK ∈ 𝓝 ((fun p : F × A.K => p.1 • p.2) ((0 : F), y))`.

Simplify using `using hOKopen.mem_nhds h0`. Conclude with `hc this`. Use `filter_upwards [nhdsWithin_le_nhds hev] with c hc b hb`. Apply `hMU` to reduce the goal to its premises. Rewrite using `[SetLike.mem_coe, hM]`.

Introduce `y hy`. Use `hb y (hc y hy)` as an intermediate fact. Simplify `this` using `[Et.psiK, Algebra.traceForm_apply, mul_comm]`.
-/
theorem GlobalTheory.JR.annihilator_small : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ U ∈ 𝓝 (0 : A.K), ∀ᶠ c in 𝓝[≠] (0 : F), ∀ b : A.K, (∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1) → b ∈ U := by
  intro F E _ _ _ _ hU A ψ hψ U hUmem
  haveI : IsUltrametricDist F := hU.ultraF
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ContinuousSMul F A.K := IsModuleTopology.toContinuousSMul F A.K
  have hfacts := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  have hnd : (Algebra.traceForm F A.K).Nondegenerate := hfacts.2.2.1
  have hOKopen : IsOpen A.OK := hfacts.2.2.2.2.2.2.2.2.2.1
  obtain ⟨R, hR⟩ := hfacts.2.2.2.2.2.2.2.2.2.2.2
  have h0 : (0 : A.K) ∈ A.OK := by rw [← hR]; exact R.zero_mem
  obtain ⟨-, hsmall⟩ := GlobalTheory.JR.exists_small_dual_lattices F ψ hψ A.K (Algebra.traceForm F A.K)
    (Algebra.traceForm_isSymm F (S := A.K)) hnd
  obtain ⟨M, N, hMU, -, -, -, hNc, -, hM⟩ := hsmall U hUmem
  have hev : ∀ᶠ c in 𝓝 (0 : F), ∀ y ∈ (N : Set A.K), c • y ∈ A.OK := by
    refine hNc.eventually_forall_of_forall_eventually fun y _ => ?_
    have hc : ContinuousAt (fun p : F × A.K => p.1 • p.2) ((0 : F), y) := continuous_smul.continuousAt
    have : A.OK ∈ 𝓝 ((fun p : F × A.K => p.1 • p.2) ((0 : F), y)) := by
      simpa using hOKopen.mem_nhds h0
    exact hc this
  filter_upwards [nhdsWithin_le_nhds hev] with c hc b hb
  apply hMU
  rw [SetLike.mem_coe, hM]
  intro y hy
  have := hb y (hc y hy)
  simpa [Et.psiK, Algebra.traceForm_apply, mul_comm] using this
