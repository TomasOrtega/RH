import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmallDualLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.DualScaledIntegers

/- English proof (translation)
Introduce `F E _ _ _ _ U A ψ hψ c hc`. Use `U.ultraF` as an intermediate fact. Use `U.lcF` as an intermediate fact. Take `⟨-, -, hnd, -, -, -, -, -, -, hop, hcp, R, hR⟩` from `GlobalTheory.T.etaleHermitianPair_structure_facts F E A`. Use `haveI : ContinuousSMul F A.K := IsModuleTopology.toContinuousSMul F A.K`.

Set `D : AddSubgroup A.K` to `{ carrier := {b : A.K | ∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1} zero_mem' := by`. Introduce `z _`. Simplify using `[Et.psiK]`. Use the proof step `add_mem' := by`. Introduce `a b ha hb z hz`.

Establish `h1` using `ha z hz`. Establish `h2` using `hb z hz`. Simplify using `only [Et.psiK] at h1 h2 ⊢`. Rewrite using `[mul_add, map_add, AddChar.map_add_eq_mul, h1, h2, one_mul]`. Use the proof step `neg_mem' := by`.

Introduce `a ha z hz`. Establish `h1` using `ha z hz`. Simplify using `only [Et.psiK] at h1 ⊢`. Rewrite using `[mul_neg, map_neg, AddChar.map_neg_eq_inv, h1, inv_one] }`. Establish `hcs : Continuous fun z : A.K => c • z` using `continuous_const_smul c`.

Establish `hM : IsCompact {z : A.K | c • z ∈ A.OK}`. Establish `: {z : A.K | c • z ∈ A.OK} = (fun z : A.K => c⁻¹ • z) '' A.OK`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce `hz`.

Conclude with `⟨c • z, hz, inv_smul_smul₀ hc z⟩`. Introduce and unpack `⟨w, hw, rfl⟩ show c • c⁻¹ • w ∈ A.OK`. Rewrite using `[smul_inv_smul₀ hc]` and apply the resulting hypothesis. Rewrite using `[this]`. Conclude with `hcp.image (continuous_const_smul _)`.

Establish `htr : Continuous (Algebra.trace F A.K)` using `IsModuleTopology.continuous_of_linearMap _`. Establish `hDo : IsOpen (D : Set A.K)`. Use `AddSubgroup.isOpen_of_mem_nhds D (g := 0) ?_` and prove the remaining obligations. Establish `h` using `hM.eventually_forall_of_forall_eventually (x₀ := (0 : A.K)) (P := fun b z => A.psiK ψ (z * b) = 1) (fun y _ => by`. Establish `hc2 : Continuous fun p : A.K × A.K => Algebra.trace F A.K (p.2 * p.1)` using `htr.comp (continuous_snd.mul continuous_fst)`.

Establish `h0 : Metric.closedBall (0 : F) 1 ∈ 𝓝 (Algebra.trace F A.K (((0 : A.K), y).2 * ((0 : A.K), y).1))`. Simplify using `using Metric.closedBall_mem_nhds (0 : F) one_pos`. Use `filter_upwards [hc2.continuousAt.preimage_mem_nhds h0] with p hp`. Conclude with `hψ.1 _ (by simpa using hp))`. Conclude with `h`.

Use `⟨D, rfl, hDo, ?_⟩` and prove the remaining obligations. Establish `hU : {z : A.K | c • z ∈ A.OK} ∈ 𝓝 (0 : A.K)`. Use `(hop.preimage hcs).mem_nhds ?_` and prove the remaining obligations. Use `show c • (0 : A.K) ∈ A.OK`. Rewrite using `[smul_zero, ← hR]`.

Conclude with `R.zero_mem`. Take `⟨M, N, hMU, -, -, -, hN, hMN, -⟩` from `(exists_small_dual_lattices F ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm F) hnd).2 _ hU`. Use `hN.of_isClosed_subset (D.isClosed_of_isOpen hDo) fun b hb => ?_` and prove the remaining obligations. Conclude with `(hMN b).2 fun x hx => hb x (hMU hx)`.
-/
theorem exists_open_compact_annihilator : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ c : F, c ≠ 0 → ∃ D : AddSubgroup A.K, (D : Set A.K) = {b : A.K | ∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1} ∧ IsOpen (D : Set A.K) ∧ IsCompact (D : Set A.K) := by
  intro F E _ _ _ _ U A ψ hψ c hc
  have := U.ultraF
  have := U.lcF
  obtain ⟨-, -, hnd, -, -, -, -, -, -, hop, hcp, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  haveI : ContinuousSMul F A.K := IsModuleTopology.toContinuousSMul F A.K
  let D : AddSubgroup A.K :=
    { carrier := {b : A.K | ∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1}
      zero_mem' := by
        intro z _
        simp [Et.psiK]
      add_mem' := by
        intro a b ha hb z hz
        have h1 := ha z hz
        have h2 := hb z hz
        simp only [Et.psiK] at h1 h2 ⊢
        rw [mul_add, map_add, AddChar.map_add_eq_mul, h1, h2, one_mul]
      neg_mem' := by
        intro a ha z hz
        have h1 := ha z hz
        simp only [Et.psiK] at h1 ⊢
        rw [mul_neg, map_neg, AddChar.map_neg_eq_inv, h1, inv_one] }
  have hcs : Continuous fun z : A.K => c • z := continuous_const_smul c
  have hM : IsCompact {z : A.K | c • z ∈ A.OK} := by
    have : {z : A.K | c • z ∈ A.OK} = (fun z : A.K => c⁻¹ • z) '' A.OK := by
      ext z
      constructor
      · intro hz
        exact ⟨c • z, hz, inv_smul_smul₀ hc z⟩
      · rintro ⟨w, hw, rfl⟩
        show c • c⁻¹ • w ∈ A.OK
        rwa [smul_inv_smul₀ hc]
    rw [this]
    exact hcp.image (continuous_const_smul _)
  have htr : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
  have hDo : IsOpen (D : Set A.K) := by
    refine AddSubgroup.isOpen_of_mem_nhds D (g := 0) ?_
    have h := hM.eventually_forall_of_forall_eventually (x₀ := (0 : A.K))
      (P := fun b z => A.psiK ψ (z * b) = 1) (fun y _ => by
        have hc2 : Continuous fun p : A.K × A.K => Algebra.trace F A.K (p.2 * p.1) :=
          htr.comp (continuous_snd.mul continuous_fst)
        have h0 : Metric.closedBall (0 : F) 1 ∈ 𝓝 (Algebra.trace F A.K (((0 : A.K), y).2 * ((0 : A.K), y).1)) := by
          simpa using Metric.closedBall_mem_nhds (0 : F) one_pos
        filter_upwards [hc2.continuousAt.preimage_mem_nhds h0] with p hp
        exact hψ.1 _ (by simpa using hp))
    exact h
  refine ⟨D, rfl, hDo, ?_⟩
  have hU : {z : A.K | c • z ∈ A.OK} ∈ 𝓝 (0 : A.K) := by
    refine (hop.preimage hcs).mem_nhds ?_
    show c • (0 : A.K) ∈ A.OK
    rw [smul_zero, ← hR]
    exact R.zero_mem
  obtain ⟨M, N, hMU, -, -, -, hN, hMN, -⟩ :=
    (exists_small_dual_lattices F ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm F) hnd).2 _ hU
  refine hN.of_isClosed_subset (D.isClosed_of_isOpen hDo) fun b hb => ?_
  exact (hMN b).2 fun x hx => hb x (hMU hx)

end GlobalTheory.JR.DualScaledIntegers
