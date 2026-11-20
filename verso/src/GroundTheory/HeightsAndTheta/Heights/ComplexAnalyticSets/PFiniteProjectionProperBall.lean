import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteProjectionProperBall
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

/- English proof (translation)
Introduce `σ _ X w d A hX hiso U hU`. Take `⟨N, k, f, hNo, hwN, hf, hXN⟩` from `hX`. Take `⟨W, hW, hWiso⟩` from `hiso`. Establish `hmem : N ∩ U ∩ W ∈ 𝓝 w` using `Filter.inter_mem (Filter.inter_mem (hNo.mem_nhds hwN) hU) hW`. Take `⟨ρ, hρ, hball⟩` from `Metric.nhds_basis_closedBall.mem_iff.mp hmem`.

Establish `hBN : Metric.closedBall w ρ ⊆ N` using `fun x hx => (hball hx).1.1`. Use `set C : Set (σ → ℂ) := Metric.closedBall w ρ ∩ (fun z i => f i z) ⁻¹' {0} with hCdef`. Establish `hCX : ∀ x ∈ C, x ∈ X`. Introduce `x hx`. Establish `hxN` using `hBN hx.1`.

Establish `: x ∈ X ∩ N`. Rewrite using `[hXN]`. Use `⟨hxN, fun i => ?_⟩` and prove the remaining obligations. Use `congrFun (show (fun i => f i x) = 0 from hx.2) i` as an intermediate fact. Simplify using `using this`.

Conclude with `this.1`. Establish `hXC : ∀ x ∈ X, x ∈ Metric.closedBall w ρ → x ∈ C`. Introduce `x hxX hxB`. Establish `: x ∈ {z | z ∈ N ∧ ∀ i, f i z = 0}` using `hXN ▸ ⟨hxX, hBN hxB⟩`. Use `⟨hxB, ?_⟩` and prove the remaining obligations.

Use `show (fun i => f i x) = 0`. Use function extensionality and compare the values at `i`. Simplify using `using this.2 i`. Establish `hCcl : IsClosed C`. Use `ContinuousOn.preimage_isClosed_of_isClosed ?_ Metric.isClosed_closedBall isClosed_singleton` and prove the remaining obligations.

Conclude with `continuousOn_pi.mpr fun i => ((hf i).continuousOn).mono hBN`. Establish `hC : IsCompact C` using `(isCompact_closedBall w ρ).of_isClosed_subset hCcl Set.inter_subset_left`. Use `set S : Set (σ → ℂ) := C ∩ Metric.sphere w ρ with hSdef`. Establish `hS : IsCompact S` using `hC.inter_right Metric.isClosed_sphere`. Establish `hT : IsCompact (A '' S)` using `hS.image A.continuous`.

Establish `hAw : A w ∉ A '' S`. Introduce and unpack `⟨x, hxS, hxA⟩`. Establish `hxw : x = w` using `hWiso x ⟨hCX x hxS.1, (hball hxS.1.1).2⟩ hxA`. Establish `hd` using `hxS.2`. Rewrite `hd` using `[hxw, Metric.mem_sphere, dist_self]`.

Conclude with `hρ.ne hd`. Take `⟨r, hr, hrT⟩` from `Metric.isOpen_iff.mp hT.isClosed.isOpen_compl (A w) hAw`. Use `⟨ρ, hρ, r, hr, fun x hx => (hball (Metric.ball_subset_closedBall hx)).1.2, ?_⟩` and prove the remaining obligations. Introduce `K hKr hK`. Establish `heq : {x | x ∈ X ∩ Metric.ball w ρ ∧ A x ∈ K} = C ∩ A ⁻¹' K`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨hxX, hxB⟩, hxK⟩`. Conclude with `⟨hXC x hxX (Metric.ball_subset_closedBall hxB), hxK⟩`. Introduce and unpack `⟨hxC, hxK⟩`.

Use `⟨⟨hCX x hxC, ?_⟩, hxK⟩` and prove the remaining obligations. Establish `hle : dist x w ≤ ρ` using `hxC.1`. Break down `hle.lt_or_eq with hlt | heq` into its components or cases. Conclude with `hlt`. Conclude with `absurd ⟨x, ⟨hxC, heq⟩, rfl⟩ (hrT (hKr hxK))`.

Rewrite using `[heq]`. Conclude with `hC.inter_right (hK.isClosed.preimage A.continuous)`.
-/
theorem FiniteProjectionProperBall.proof : FiniteProjectionProperBall.Statement := by
  intro σ _ X w d A hX hiso U hU
  obtain ⟨N, k, f, hNo, hwN, hf, hXN⟩ := hX
  obtain ⟨W, hW, hWiso⟩ := hiso
  have hmem : N ∩ U ∩ W ∈ 𝓝 w := Filter.inter_mem (Filter.inter_mem (hNo.mem_nhds hwN) hU) hW
  obtain ⟨ρ, hρ, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hmem
  have hBN : Metric.closedBall w ρ ⊆ N := fun x hx => (hball hx).1.1

  set C : Set (σ → ℂ) := Metric.closedBall w ρ ∩ (fun z i => f i z) ⁻¹' {0} with hCdef
  have hCX : ∀ x ∈ C, x ∈ X := by
    intro x hx
    have hxN := hBN hx.1
    have : x ∈ X ∩ N := by
      rw [hXN]
      refine ⟨hxN, fun i => ?_⟩
      have := congrFun (show (fun i => f i x) = 0 from hx.2) i
      simpa using this
    exact this.1
  have hXC : ∀ x ∈ X, x ∈ Metric.closedBall w ρ → x ∈ C := by
    intro x hxX hxB
    have : x ∈ {z | z ∈ N ∧ ∀ i, f i z = 0} := hXN ▸ ⟨hxX, hBN hxB⟩
    refine ⟨hxB, ?_⟩
    show (fun i => f i x) = 0
    funext i
    simpa using this.2 i
  have hCcl : IsClosed C := by
    refine ContinuousOn.preimage_isClosed_of_isClosed ?_ Metric.isClosed_closedBall isClosed_singleton
    exact continuousOn_pi.mpr fun i => ((hf i).continuousOn).mono hBN
  have hC : IsCompact C := (isCompact_closedBall w ρ).of_isClosed_subset hCcl Set.inter_subset_left

  set S : Set (σ → ℂ) := C ∩ Metric.sphere w ρ with hSdef
  have hS : IsCompact S := hC.inter_right Metric.isClosed_sphere
  have hT : IsCompact (A '' S) := hS.image A.continuous
  have hAw : A w ∉ A '' S := by
    rintro ⟨x, hxS, hxA⟩
    have hxw : x = w := hWiso x ⟨hCX x hxS.1, (hball hxS.1.1).2⟩ hxA
    have hd := hxS.2
    rw [hxw, Metric.mem_sphere, dist_self] at hd
    exact hρ.ne hd
  obtain ⟨r, hr, hrT⟩ := Metric.isOpen_iff.mp hT.isClosed.isOpen_compl (A w) hAw
  refine ⟨ρ, hρ, r, hr, fun x hx => (hball (Metric.ball_subset_closedBall hx)).1.2, ?_⟩
  intro K hKr hK
  have heq : {x | x ∈ X ∩ Metric.ball w ρ ∧ A x ∈ K} = C ∩ A ⁻¹' K := by
    ext x
    constructor
    · rintro ⟨⟨hxX, hxB⟩, hxK⟩
      exact ⟨hXC x hxX (Metric.ball_subset_closedBall hxB), hxK⟩
    · rintro ⟨hxC, hxK⟩
      refine ⟨⟨hCX x hxC, ?_⟩, hxK⟩
      have hle : dist x w ≤ ρ := hxC.1
      rcases hle.lt_or_eq with hlt | heq
      · exact hlt
      · exact absurd ⟨x, ⟨hxC, heq⟩, rfl⟩ (hrT (hKr hxK))
  rw [heq]
  exact hC.inter_right (hK.isClosed.preimage A.continuous)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
