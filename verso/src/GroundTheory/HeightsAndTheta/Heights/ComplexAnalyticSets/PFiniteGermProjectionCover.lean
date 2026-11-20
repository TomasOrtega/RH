import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteGermProjectionCover
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermProjectionOpenNear
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProperOpenProjectionCover
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

/- English proof (translation)
Introduce `σ _ X w d A hX hirr hiso hinj`. Take `⟨N₀, hN₀, hop⟩` from `hopen σ X w d A hX hirr hiso hinj`. Take `⟨N, k, f, hNo, hwN, hf, hXN⟩` from `hX`. Use `⟨interior N₀ ∩ N, Filter.inter_mem (interior_mem_nhds.2 hN₀) (hNo.mem_nhds hwN), ?_⟩` and prove the remaining obligations. Introduce `B D hBo hBN hwB hDo hDc hmaps hprop hisoB`.

Establish `hBN' : B ⊆ N` using `fun x hx => (hBN hx).2`. Establish `hzero : X ∩ B = {z | z ∈ B ∧ ∀ i, f i z = 0}`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hzX, hzB⟩`.

Establish `h1 : z ∈ X ∩ N` using `⟨hzX, hBN' hzB⟩`. Rewrite `h1` using `[hXN]`. Conclude with `⟨hzB, h1.2⟩`. Introduce and unpack `⟨hzB, hz⟩`. Establish `h2 : z ∈ {z | z ∈ N ∧ ∀ i, f i z = 0}` using `⟨hBN' hzB, hz⟩`.

Rewrite `h2` using `[← hXN]`. Conclude with `⟨h2.1, hzB⟩`. Establish `hopB : ∀ x ∈ X ∩ B, ∀ V ∈ 𝓝 x, A '' (X ∩ B ∩ V) ∈ 𝓝 (A x)`. Introduce `x hx V hV`. Establish `h1` using `hop x ⟨hx.1, interior_subset (hBN hx.2).1⟩ (V ∩ B) (Filter.inter_mem hV (hBo.mem_nhds hx.2))`.

Establish `h2 : X ∩ (V ∩ B) = X ∩ B ∩ V`. Use extensionality with `z`. Simplify using `only [Set.mem_inter_iff]`. The claim follows by propositional logic. Rewrite `h1` using `[h2]`. Then use the resulting hypothesis.

Take `⟨δ, M, hδ, hδne, hcount, hgraph, hdense⟩` from `hcov σ X B k f d A D hBo (fun i => (hf i).mono hBN') hzero hDo hDc ⟨A w, hmaps hwB⟩ hmaps hprop hopB`. Conclude with `⟨δ, M, hBo, hwB, hDo, hDc, hmaps, hprop, hisoB, hδ, hδne, hcount, hgraph, hdense⟩`.
-/
theorem FiniteGermProjectionCover.proof (hopen : IrreducibleGermProjectionOpenNear.Statement)
    (hcov : ProperOpenProjectionCover.Statement) : FiniteGermProjectionCover.Statement := by
  intro σ _ X w d A hX hirr hiso hinj
  obtain ⟨N₀, hN₀, hop⟩ := hopen σ X w d A hX hirr hiso hinj
  obtain ⟨N, k, f, hNo, hwN, hf, hXN⟩ := hX
  refine ⟨interior N₀ ∩ N, Filter.inter_mem (interior_mem_nhds.2 hN₀) (hNo.mem_nhds hwN), ?_⟩
  intro B D hBo hBN hwB hDo hDc hmaps hprop hisoB
  have hBN' : B ⊆ N := fun x hx => (hBN hx).2

  have hzero : X ∩ B = {z | z ∈ B ∧ ∀ i, f i z = 0} := by
    ext z
    constructor
    · rintro ⟨hzX, hzB⟩
      have h1 : z ∈ X ∩ N := ⟨hzX, hBN' hzB⟩
      rw [hXN] at h1
      exact ⟨hzB, h1.2⟩
    · rintro ⟨hzB, hz⟩
      have h2 : z ∈ {z | z ∈ N ∧ ∀ i, f i z = 0} := ⟨hBN' hzB, hz⟩
      rw [← hXN] at h2
      exact ⟨h2.1, hzB⟩

  have hopB : ∀ x ∈ X ∩ B, ∀ V ∈ 𝓝 x, A '' (X ∩ B ∩ V) ∈ 𝓝 (A x) := by
    intro x hx V hV
    have h1 := hop x ⟨hx.1, interior_subset (hBN hx.2).1⟩ (V ∩ B)
      (Filter.inter_mem hV (hBo.mem_nhds hx.2))
    have h2 : X ∩ (V ∩ B) = X ∩ B ∩ V := by
      ext z
      simp only [Set.mem_inter_iff]
      tauto
    rwa [h2] at h1
  obtain ⟨δ, M, hδ, hδne, hcount, hgraph, hdense⟩ :=
    hcov σ X B k f d A D hBo (fun i => (hf i).mono hBN') hzero hDo hDc ⟨A w, hmaps hwB⟩ hmaps hprop hopB
  exact ⟨δ, M, hBo, hwB, hDo, hDc, hmaps, hprop, hisoB, hδ, hδne, hcount, hgraph, hdense⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
