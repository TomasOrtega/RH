import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteGermProjectionCover
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermProjectionOpenNear
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProperOpenProjectionCover
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Supply the required witnesses or components. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. The claim follows by propositional logic. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Extract witnesses or component facts from the available result. Supply the required witnesses or components.
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
