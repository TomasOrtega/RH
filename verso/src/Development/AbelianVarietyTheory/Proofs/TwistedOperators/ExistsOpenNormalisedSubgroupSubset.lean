import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockTriangularOneAddMat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
open scoped ENNReal

namespace GlobalTheory.SmGL

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Assume the hypotheses and unpack their components.

Assume the hypotheses and unpack their components. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem exists_open_normalised_subgroup_subset (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] :
    ∀ U ∈ 𝓝 (1 : GL n k), ∃ J : Subgroup (GL n k), IsOpen (J : Set (GL n k)) ∧
      (J : Set (GL n k)) ⊆ U ∧ J ≤ KO k n ∧ ∀ x ∈ KO k n, ∀ j ∈ J, x * j * x⁻¹ ∈ J := by
  intro U hU
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨SplitWeil.cball s, SplitWeil.add_mem_cball⟩, by simp [SplitWeil.cball]⟩,
      SplitWeil.neg_mem_cball⟩, SplitWeil.isOpen_cball s⟩, hs⟩⟩
  have : TotallyDisconnectedSpace k := inferInstance
  have : TotallyDisconnectedSpace (Matrix n n k) :=
    inferInstanceAs (TotallyDisconnectedSpace (n → n → k))
  have : TotallyDisconnectedSpace (GL n k) :=
    ⟨(SplitFlip.isEmbedding_val_GL (k := k) (n := n)).isTotallyDisconnected
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  have : CompactSpace (KO k n) :=
    isCompact_iff_compactSpace.1 (SplitFlip.isCompact_KO (k := k) (n := n))
  have hV : IsOpen ((fun x : KO k n => (x : GL n k)) ⁻¹' interior U) :=
    isOpen_interior.preimage continuous_subtype_val
  have h1 : (1 : KO k n) ∈ (fun x : KO k n => (x : GL n k)) ⁻¹' interior U :=
    mem_interior_iff_mem_nhds.2 hU
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hV h1
  refine ⟨H.toSubgroup.map (KO k n).subtype, ?_, ?_, ?_, ?_⟩
  · exact (SplitFlip.isOpen_KO (k := k) (n := n)).isOpenMap_subtype_val _ H.isOpen
  · rintro _ ⟨y, hy, rfl⟩
    exact interior_subset (hH hy)
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · rintro x hx _ ⟨y, hy, rfl⟩
    have hc : (⟨x, hx⟩ : KO k n) * y * (⟨x, hx⟩ : KO k n)⁻¹ ∈ H.toSubgroup :=
      H.isNormal'.conj_mem y hy (⟨x, hx⟩ : KO k n)
    exact Subgroup.mem_map_of_mem (KO k n).subtype hc

end GlobalTheory.SmGL
