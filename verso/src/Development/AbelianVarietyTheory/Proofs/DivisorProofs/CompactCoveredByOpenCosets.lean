import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmAOneApply
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory

open scoped Pointwise

/- English proof (translation)
Introduce `G _ _ _ K hK C hC`. Take `⟨t, ht⟩` from `hC.elim_finite_subcover (fun g : G => g • (K : Set G)) (fun g => hK.smul g) (fun x _ => Set.mem_iUnion.2 ⟨x, Set.mem_smul_set.2 ⟨1, K.one_mem, by simp⟩⟩)`. Use `⟨(t.image (fun g => (QuotientGroup.mk g : G ⧸ K))).image Quotient.out, ?_, ?_⟩` and prove the remaining obligations. Introduce `r hr r' hr' hrr'`. Simplify using `only [Finset.mem_image] at hr hr'`.

Take `⟨a, -, rfl⟩` from `hr`. Take `⟨b, -, rfl⟩` from `hr'`. Establish `h : (QuotientGroup.mk (Quotient.out a) : G ⧸ K) = QuotientGroup.mk (Quotient.out b)` using `QuotientGroup.eq.2 hrr'`. Rewrite `h` using `[QuotientGroup.out_eq', QuotientGroup.out_eq']`. Rewrite using `[h]`.

Introduce `g hg`. Establish `hm` using `ht hg`. Simplify using `only [Set.mem_iUnion] at hm`. Take `⟨gi, hgi, hmem⟩` from `hm`. Take `⟨k, hk, rfl⟩` from `Set.mem_smul_set.1 hmem`.

Use `⟨Quotient.out (QuotientGroup.mk gi : G ⧸ K), Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hgi), ?_⟩` and prove the remaining obligations. Establish `h1 : (Quotient.out (QuotientGroup.mk gi : G ⧸ K))⁻¹ * gi ∈ K` using `QuotientGroup.eq.1 (QuotientGroup.out_eq' _)`. Simplify `K.mul_mem h1 hk` using `[smul_eq_mul, mul_assoc]`.
-/
theorem compact_finite_leftCoset_reps : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) →
    ∀ C : Set G, IsCompact C →
    ∃ R : Finset G, (∀ r ∈ R, ∀ r' ∈ R, r⁻¹ * r' ∈ K → r = r') ∧ ∀ g ∈ C, ∃ r ∈ R, r⁻¹ * g ∈ K := by
  intro G _ _ _ K hK C hC
  classical
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun g : G => g • (K : Set G)) (fun g => hK.smul g)
    (fun x _ => Set.mem_iUnion.2 ⟨x, Set.mem_smul_set.2 ⟨1, K.one_mem, by simp⟩⟩)
  refine ⟨(t.image (fun g => (QuotientGroup.mk g : G ⧸ K))).image Quotient.out, ?_, ?_⟩
  · intro r hr r' hr' hrr'
    simp only [Finset.mem_image] at hr hr'
    obtain ⟨a, -, rfl⟩ := hr
    obtain ⟨b, -, rfl⟩ := hr'
    have h : (QuotientGroup.mk (Quotient.out a) : G ⧸ K) = QuotientGroup.mk (Quotient.out b) :=
      QuotientGroup.eq.2 hrr'
    rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h
    rw [h]
  · intro g hg
    have hm := ht hg
    simp only [Set.mem_iUnion] at hm
    obtain ⟨gi, hgi, hmem⟩ := hm
    obtain ⟨k, hk, rfl⟩ := Set.mem_smul_set.1 hmem
    refine ⟨Quotient.out (QuotientGroup.mk gi : G ⧸ K),
      Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hgi), ?_⟩
    have h1 : (Quotient.out (QuotientGroup.mk gi : G ⧸ K))⁻¹ * gi ∈ K :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    simpa [smul_eq_mul, mul_assoc] using K.mul_mem h1 hk

end GlobalTheory
