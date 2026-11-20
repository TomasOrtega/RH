import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.MemSplitSeqIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KAcyclicHomology
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SeqChainBoundaryCompBoundaryApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SplitSetPermRepChainsIsoSplitSeqChains

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL

namespace GlobalTheory.HomStab.SplitEx

/- English proof (translation)
Introduce `R _ n`. Establish `key` using `T.splitSet_permRep_chains_iso_splitSeq_chains R n`. Establish `hzero : ∀ p (x : SplitSet R n (p + 1 + 1) →₀ ℤ), (splitD R n p).hom ((splitD R n (p + 1)).hom x) = 0`. Introduce `p x`. Apply `(key p).1` to reduce the goal to its premises.

Establish `h1` using `(key p).2.2 ((splitD R n (p + 1)).hom x)`. Establish `h2` using `(key (p + 1)).2.2 x`. Rewrite `h1` using `[h2, T.seqChain_boundary_comp_boundary_apply]`. Conclude with `h1.trans (Finsupp.mapDomain_zero (f := (Subtype.val : SplitSet R n p → List ((Fin n → R) × (Fin n → R)))) (M := ℤ)).symm`. Use `⟨fun p => ?_, fun h0 => ?_, fun p hp => ?_⟩` and prove the remaining obligations.

Use extensionality with `c a`. Simplify using `[hzero]`. Introduce `(y : SplitSet R n 0 →₀ ℤ)`. Establish `hy : Finsupp.mapDomain (Subtype.val : SplitSet R n 0 → List ((Fin n → R) × (Fin n → R))) y ∈ chains (splitSeq R n) 0`. Rewrite using `[← (key 0).2.1]`.

Conclude with `LinearMap.mem_range.mpr ⟨y, rfl⟩`. Establish `hbd : bd _ (Finsupp.mapDomain (Subtype.val : SplitSet R n 0 → List ((Fin n → R) × (Fin n → R))) y) = 0`. Establish `hsup : ↑(Finsupp.mapDomain (Subtype.val : SplitSet R n 0 → List ((Fin n → R) × (Fin n → R))) y).support ⊆ {l | l ∈ splitSeq R n ∧ l.length = 0}` using `(Finsupp.mem_supported ℤ _).mp hy`. Rewrite using `[bd, Finsupp.linearCombination_apply, Finsupp.sum]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `l hl`. Establish `hlen : l.length = 0` using `(hsup hl).2`. Simplify using `[hlen]`. Take `⟨b, hb, hbeq⟩` from `h0 _ hy hbd`. Establish `hb' : b ∈ LinearMap.range (Finsupp.lmapDomain ℤ ℤ (Subtype.val : SplitSet R n 1 → List ((Fin n → R) × (Fin n → R))))`.

Rewrite using `[(key 1).2.1]`. Conclude with `hb`. Take `⟨x, rfl⟩` from `LinearMap.mem_range.mp hb'`. Use `⟨x, (key 0).1 ?_⟩` and prove the remaining obligations. Conclude with `((key 0).2.2 x).trans hbeq`.

Introduce `(y : SplitSet R n (p + 1) →₀ ℤ)`. Prove the components needed by the constructor for the conclusion. Introduce `hy0`. Establish `hy : Finsupp.mapDomain (Subtype.val : SplitSet R n (p + 1) → List ((Fin n → R) × (Fin n → R))) y ∈ chains (splitSeq R n) (p + 1)`. Rewrite using `[← (key (p + 1)).2.1]`.

Conclude with `LinearMap.mem_range.mpr ⟨y, rfl⟩`. Establish `hbd : bd _ (Finsupp.mapDomain (Subtype.val : SplitSet R n (p + 1) → List ((Fin n → R) × (Fin n → R))) y) = 0`. Establish `h1` using `(key p).2.2 y`. Rewrite `h1` using `[hy0]`. Conclude with `h1.symm.trans Finsupp.mapDomain_zero`.

Take `⟨b, hb, hbeq⟩` from `hp _ hy hbd`. Establish `hb' : b ∈ LinearMap.range (Finsupp.lmapDomain ℤ ℤ (Subtype.val : SplitSet R n (p + 1 + 1) → List ((Fin n → R) × (Fin n → R))))`. Rewrite using `[(key (p + 1 + 1)).2.1]`. Conclude with `hb`. Take `⟨x, rfl⟩` from `LinearMap.mem_range.mp hb'`.

Use `⟨x, (key (p + 1)).1 ?_⟩` and prove the remaining obligations. Conclude with `((key (p + 1)).2.2 x).trans hbeq`. Introduce and unpack `⟨x, rfl⟩`. Conclude with `hzero p x`.
-/
theorem main : ∀ (R : Type) [CommRing R] (n : ℕ), (∀ p, splitD R n (p + 1) ≫ splitD R n p = 0) ∧
    (ExactAt (splitSeq R n) 0 → Function.Surjective (splitD R n 0).hom) ∧
    ∀ p, ExactAt (splitSeq R n) (p + 1) → Function.Exact (splitD R n (p + 1)).hom (splitD R n p).hom := by
  intro R _ n
  have key := T.splitSet_permRep_chains_iso_splitSeq_chains R n
  have hzero : ∀ p (x : SplitSet R n (p + 1 + 1) →₀ ℤ),
      (splitD R n p).hom ((splitD R n (p + 1)).hom x) = 0 := by
    intro p x
    apply (key p).1
    have h1 := (key p).2.2 ((splitD R n (p + 1)).hom x)
    have h2 := (key (p + 1)).2.2 x
    rw [h2, T.seqChain_boundary_comp_boundary_apply] at h1
    exact h1.trans (Finsupp.mapDomain_zero
      (f := (Subtype.val : SplitSet R n p → List ((Fin n → R) × (Fin n → R)))) (M := ℤ)).symm
  refine ⟨fun p => ?_, fun h0 => ?_, fun p hp => ?_⟩
  · ext c a
    simp [hzero]
  · intro (y : SplitSet R n 0 →₀ ℤ)
    have hy : Finsupp.mapDomain (Subtype.val : SplitSet R n 0 → List ((Fin n → R) × (Fin n → R))) y
        ∈ chains (splitSeq R n) 0 := by
      rw [← (key 0).2.1]
      exact LinearMap.mem_range.mpr ⟨y, rfl⟩
    have hbd : bd _ (Finsupp.mapDomain (Subtype.val : SplitSet R n 0 → List ((Fin n → R) × (Fin n → R))) y) = 0 := by
      have hsup : ↑(Finsupp.mapDomain (Subtype.val : SplitSet R n 0 → List ((Fin n → R) × (Fin n → R))) y).support
          ⊆ {l | l ∈ splitSeq R n ∧ l.length = 0} := (Finsupp.mem_supported ℤ _).mp hy
      rw [bd, Finsupp.linearCombination_apply, Finsupp.sum]
      apply Finset.sum_eq_zero
      intro l hl
      have hlen : l.length = 0 := (hsup hl).2
      simp [hlen]
    obtain ⟨b, hb, hbeq⟩ := h0 _ hy hbd
    have hb' : b ∈ LinearMap.range
        (Finsupp.lmapDomain ℤ ℤ (Subtype.val : SplitSet R n 1 → List ((Fin n → R) × (Fin n → R)))) := by
      rw [(key 1).2.1]
      exact hb
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hb'
    refine ⟨x, (key 0).1 ?_⟩
    exact ((key 0).2.2 x).trans hbeq
  · intro (y : SplitSet R n (p + 1) →₀ ℤ)
    constructor
    · intro hy0
      have hy : Finsupp.mapDomain (Subtype.val : SplitSet R n (p + 1) → List ((Fin n → R) × (Fin n → R))) y
          ∈ chains (splitSeq R n) (p + 1) := by
        rw [← (key (p + 1)).2.1]
        exact LinearMap.mem_range.mpr ⟨y, rfl⟩
      have hbd : bd _ (Finsupp.mapDomain (Subtype.val : SplitSet R n (p + 1) → List ((Fin n → R) × (Fin n → R))) y) = 0 := by
        have h1 := (key p).2.2 y
        rw [hy0] at h1
        exact h1.symm.trans Finsupp.mapDomain_zero
      obtain ⟨b, hb, hbeq⟩ := hp _ hy hbd
      have hb' : b ∈ LinearMap.range
          (Finsupp.lmapDomain ℤ ℤ (Subtype.val : SplitSet R n (p + 1 + 1) → List ((Fin n → R) × (Fin n → R)))) := by
        rw [(key (p + 1 + 1)).2.1]
        exact hb
      obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hb'
      refine ⟨x, (key (p + 1)).1 ?_⟩
      exact ((key (p + 1)).2.2 x).trans hbeq
    · rintro ⟨x, rfl⟩
      exact hzero p x

end GlobalTheory.HomStab.SplitEx

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.HomStab.SplitEx.main`.
-/
theorem _root_.GlobalTheory.T.splitSequence_rep_complex_exact : ∀ (R : Type) [CommRing R] (n : ℕ), (∀ p, splitD R n (p + 1) ≫ splitD R n p = 0) ∧ (ExactAt (splitSeq R n) 0 → Function.Surjective (splitD R n 0).hom) ∧ ∀ p, ExactAt (splitSeq R n) (p + 1) → Function.Exact (splitD R n (p + 1)).hom (splitD R n p).hom := by
  first
  | exact @GlobalTheory.HomStab.SplitEx.main
end
