import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SubClosed

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCxMap

/- English proof (translation)
Establish `key : (bd W).comp (Finsupp.lmapDomain ℤ ℤ (List.map e)) = (Finsupp.lmapDomain ℤ ℤ (List.map e)).comp (bd V)`. Apply `Finsupp.lhom_ext` to reduce the goal to its premises. Introduce `l n`. Simplify using `[bd, Finsupp.linearCombination_single, Finsupp.mapDomain_single, Finset.smul_sum, Finsupp.mapDomain_finset_sum, Finsupp.mapDomain_smul, List.eraseIdx_map, ← Finsupp.single_mul]`. Conclude with `LinearMap.congr_fun key c`.
-/
theorem bd_mapDomain {V W : Type} (e : V → W) (c : List V →₀ ℤ) :
    bd W (Finsupp.lmapDomain ℤ ℤ (List.map e) c) = Finsupp.lmapDomain ℤ ℤ (List.map e) (bd V c) := by
  have key : (bd W).comp (Finsupp.lmapDomain ℤ ℤ (List.map e)) =
      (Finsupp.lmapDomain ℤ ℤ (List.map e)).comp (bd V) := by
    apply Finsupp.lhom_ext
    intro l n
    simp [bd, Finsupp.linearCombination_single, Finsupp.mapDomain_single, Finset.smul_sum,
      Finsupp.mapDomain_finset_sum, Finsupp.mapDomain_smul, List.eraseIdx_map,
      ← Finsupp.single_mul]
  exact LinearMap.congr_fun key c

/- English proof (translation)
Unfold `chains`. Rewrite using `[Finsupp.lmapDomain_supported]`. Use `congr 1`. Use extensionality with `l`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨l', hl', rfl⟩, hlen⟩`. Conclude with `⟨l', ⟨hl', by simpa using hlen⟩, rfl⟩`. Introduce and unpack `⟨l', ⟨hl', hlen⟩, rfl⟩`. Conclude with `⟨⟨l', hl', rfl⟩, by simpa using hlen⟩`.
-/
theorem chains_map {V W : Type} (e : V → W) (F : Set (List V)) (q : ℕ) :
    chains (List.map e '' F) q = (chains F q).map (Finsupp.lmapDomain ℤ ℤ (List.map e)) := by
  unfold chains
  rw [Finsupp.lmapDomain_supported]
  congr 1
  ext l
  constructor
  · rintro ⟨⟨l', hl', rfl⟩, hlen⟩
    exact ⟨l', ⟨hl', by simpa using hlen⟩, rfl⟩
  · rintro ⟨l', ⟨hl', hlen⟩, rfl⟩
    exact ⟨⟨l', hl', rfl⟩, by simpa using hlen⟩

end GlobalTheory.SeqCxMap

section
open GlobalTheory.SeqCx Matrix
/- English proof (translation)
Introduce `V W e he F p`. Establish `hinj : Function.Injective (Finsupp.lmapDomain ℤ ℤ (List.map e))`. Introduce `x y hxy`. Conclude with `Finsupp.mapDomain_injective (List.map_injective_iff.mpr he) hxy`. Unfold `GlobalTheory.SeqCx.ExactAt`.

Prove the components needed by the constructor for the conclusion. Introduce `h c hc hbc`. Take `⟨b, hb, hbb⟩` from `h (Finsupp.lmapDomain ℤ ℤ (List.map e) c) (by rw [GlobalTheory.SeqCxMap.chains_map]; exact Submodule.mem_map_of_mem hc) (by rw [GlobalTheory.SeqCxMap.bd_mapDomain, hbc, map_zero])`. Rewrite `hb` using `[GlobalTheory.SeqCxMap.chains_map]`. Take `⟨b', hb', rfl⟩` from `hb`.

Conclude with `⟨b', hb', hinj (by rw [← GlobalTheory.SeqCxMap.bd_mapDomain]; exact hbb)⟩`. Introduce `h c hc hbc`. Rewrite `hc` using `[GlobalTheory.SeqCxMap.chains_map]`. Take `⟨c', hc', rfl⟩` from `hc`. Take `⟨b', hb', hbb⟩` from `h c' hc' (hinj (by rw [← GlobalTheory.SeqCxMap.bd_mapDomain, hbc, map_zero]))`.

Use `⟨Finsupp.lmapDomain ℤ ℤ (List.map e) b', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.SeqCxMap.chains_map]`. Conclude with `Submodule.mem_map_of_mem hb'`. Rewrite using `[GlobalTheory.SeqCxMap.bd_mapDomain, hbb]`.
-/
theorem _root_.GlobalTheory.T.seqChain_exactAt_map_iff : ∀ (V W : Type) (e : V → W), Function.Injective e → ∀ (F : Set (List V)) (p : ℕ), ExactAt (List.map e '' F) p ↔ ExactAt F p := by
  intro V W e he F p
  have hinj : Function.Injective (Finsupp.lmapDomain ℤ ℤ (List.map e)) := by
    intro x y hxy
    exact Finsupp.mapDomain_injective (List.map_injective_iff.mpr he) hxy
  unfold GlobalTheory.SeqCx.ExactAt
  constructor
  · intro h c hc hbc
    obtain ⟨b, hb, hbb⟩ := h (Finsupp.lmapDomain ℤ ℤ (List.map e) c)
      (by rw [GlobalTheory.SeqCxMap.chains_map]; exact Submodule.mem_map_of_mem hc)
      (by rw [GlobalTheory.SeqCxMap.bd_mapDomain, hbc, map_zero])
    rw [GlobalTheory.SeqCxMap.chains_map] at hb
    obtain ⟨b', hb', rfl⟩ := hb
    exact ⟨b', hb', hinj (by rw [← GlobalTheory.SeqCxMap.bd_mapDomain]; exact hbb)⟩
  · intro h c hc hbc
    rw [GlobalTheory.SeqCxMap.chains_map] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    obtain ⟨b', hb', hbb⟩ := h c' hc'
      (hinj (by rw [← GlobalTheory.SeqCxMap.bd_mapDomain, hbc, map_zero]))
    refine ⟨Finsupp.lmapDomain ℤ ℤ (List.map e) b', ?_, ?_⟩
    · rw [GlobalTheory.SeqCxMap.chains_map]; exact Submodule.mem_map_of_mem hb'
    · rw [GlobalTheory.SeqCxMap.bd_mapDomain, hbb]
end
