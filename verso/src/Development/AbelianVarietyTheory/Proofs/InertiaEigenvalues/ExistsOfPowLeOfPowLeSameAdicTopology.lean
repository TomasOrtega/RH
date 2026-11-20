import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicCompleteOfPowLeOfPowLe
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Introduce `S A _ _ s I ι TB I' n m _ _ _ h1 h2`. Establish `hk : ∀ k : ℕ, I ^ (n * k) ≤ I' ^ k` using `fun k => by`. Rewrite using `[pow_mul]`. Conclude with `Ideal.pow_right_mono h1 k`. Use `⟨{ TB with fin := ?_, approx := ?_, complete := ?_ }, rfl, rfl⟩` and prove the remaining obligations.

Introduce `x k`. Conclude with `(TB.fin x (n * k)).subset fun i hi h => hi (hk k h)`. Introduce `x k F hF set G : Finset ι := F ∪ (TB.fin x (n * k)).toFinset with hG`. Establish `hG' : ∀ i, i ∉ G → TB.c i x ∈ I ^ (n * k)`. Introduce `i hi`.

Assume the negation of the conclusion as `h`. Conclude with `hi (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h))`. Establish `hmain` using `TB.approx x (n * k) G hG'`. Establish `hmap : (I ^ (n * k)).map s ≤ (I' ^ k).map s` using `Ideal.map_mono (hk k)`. Establish `hsplit : ∑ i ∈ G, s (TB.c i x) * TB.b i = ∑ i ∈ F, s (TB.c i x) * TB.b i + ∑ i ∈ G \ F, s (TB.c i x) * TB.b i`.

Rewrite using `[add_comm, Finset.sum_sdiff (Finset.subset_union_left)]`. Establish `hrest : ∑ i ∈ G \ F, s (TB.c i x) * TB.b i ∈ (I' ^ k).map s`. Use `Ideal.sum_mem _ fun i hi => ?_` and prove the remaining obligations. Establish `: i ∉ F` using `(Finset.mem_sdiff.1 hi).2`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem s (hF i this))`.

Establish `: x - ∑ i ∈ F, s (TB.c i x) * TB.b i = (x - ∑ i ∈ G, s (TB.c i x) * TB.b i) + ∑ i ∈ G \ F, s (TB.c i x) * TB.b i`. Rewrite using `[hsplit]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `add_mem (hmap hmain) hrest`.

Use `GlobalTheory.isAdicComplete_of_pow_le_of_pow_le A (I.map s) (I'.map s) n m ?_ ?_ TB.complete` and prove the remaining obligations. Rewrite using `[← Ideal.map_pow]`. Conclude with `Ideal.map_mono h1`. Rewrite using `[← Ideal.map_pow]`. Conclude with `Ideal.map_mono h2`.
-/
theorem TopBasis.exists_of_pow_le_of_pow_le :
    ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (ι : Type) (TB : TopBasis s I ι)
      (I' : Ideal S) (n m : ℕ), IsHausdorff I S → 0 < n → 0 < m → I ^ n ≤ I' → I' ^ m ≤ I →
      ∃ TB' : TopBasis s I' ι, TB'.b = TB.b ∧ TB'.c = TB.c := by
  intro S A _ _ s I ι TB I' n m _ _ _ h1 h2
  have hk : ∀ k : ℕ, I ^ (n * k) ≤ I' ^ k := fun k => by
    rw [pow_mul]; exact Ideal.pow_right_mono h1 k
  classical
  refine ⟨{ TB with fin := ?_, approx := ?_, complete := ?_ }, rfl, rfl⟩
  · intro x k
    exact (TB.fin x (n * k)).subset fun i hi h => hi (hk k h)
  · intro x k F hF
    set G : Finset ι := F ∪ (TB.fin x (n * k)).toFinset with hG
    have hG' : ∀ i, i ∉ G → TB.c i x ∈ I ^ (n * k) := by
      intro i hi
      by_contra h
      exact hi (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h))
    have hmain := TB.approx x (n * k) G hG'
    have hmap : (I ^ (n * k)).map s ≤ (I' ^ k).map s := Ideal.map_mono (hk k)
    have hsplit : ∑ i ∈ G, s (TB.c i x) * TB.b i =
        ∑ i ∈ F, s (TB.c i x) * TB.b i + ∑ i ∈ G \ F, s (TB.c i x) * TB.b i := by
      rw [add_comm, Finset.sum_sdiff (Finset.subset_union_left)]
    have hrest : ∑ i ∈ G \ F, s (TB.c i x) * TB.b i ∈ (I' ^ k).map s := by
      refine Ideal.sum_mem _ fun i hi => ?_
      have : i ∉ F := (Finset.mem_sdiff.1 hi).2
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem s (hF i this))
    have : x - ∑ i ∈ F, s (TB.c i x) * TB.b i =
        (x - ∑ i ∈ G, s (TB.c i x) * TB.b i) + ∑ i ∈ G \ F, s (TB.c i x) * TB.b i := by
      rw [hsplit]; ring
    rw [this]
    exact add_mem (hmap hmain) hrest
  · refine GlobalTheory.isAdicComplete_of_pow_le_of_pow_le A (I.map s) (I'.map s) n m ?_ ?_ TB.complete
    · rw [← Ideal.map_pow]; exact Ideal.map_mono h1
    · rw [← Ideal.map_pow]; exact Ideal.map_mono h2

end GlobalTheory.BSP
