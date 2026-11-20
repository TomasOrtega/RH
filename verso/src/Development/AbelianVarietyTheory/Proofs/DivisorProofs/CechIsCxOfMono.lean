import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAndTotalDifferentialAdditiveSquareZero

set_option autoImplicit false

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

/- English proof (translation)
Introduce `k _ ι _ E _ _ A hA n a ha`. Establish `ha' : ∀ s, a s ∈ (if s.Nonempty ∧ (s.card : ℤ) = n + 1 then A s else ⊥)` using `fun s => (Submodule.mem_pi.1 ha) s (Set.mem_univ _)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show GlobalTheory.DI.delta a ∈ cechC A (n + 1)`. Use `Submodule.mem_pi.2 fun t _ => ?_` and prove the remaining obligations.

Use `show ∑ i ∈ t, GlobalTheory.cubeSign t i • a (t.erase i) ∈ _`. Use `split_ifs with ht`. Use `Submodule.sum_mem _ fun i _ => zsmul_mem ?_ _` and prove the remaining obligations. Establish `h` using `ha' (t.erase i)`. Use `split_ifs at h with h2`.

Conclude with `hA _ _ h2.1 (Finset.erase_subset _ _) h`. Rewrite `h` using `[Submodule.mem_bot]`. Rewrite using `[h]`. Conclude with `zero_mem _`. Rewrite using `[Submodule.mem_bot]`.

Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Establish `h` using `ha' (t.erase i)`. Use `split_ifs at h with h2`. It suffices to derive a contradiction. Apply `ht` to reduce the goal to its premises.

Use `⟨⟨i, hi⟩, ?_⟩` and prove the remaining obligations. Establish `h3` using `Finset.card_erase_add_one hi`. Establish `h4` using `h2.2`. Use linear arithmetic over natural numbers and integers. Rewrite `h` using `[Submodule.mem_bot]`.

Rewrite using `[h, smul_zero]`. Conclude with `GlobalTheory.DI.delta_delta a`.
-/
theorem cech_isCx_of_mono : ∀ (k : Type) [Field k] (ι : Type) [LinearOrder ι] (E : Type) [AddCommGroup E] [Module k E]
    (A : Finset ι → Submodule k E), (∀ s t, s.Nonempty → s ⊆ t → A s ≤ A t) → (cech A).IsCx := by
  intro k _ ι _ E _ _ A hA n a ha
  have ha' : ∀ s, a s ∈ (if s.Nonempty ∧ (s.card : ℤ) = n + 1 then A s else ⊥) :=
    fun s => (Submodule.mem_pi.1 ha) s (Set.mem_univ _)
  refine ⟨?_, ?_⟩
  · show GlobalTheory.DI.delta a ∈ cechC A (n + 1)
    refine Submodule.mem_pi.2 fun t _ => ?_
    show ∑ i ∈ t, GlobalTheory.cubeSign t i • a (t.erase i) ∈ _
    split_ifs with ht
    · refine Submodule.sum_mem _ fun i _ => zsmul_mem ?_ _
      have h := ha' (t.erase i)
      split_ifs at h with h2
      · exact hA _ _ h2.1 (Finset.erase_subset _ _) h
      · rw [Submodule.mem_bot] at h; rw [h]; exact zero_mem _
    · rw [Submodule.mem_bot]
      refine Finset.sum_eq_zero fun i hi => ?_
      have h := ha' (t.erase i)
      split_ifs at h with h2
      · exfalso
        apply ht
        refine ⟨⟨i, hi⟩, ?_⟩
        have h3 := Finset.card_erase_add_one hi
        have h4 := h2.2
        omega
      · rw [Submodule.mem_bot] at h; rw [h, smul_zero]
  · exact GlobalTheory.DI.delta_delta a

end GlobalTheory.PD
