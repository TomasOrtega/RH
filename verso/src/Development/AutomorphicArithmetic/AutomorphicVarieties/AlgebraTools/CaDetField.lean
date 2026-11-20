import Mathlib

open IsLocalRing

/- English proof (translation)
Take `⟨c, -, hc⟩` from `Finset.exists_max_image Finset.univ (fun j => V.valuation (w j)) Finset.univ_nonempty`. Establish `hwc : w c ≠ 0`. Introduce `h0`. Apply `hw` to reduce the goal to its premises. Use function extensionality and compare the values at `j`.

Establish `hj` using `hc j (Finset.mem_univ j)`. Rewrite `hj` using `[h0, map_zero]`. Conclude with `(Valuation.zero_iff _).mp (le_antisymm hj zero_le')`. Use `⟨c, hwc, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[← V.valuation_le_one_iff, map_div₀]`.

Conclude with `div_le_one_of_le₀ (hc j (Finset.mem_univ j)) zero_le'`.
-/
private theorem UpperTheory.V.AlgebraTools.exists_div_mem_valuationSubring_of_ne_zero {K : Type} [Field K] (V : ValuationSubring K)
    {ι : Type} [Fintype ι] [Nonempty ι] (w : ι → K) (hw : w ≠ 0) :
    ∃ c, w c ≠ 0 ∧ ∀ j, w j / w c ∈ V := by
  obtain ⟨c, -, hc⟩ := Finset.exists_max_image Finset.univ (fun j => V.valuation (w j))
    Finset.univ_nonempty
  have hwc : w c ≠ 0 := by
    intro h0
    apply hw
    funext j
    have hj := hc j (Finset.mem_univ j)
    rw [h0, map_zero] at hj
    exact (Valuation.zero_iff _).mp (le_antisymm hj zero_le')
  refine ⟨c, hwc, fun j => ?_⟩
  rw [← V.valuation_le_one_iff, map_div₀]
  exact div_le_one_of_le₀ (hc j (Finset.mem_univ j)) zero_le'

/- English proof (translation)
Introduce `K _ V ι _ _ _ z m hm hdet`. Establish `key : ∀ w : ι → K, z.mulVec w = 0 → ∀ c, w c ≠ 0 → z.mulVec (fun j => w j / w c) = 0`. Introduce `w hw c _`. Establish `e : (fun j => w j / w c) = (w c)⁻¹ • w`. Use function extensionality and compare the values at `j`.

Simplify using `[div_eq_inv_mul]`. Rewrite using `[e, Matrix.mulVec_smul, hw, smul_zero]`. Distinguish the cases in `h0 : m = 0`. Take `⟨w, hw, hzw⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hdet`. Take `⟨c, hc, hV⟩` from `UpperTheory.V.AlgebraTools.exists_div_mem_valuationSubring_of_ne_zero V w hw`.

Conclude with `⟨c, fun j => w j / w c, div_self hc, hV, key w hzw c hc, fun j => by simp [h0]⟩`. Take `⟨c, hc, hV⟩` from `UpperTheory.V.AlgebraTools.exists_div_mem_valuationSubring_of_ne_zero V m h0`. Conclude with `⟨c, fun j => m j / m c, div_self hc, hV, key m hm c hc, fun j => (div_mul_cancel₀ _ hc).symm⟩`.
-/
theorem UpperTheory.V.AlgebraTools.exists_kernel_vector :
    ∀ (K : Type) [Field K] (V : ValuationSubring K) (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι]
      (z : Matrix ι ι K) (m : ι → K), z.mulVec m = 0 → z.det = 0 →
      ∃ (c : ι) (l : ι → K), l c = 1 ∧ (∀ j, l j ∈ V) ∧ z.mulVec l = 0 ∧ ∀ j, m j = l j * m c := by
  intro K _ V ι _ _ _ z m hm hdet
  have key : ∀ w : ι → K, z.mulVec w = 0 → ∀ c, w c ≠ 0 →
      z.mulVec (fun j => w j / w c) = 0 := by
    intro w hw c _
    have e : (fun j => w j / w c) = (w c)⁻¹ • w := by
      funext j
      simp [div_eq_inv_mul]
    rw [e, Matrix.mulVec_smul, hw, smul_zero]
  by_cases h0 : m = 0
  · obtain ⟨w, hw, hzw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    obtain ⟨c, hc, hV⟩ := UpperTheory.V.AlgebraTools.exists_div_mem_valuationSubring_of_ne_zero V w hw
    exact ⟨c, fun j => w j / w c, div_self hc, hV, key w hzw c hc, fun j => by simp [h0]⟩
  · obtain ⟨c, hc, hV⟩ := UpperTheory.V.AlgebraTools.exists_div_mem_valuationSubring_of_ne_zero V m h0
    exact ⟨c, fun j => m j / m c, div_self hc, hV, key m hm c hc,
      fun j => (div_mul_cancel₀ _ hc).symm⟩
