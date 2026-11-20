import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.NormOneCompact
import GroundTheory.GlobalFields.TateThesis.IdeleMeasureNormOne

open NumberField Set
open GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GroundTheory.Automorphic

namespace Reduction

variable {K : Type*} [Field K] [NumberField K]

/- English proof (translation)
Take `⟨D, hD, -, hxD⟩` from `exists_isCompact_normOneSubgroup K`. Take `⟨w₀⟩ : Nonempty (InfinitePlace K)` from `inferInstance`. Use `set I : Set {r : ℝ // 0 < r} := Subtype.val ⁻¹' Icc a b with hI`. Establish `hIc : IsCompact I`. Rewrite using `[Subtype.isCompact_iff]`.

Establish `: Subtype.val '' I = Icc a b`. Use extensionality with `r`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht, rfl⟩`. Conclude with `ht`.

Introduce `hr`. Conclude with `⟨⟨r, lt_of_lt_of_le ha hr.1⟩, hr, rfl⟩`. Rewrite using `[this]`. Conclude with `isCompact_Icc`. Use `⟨(fun p : IdeleGroup K × {r : ℝ // 0 < r} => p.1 * moduleSection w₀ p.2) '' (D ×ˢ I), (hD.prod hIc).image (continuous_fst.mul ((continuous_moduleSection w₀).comp continuous_snd)), fun s has hsb => ?_⟩` and prove the remaining obligations.

Take `⟨c, hc⟩` from `hxD _ (mul_inv_moduleSection_mem w₀ s)`. Use `⟨c, ⟨(diagonal K c * (s * (moduleSection w₀ (ideleModule K s))⁻¹), ideleModule K s), ⟨hc, has, hsb⟩, ?_⟩⟩` and prove the remaining obligations. Simplify using `only [mul_assoc, inv_mul_cancel, mul_one]`.
-/
theorem exists_isCompact_mul_mem_of_ideleModule_mem_Icc {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∃ S : Set (IdeleGroup K), IsCompact S ∧ ∀ s : IdeleGroup K,
      a ≤ (ideleModule K s : ℝ) → (ideleModule K s : ℝ) ≤ b → ∃ c : Kˣ, diagonal K c * s ∈ S := by
  obtain ⟨D, hD, -, hxD⟩ := exists_isCompact_normOneSubgroup K
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace K) := inferInstance
  set I : Set {r : ℝ // 0 < r} := Subtype.val ⁻¹' Icc a b with hI
  have hIc : IsCompact I := by
    rw [Subtype.isCompact_iff]
    have : Subtype.val '' I = Icc a b := by
      ext r
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ht
      · intro hr
        exact ⟨⟨r, lt_of_lt_of_le ha hr.1⟩, hr, rfl⟩
    rw [this]
    exact isCompact_Icc
  refine ⟨(fun p : IdeleGroup K × {r : ℝ // 0 < r} => p.1 * moduleSection w₀ p.2) '' (D ×ˢ I),
    (hD.prod hIc).image (continuous_fst.mul ((continuous_moduleSection w₀).comp continuous_snd)),
    fun s has hsb => ?_⟩
  obtain ⟨c, hc⟩ := hxD _ (mul_inv_moduleSection_mem w₀ s)
  refine ⟨c, ⟨(diagonal K c * (s * (moduleSection w₀ (ideleModule K s))⁻¹), ideleModule K s),
    ⟨hc, has, hsb⟩, ?_⟩⟩
  simp only [mul_assoc, inv_mul_cancel, mul_one]

end Reduction

end GroundTheory.Automorphic
