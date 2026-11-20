import Mathlib
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Take `⟨q, rfl⟩` from `h x`. Take `⟨b, hb, hq⟩` from `IsLocalization.integerNormalization_spec (nonZeroDivisors O) q`. Use `⟨b, nonZeroDivisors.ne_zero hb, IsLocalization.integerNormalization (nonZeroDivisors O) q, ?_⟩` and prove the remaining obligations. Rewrite using `[← aeval_map_algebraMap E, hq, ← algebraMap_smul E b q, map_smul, algebraMap_smul]`.
-/
theorem exists_denominator_aeval_elem (O E A : Type) [CommRing O] [IsDomain O] [Field E] [Algebra O E]
    [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] (g : A)
    (h : ∀ x : A, ∃ p : E[X], aeval g p = x) (x : A) :
    ∃ c : O, c ≠ 0 ∧ ∃ p : O[X], aeval g p = c • x := by
  obtain ⟨q, rfl⟩ := h x
  obtain ⟨b, hb, hq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors O) q
  refine ⟨b, nonZeroDivisors.ne_zero hb, IsLocalization.integerNormalization (nonZeroDivisors O) q, ?_⟩
  rw [← aeval_map_algebraMap E, hq, ← algebraMap_smul E b q, map_smul, algebraMap_smul]

/- English proof (translation)
Take `⟨s, rfl⟩` from `hS`. Establish `key : ∃ c : O, c ≠ 0 ∧ ∀ x ∈ s, ∃ p : O[X], aeval g p = c • x`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `insert a s _ ih`.

Take `⟨c, hc, hs⟩` from `ih`. Take `⟨d, hd, p, hp⟩` from `exists_denominator_aeval_elem O E A g h a`. Use `⟨c * d, mul_ne_zero hc hd, fun x hx => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hx with rfl | hx` into its components or cases. Conclude with `⟨c • p, by rw [map_smul, hp, mul_smul]⟩`.

Take `⟨q, hq⟩` from `hs x hx`. Conclude with `⟨d • q, by rw [map_smul, hq, mul_comm, mul_smul]⟩`. Take `⟨c, hc, hs⟩` from `key`. Use `⟨c, hc, fun x hx => ?_⟩` and prove the remaining obligations. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx => exact hs x hx`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨p, hp⟩` from `hx`. Take `⟨q, hq⟩` from `hy`.

Conclude with `⟨p + q, by rw [map_add, hp, hq, smul_add]⟩`. Consider the case `smul a x _ hx`. Take `⟨p, hp⟩` from `hx`. Conclude with `⟨a • p, by rw [map_smul, hp, smul_comm]⟩`.
-/
theorem exists_common_denominator_aeval_of_fg (O E A : Type) [CommRing O] [IsDomain O] [Field E]
    [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A]
    [IsScalarTower O E A] (g : A) (h : ∀ x : A, ∃ p : E[X], aeval g p = x)
    (S : Submodule O A) (hS : S.FG) :
    ∃ c : O, c ≠ 0 ∧ ∀ x ∈ S, ∃ p : O[X], aeval g p = c • x := by
  classical
  obtain ⟨s, rfl⟩ := hS
  have key : ∃ c : O, c ≠ 0 ∧ ∀ x ∈ s, ∃ p : O[X], aeval g p = c • x := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_ne_zero, by simp⟩
    | insert a s _ ih =>
      obtain ⟨c, hc, hs⟩ := ih
      obtain ⟨d, hd, p, hp⟩ := exists_denominator_aeval_elem O E A g h a
      refine ⟨c * d, mul_ne_zero hc hd, fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact ⟨c • p, by rw [map_smul, hp, mul_smul]⟩
      · obtain ⟨q, hq⟩ := hs x hx
        exact ⟨d • q, by rw [map_smul, hq, mul_comm, mul_smul]⟩
  obtain ⟨c, hc, hs⟩ := key
  refine ⟨c, hc, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨p, hp⟩ := hx
    obtain ⟨q, hq⟩ := hy
    exact ⟨p + q, by rw [map_add, hp, hq, smul_add]⟩
  | smul a x _ hx =>
    obtain ⟨p, hp⟩ := hx
    exact ⟨a • p, by rw [map_smul, hp, smul_comm]⟩

end GlobalTheory
