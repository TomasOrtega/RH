import Mathlib

open NumberField

namespace GlobalTheory.IntegralMultipleOfVectors

/- English proof (translation)
Establish `h : IsAlgebraic ℤ a` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic a)`. Take `⟨y, hy, hi⟩` from `h.exists_integral_multiple`. Establish `hi' : IsIntegral ℤ ((y.natAbs : E) * a)`. Break down `Int.natAbs_eq y with h1 | h1` into its components or cases. Establish `: (y.natAbs : E) * a = y • a` using `by conv_rhs => rw [h1]`.

Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `hi`. Establish `: (y.natAbs : E) * a = -(y • a)` using `by conv_rhs => rw [h1]`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Conclude with `hi.neg`. Conclude with `⟨y.natAbs, ⟨_, hi'⟩, Int.natAbs_pos.mpr hy, rfl⟩`.
-/
theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ (e : ℕ) (b : RingOfIntegers E), 0 < e ∧ (e : E) * a = algebraMap (RingOfIntegers E) E b := by
  have h : IsAlgebraic ℤ a :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨y, hy, hi⟩ := h.exists_integral_multiple
  have hi' : IsIntegral ℤ ((y.natAbs : E) * a) := by
    rcases Int.natAbs_eq y with h1 | h1
    · have : (y.natAbs : E) * a = y • a := by
        conv_rhs => rw [h1]
        simp
      rw [this]; exact hi
    · have : (y.natAbs : E) * a = -(y • a) := by
        conv_rhs => rw [h1]
        simp
      rw [this]; exact hi.neg
  exact ⟨y.natAbs, ⟨_, hi'⟩, Int.natAbs_pos.mpr hy, rfl⟩

/- English proof (translation)
Establish `hw : w ∈ Submodule.span E (L : Set (Fin n → E))` using `hL ▸ Submodule.mem_top`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_pos, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_pos, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨d, hd, hx⟩` from `hx`. Take `⟨e, he, hy⟩` from `hy`. Use `⟨d * e, Nat.mul_pos hd he, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `L.add_mem ?_ ?_` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `nsmul_mem hx e`. Rewrite using `[mul_smul]`. Conclude with `nsmul_mem hy d`. Consider the case `smul a x _ hx`.

Take `⟨d, hd, hx⟩` from `hx`. Take `⟨e, b, he, hb⟩` from `exists_nat_mul_integral a`. Use `⟨e * d, Nat.mul_pos he hd, ?_⟩` and prove the remaining obligations. Establish `: (e * d) • a • x = b • d • x`. Rewrite using `[← algebraMap_smul E b, ← hb]`.

Use extensionality with `i`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `L.smul_mem b hx`.
-/
theorem exists_nsmul_mem {E : Type} [Field E] {n : ℕ} [NumberField E]
    (L : Submodule (RingOfIntegers E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (w : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ d • w ∈ L := by
  have hw : w ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, hd, hx⟩ := hx
    obtain ⟨e, he, hy⟩ := hy
    refine ⟨d * e, Nat.mul_pos hd he, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact nsmul_mem hx e
    · rw [mul_smul]; exact nsmul_mem hy d
  | smul a x _ hx =>
    obtain ⟨d, hd, hx⟩ := hx
    obtain ⟨e, b, he, hb⟩ := exists_nat_mul_integral a
    refine ⟨e * d, Nat.mul_pos he hd, ?_⟩
    have : (e * d) • a • x = b • d • x := by
      rw [← algebraMap_smul E b, ← hb]
      ext i
      simp
      ring
    rw [this]
    exact L.smul_mem b hx

/- English proof (translation)
Take `⟨s, hs⟩` from `hfg`. Use `choose f hf hmem using fun v => exists_nsmul_mem L hL (M.mulVec v)`. Use `⟨∏ v ∈ s, f v, Finset.prod_pos fun v _ => hf v, fun v hv => ?_⟩` and prove the remaining obligations. Establish `hv' : v ∈ Submodule.span (RingOfIntegers E) (s : Set (Fin n → E))`. Rewrite using `[hs]`.

Conclude with `hv`. Use `clear hv`. Proceed by induction on `hv' using Submodule.span_induction with`. Consider the case `mem x hx`. Rewrite using `[← Finset.prod_erase_mul s f (Finset.mem_coe.mp hx), mul_smul]`.

Conclude with `nsmul_mem (hmem x) _`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Rewrite using `[Matrix.mulVec_add, smul_add]`. Conclude with `L.add_mem hx hy`.

Consider the case `smul a x _ hx`. Rewrite using `[← algebraMap_smul E a, Matrix.mulVec_smul, algebraMap_smul, smul_comm]`. Conclude with `L.smul_mem a hx`.
-/
theorem exists_nsmul_mulVec_mem {E : Type} [Field E] {n : ℕ} [NumberField E]
    (L : Submodule (RingOfIntegers E) (Fin n → E)) (hfg : L.FG)
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (M : Matrix (Fin n) (Fin n) E) :
    ∃ d : ℕ, 0 < d ∧ ∀ v ∈ L, d • M.mulVec v ∈ L := by
  classical
  obtain ⟨s, hs⟩ := hfg
  choose f hf hmem using fun v => exists_nsmul_mem L hL (M.mulVec v)
  refine ⟨∏ v ∈ s, f v, Finset.prod_pos fun v _ => hf v, fun v hv => ?_⟩
  have hv' : v ∈ Submodule.span (RingOfIntegers E) (s : Set (Fin n → E)) := by
    rw [hs]; exact hv
  clear hv
  induction hv' using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.prod_erase_mul s f (Finset.mem_coe.mp hx), mul_smul]
    exact nsmul_mem (hmem x) _
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Matrix.mulVec_add, smul_add]
    exact L.add_mem hx hy
  | smul a x _ hx =>
    rw [← algebraMap_smul E a, Matrix.mulVec_smul, algebraMap_smul, smul_comm]
    exact L.smul_mem a hx

end GlobalTheory.IntegralMultipleOfVectors
