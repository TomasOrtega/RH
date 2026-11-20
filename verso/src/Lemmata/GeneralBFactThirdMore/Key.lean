import Mathlib

namespace Bl.general_b_fact_third'

/- English proof (translation)
Take `⟨y, hy0, hy⟩` from `((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)).exists_integral_multiple`. Use `⟨y.natAbs, Int.natAbs_pos.mpr hy0, ?_⟩` and prove the remaining obligations. Take `h | h` from `Int.natAbs_eq y`. Rewrite `hy` using `[h, zsmul_eq_mul]`. Simplify using `using hy`.

Rewrite `hy` using `[h, zsmul_eq_mul]`. Simplify using `using hy.neg`.
-/
private lemma key {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * c) := by
  obtain ⟨y, hy0, hy⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)).exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, ?_⟩
  obtain h | h := Int.natAbs_eq y
  · rw [h, zsmul_eq_mul] at hy
    simpa using hy
  · rw [h, zsmul_eq_mul] at hy
    simpa using hy.neg

/- English proof (translation)
Introduce `E _ _ n L hL w`. Establish `hw : w ∈ Submodule.span E (L : Set (Fin n → E))`. Rewrite using `[hL]`. Conclude with `Submodule.mem_top`. Proceed by induction on `hw using Submodule.span_induction with`.

Consider the case `mem x hx => exact ⟨1, one_pos, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_pos, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, hax⟩` from `hx`. Take `⟨b, hb, hby⟩` from `hy`.

Use `⟨a * b, Nat.mul_pos ha hb, ?_⟩` and prove the remaining obligations. Establish `e : (a * b) • (x + y) = b • (a • x) + a • (b • y)`. Rewrite using `[smul_add, smul_smul, smul_smul, mul_comm b a]`. Rewrite using `[e]`. Conclude with `L.add_mem (nsmul_mem hax b) (nsmul_mem hby a)`.

Consider the case `smul c x _ hx`. Take `⟨a, ha, hax⟩` from `hx`. Take `⟨d, hd, hdc⟩` from `key c`. Use `⟨d * a, Nat.mul_pos hd ha, ?_⟩` and prove the remaining obligations. Establish `h1` using `L.smul_mem (⟨(d : E) * c, hdc⟩ : NumberField.RingOfIntegers E) hax`.

Use `h1 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i`. Rewrite using `[Pi.smul_apply, Algebra.smul_def]`. Express the relevant statement in the definitionally equal form `_ = ((d : E) * c) * _`. Simplify using `[nsmul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem goal1 :
  ∀ {E : Type} [inst : Field.{0} E] [NumberField.{0} E] {n : Nat}
  (L : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) (Fin n → E)),
  Eq.{1} (Submodule.span.{0, 0} E (SetLike.coe.{0, 0} L)) Top.top.{0} →
    ∀ (w : Fin n → E),
      Exists.{1} fun (m : Nat) ↦ And (LT.lt.{0} 0 m) (Membership.mem.{0, 0} L (HSMul.hSMul.{0, 0, 0} m w)) := by
  intro E _ _ n L hL w
  have hw : w ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL]; exact Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    have e : (a * b) • (x + y) = b • (a • x) + a • (b • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm b a]
    rw [e]
    exact L.add_mem (nsmul_mem hax b) (nsmul_mem hby a)
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨d, hd, hdc⟩ := key c
    refine ⟨d * a, Nat.mul_pos hd ha, ?_⟩
    have h1 := L.smul_mem (⟨(d : E) * c, hdc⟩ : NumberField.RingOfIntegers E) hax
    convert h1 using 1
    ext i
    rw [Pi.smul_apply, Algebra.smul_def]
    change _ = ((d : E) * c) * _
    simp [nsmul_eq_mul]
    ring

end Bl.general_b_fact_third'
