import Mathlib

namespace GlobalTheory.NatMultipleIntegralSmulBound

open NumberField

/- English proof (translation)
Establish `ha : IsAlgebraic ℤ a` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)`. Take `⟨y, hy, hint⟩` from `ha.exists_integral_multiple`. Use `⟨y.natAbs * y.natAbs, Nat.mul_pos (Int.natAbs_pos.2 hy) (Int.natAbs_pos.2 hy), ⟨y • (y • a), (mem_integralClosure_iff ℤ E).2 (hint.smul y)⟩, ?_⟩` and prove the remaining obligations. Use `show y • (y • a) = ((y.natAbs * y.natAbs : ℕ) : E) * a`. Rewrite using `[smul_smul, zsmul_eq_mul, ← Int.cast_natCast, Int.natAbs_mul_self]`.
-/
theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ m : ℕ, 0 < m ∧ ∃ b : RingOfIntegers E, (b : E) = (m : E) * a := by
  have ha : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨y, hy, hint⟩ := ha.exists_integral_multiple
  refine ⟨y.natAbs * y.natAbs, Nat.mul_pos (Int.natAbs_pos.2 hy) (Int.natAbs_pos.2 hy),
    ⟨y • (y • a), (mem_integralClosure_iff ℤ E).2 (hint.smul y)⟩, ?_⟩
  show y • (y • a) = ((y.natAbs * y.natAbs : ℕ) : E) * a
  rw [smul_smul, zsmul_eq_mul, ← Int.cast_natCast, Int.natAbs_mul_self]

/- English proof (translation)
Establish `key : ∀ x ∈ Submodule.span E (↑L' : Set (Fin n → E)), ∃ c : ℕ, 0 < c ∧ (c : E) • x ∈ L'`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_pos, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_pos, by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨c, hc, hcx⟩` from `hx`. Take `⟨d, hd, hdy⟩` from `hy`. Use `⟨c * d, Nat.mul_pos hc hd, ?_⟩` and prove the remaining obligations. Establish `e : ((c * d : ℕ) : E) • (x + y) = d • ((c : E) • x) + c • ((d : E) • y)`.

Rewrite using `[smul_add, ← Nat.cast_smul_eq_nsmul E d, ← Nat.cast_smul_eq_nsmul E c, smul_smul, smul_smul, Nat.cast_mul, mul_comm (d : E)]`. Rewrite using `[e]`. Conclude with `L'.add_mem (L'.nsmul_mem hcx d) (L'.nsmul_mem hdy c)`. Consider the case `smul e x _ hx`. Take `⟨c, hc, hcx⟩` from `hx`.

Take `⟨m, hm, b, hb⟩` from `exists_nat_mul_integral e`. Use `⟨m * c, Nat.mul_pos hm hc, ?_⟩` and prove the remaining obligations. Establish `e' : ((m * c : ℕ) : E) • (e • x) = (b : E) • ((c : E) • x)`. Rewrite using `[hb, smul_smul, smul_smul, Nat.cast_mul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `hb' : (b : E) • ((c : E) • x) = b • ((c : E) • x)` using `algebraMap_smul E b _`. Rewrite using `[e', hb']`. Conclude with `L'.smul_mem b hcx`. Conclude with `key x (h ▸ Submodule.mem_top)`.
-/
theorem exists_nat_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L' : Submodule (RingOfIntegers E) (Fin n → E))
    (h : Submodule.span E (↑L' : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ c : ℕ, 0 < c ∧ (c : E) • x ∈ L' := by
  have key : ∀ x ∈ Submodule.span E (↑L' : Set (Fin n → E)), ∃ c : ℕ, 0 < c ∧ (c : E) • x ∈ L' := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
    | zero => exact ⟨1, one_pos, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, hcx⟩ := hx
      obtain ⟨d, hd, hdy⟩ := hy
      refine ⟨c * d, Nat.mul_pos hc hd, ?_⟩
      have e : ((c * d : ℕ) : E) • (x + y) = d • ((c : E) • x) + c • ((d : E) • y) := by
        rw [smul_add, ← Nat.cast_smul_eq_nsmul E d, ← Nat.cast_smul_eq_nsmul E c, smul_smul, smul_smul,
          Nat.cast_mul, mul_comm (d : E)]
      rw [e]
      exact L'.add_mem (L'.nsmul_mem hcx d) (L'.nsmul_mem hdy c)
    | smul e x _ hx =>
      obtain ⟨c, hc, hcx⟩ := hx
      obtain ⟨m, hm, b, hb⟩ := exists_nat_mul_integral e
      refine ⟨m * c, Nat.mul_pos hm hc, ?_⟩
      have e' : ((m * c : ℕ) : E) • (e • x) = (b : E) • ((c : E) • x) := by
        rw [hb, smul_smul, smul_smul, Nat.cast_mul]
        congr 1
        ring
      have hb' : (b : E) • ((c : E) • x) = b • ((c : E) • x) := algebraMap_smul E b _
      rw [e', hb']
      exact L'.smul_mem b hcx
  exact key x (h ▸ Submodule.mem_top)

/- English proof (translation)
Take `⟨s, rfl⟩` from `hL`. Establish `hs : ∃ c : ℕ, 0 < c ∧ ∀ x ∈ s, (c : E) • x ∈ L'`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨1, one_pos, by simp⟩`. Consider the case `@insert a s _ ih`.

Take `⟨c, hc, hcs⟩` from `ih`. Take `⟨d, hd, hda⟩` from `exists_nat_smul_mem L' h a`. Use `⟨c * d, Nat.mul_pos hc hd, fun x hx => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hx with rfl | hx` into its components or cases. Establish `e : ((c * d : ℕ) : E) • x = c • ((d : E) • x)`.

Rewrite using `[← Nat.cast_smul_eq_nsmul E c, smul_smul, Nat.cast_mul]`. Rewrite using `[e]`. Conclude with `L'.nsmul_mem hda c`. Establish `e : ((c * d : ℕ) : E) • x = d • ((c : E) • x)`. Rewrite using `[← Nat.cast_smul_eq_nsmul E d, smul_smul, Nat.cast_mul, mul_comm]`.

Rewrite using `[e]`. Conclude with `L'.nsmul_mem (hcs x hx) d`. Take `⟨c, hc, hcs⟩` from `hs`. Use `⟨c, hc, fun x hx => ?_⟩` and prove the remaining obligations. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx => exact hcs x hx`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Rewrite using `[smul_add]`. Conclude with `L'.add_mem hx hy`.

Consider the case `smul b x _ hx`. Rewrite `hx`, the goal using `[Nat.cast_smul_eq_nsmul]`. Rewrite using `[smul_comm]`. Conclude with `L'.smul_mem b hx`.
-/
theorem exists_nat_smul_le {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (L L' : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.FG L)
    (h : Submodule.span E (↑L' : Set (Fin n → E)) = ⊤) :
    ∃ (c : ℕ), (0 : ℕ) < c ∧ ∀ x ∈ L, (↑c : E) • x ∈ L' := by
  classical
  obtain ⟨s, rfl⟩ := hL
  have hs : ∃ c : ℕ, 0 < c ∧ ∀ x ∈ s, (c : E) • x ∈ L' := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_pos, by simp⟩
    | @insert a s _ ih =>
      obtain ⟨c, hc, hcs⟩ := ih
      obtain ⟨d, hd, hda⟩ := exists_nat_smul_mem L' h a
      refine ⟨c * d, Nat.mul_pos hc hd, fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · have e : ((c * d : ℕ) : E) • x = c • ((d : E) • x) := by
          rw [← Nat.cast_smul_eq_nsmul E c, smul_smul, Nat.cast_mul]
        rw [e]
        exact L'.nsmul_mem hda c
      · have e : ((c * d : ℕ) : E) • x = d • ((c : E) • x) := by
          rw [← Nat.cast_smul_eq_nsmul E d, smul_smul, Nat.cast_mul, mul_comm]
        rw [e]
        exact L'.nsmul_mem (hcs x hx) d
  obtain ⟨c, hc, hcs⟩ := hs
  refine ⟨c, hc, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact hcs x hx
  | zero => simp
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact L'.add_mem hx hy
  | smul b x _ hx =>
    rw [Nat.cast_smul_eq_nsmul] at hx ⊢
    rw [smul_comm]
    exact L'.smul_mem b hx

end GlobalTheory.NatMultipleIntegralSmulBound
