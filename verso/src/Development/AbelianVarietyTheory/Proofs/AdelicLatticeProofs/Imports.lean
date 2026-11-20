import Mathlib

namespace GlobalTheory.NatMulMem

open NumberField

/- English proof (translation)
Take `⟨y, hy, hint⟩` from `IsAlgebraic.exists_integral_multiple (R := ℤ) (z := c) ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c))`. Use `⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩` and prove the remaining obligations. Rewrite `hint` using `[zsmul_eq_mul]`. Break down `Int.natAbs_eq y with h | h` into its components or cases. Establish `: ((y.natAbs : ℕ) : E) = ((y : ℤ) : E)` using `by conv_rhs => rw [h]`.

Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `hint`. Establish `: ((y.natAbs : ℕ) : E) = -((y : ℤ) : E)` using `by conv_rhs => rw [h]`. Simplify using the standard rewrite rules.

Rewrite using `[this, neg_mul]`. Conclude with `hint.neg`.
-/
lemma exists_nat_mul_mem {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : E) * c) := by
  obtain ⟨y, hy, hint⟩ :=
    IsAlgebraic.exists_integral_multiple (R := ℤ) (z := c)
      ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c))
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  rw [zsmul_eq_mul] at hint
  rcases Int.natAbs_eq y with h | h
  · have : ((y.natAbs : ℕ) : E) = ((y : ℤ) : E) := by
      conv_rhs => rw [h]
      simp
    rw [this]; exact hint
  · have : ((y.natAbs : ℕ) : E) = -((y : ℤ) : E) := by
      conv_rhs => rw [h]
      simp
    rw [this, neg_mul]; exact hint.neg

/- English proof (translation)
Introduce `hspan`. Set `S : Submodule E (Fin n → E)` to `{ carrier := {x | ∃ d : ℕ, 0 < d ∧ d • x ∈ L} add_mem' := by`. Introduce and unpack `x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩`. Use `⟨a * b, Nat.mul_pos ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`.

Use `L.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `L.toAddSubmonoid.nsmul_mem hx b`. Rewrite using `[mul_smul]`. Conclude with `L.toAddSubmonoid.nsmul_mem hy a`.

Use the proof step `zero_mem' := ⟨1, one_pos, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c x ⟨a, ha, hx⟩`. Take `⟨m, hm, hint⟩` from `exists_nat_mul_mem c`. Use `⟨m * a, Nat.mul_pos hm ha, ?_⟩` and prove the remaining obligations.

Set `r : RingOfIntegers E` to `⟨(m : E) * c, hint⟩`. Establish `key : (m * a) • (c • x) = r • (a • x)`. Use function extensionality and compare the values at `i`. Establish `hr : algebraMap (RingOfIntegers E) E r = (m : E) * c` using `rfl`. Rewrite using `[Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Algebra.smul_def r, hr]`.

Simplify using `only [nsmul_eq_mul, smul_eq_mul, Nat.cast_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Conclude with `L.smul_mem r hx }`. Establish `hle : Submodule.span E (L : Set (Fin n → E)) ≤ S` using `Submodule.span_le.mpr (fun y hy => ⟨1, one_pos, by simpa using hy⟩)`.

Introduce `x`. Establish `hx : x ∈ S` using `hle (hspan ▸ Submodule.mem_top)`. Conclude with `hx`.
-/
theorem main {E : Type} [Field E] {n : ℕ} [NumberField E]
    (L : Submodule (RingOfIntegers E) (Fin n → E)) :
    Submodule.span E (L : Set (Fin n → E)) = ⊤ →
      ∀ x : Fin n → E, ∃ d : ℕ, 0 < d ∧ d • x ∈ L := by
  intro hspan
  let S : Submodule E (Fin n → E) :=
    { carrier := {x | ∃ d : ℕ, 0 < d ∧ d • x ∈ L}
      add_mem' := by
        rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
        refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
        rw [smul_add]
        refine L.add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact L.toAddSubmonoid.nsmul_mem hx b
        · rw [mul_smul]; exact L.toAddSubmonoid.nsmul_mem hy a
      zero_mem' := ⟨1, one_pos, by simp⟩
      smul_mem' := by
        rintro c x ⟨a, ha, hx⟩
        obtain ⟨m, hm, hint⟩ := exists_nat_mul_mem c
        refine ⟨m * a, Nat.mul_pos hm ha, ?_⟩
        let r : RingOfIntegers E := ⟨(m : E) * c, hint⟩
        have key : (m * a) • (c • x) = r • (a • x) := by
          funext i
          have hr : algebraMap (RingOfIntegers E) E r = (m : E) * c := rfl
          rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Algebra.smul_def r, hr]
          simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_mul]
          ring
        rw [key]; exact L.smul_mem r hx }
  have hle : Submodule.span E (L : Set (Fin n → E)) ≤ S :=
    Submodule.span_le.mpr (fun y hy => ⟨1, one_pos, by simpa using hy⟩)
  intro x
  have hx : x ∈ S := hle (hspan ▸ Submodule.mem_top)
  exact hx

end GlobalTheory.NatMulMem
