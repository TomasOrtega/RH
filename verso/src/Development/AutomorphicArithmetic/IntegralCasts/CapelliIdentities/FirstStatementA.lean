import Mathlib

/- English proof (translation)
Introduce `E _ _ n L x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add y z _ _ h1 h2`.

Take `⟨a, ha, hya⟩` from `h1`. Take `⟨b, hb, hzb⟩` from `h2`. Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations. Establish `e : (a * b) • (y + z) = b • (a • y) + a • (b • z)`. Rewrite using `[smul_add, mul_smul, mul_smul, smul_comm a b y]`.

Rewrite using `[e]`. Conclude with `L.add_mem (L.smul_of_tower_mem b hya) (L.smul_of_tower_mem a hzb)`. Consider the case `smul c y _ h`. Take `⟨a, ha, hya⟩` from `h`. Establish `halg : IsAlgebraic ℤ c` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)`.

Take `⟨d, hd, hint⟩` from `halg.exists_integral_multiple`. Use `⟨d * a, mul_ne_zero hd ha, ?_⟩` and prove the remaining obligations. Set `r : NumberField.RingOfIntegers E` to `⟨d • c, hint⟩`. Establish `e : (d * a) • (c • y) = r • (a • y)`. Establish `: r • (a • y) = (d • c) • (a • y)` using `rfl`.

Rewrite using `[this, mul_smul, smul_comm a c y, smul_assoc]`. Rewrite using `[e]`. Conclude with `L.smul_mem r hya`.
-/
theorem UpperTheory.Reformulated.B.FirstStatementA.main :
    ∀ {E : Type} [inst : Field E]
    [NumberField E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)),
    ∀ x ∈ Submodule.span E (↑L : Set (Fin n → E)), ∃ (m : ℤ), m ≠ (0 : ℤ) ∧ m • x ∈ L := by
  intro E _ _ n L x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ h1 h2 =>
    obtain ⟨a, ha, hya⟩ := h1
    obtain ⟨b, hb, hzb⟩ := h2
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have e : (a * b) • (y + z) = b • (a • y) + a • (b • z) := by
      rw [smul_add, mul_smul, mul_smul, smul_comm a b y]
    rw [e]
    exact L.add_mem (L.smul_of_tower_mem b hya) (L.smul_of_tower_mem a hzb)
  | smul c y _ h =>
    obtain ⟨a, ha, hya⟩ := h
    have halg : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)
    obtain ⟨d, hd, hint⟩ := halg.exists_integral_multiple
    refine ⟨d * a, mul_ne_zero hd ha, ?_⟩
    let r : NumberField.RingOfIntegers E := ⟨d • c, hint⟩
    have e : (d * a) • (c • y) = r • (a • y) := by
      have : r • (a • y) = (d • c) • (a • y) := rfl
      rw [this, mul_smul, smul_comm a c y, smul_assoc]
    rw [e]
    exact L.smul_mem r hya
