import Mathlib

namespace GlobalTheory.NonzeroSmulMemSpan

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨a, ha, hay⟩` from `hy`.

Take `⟨b, hb, hbz⟩` from `hz`. Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `A.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`.

Conclude with `A.smul_mem b hay`. Rewrite using `[mul_smul]`. Conclude with `A.smul_mem a hbz`. Consider the case `smul c y _ hy`. Take `⟨a, ha, hay⟩` from `hy`.

Take `⟨⟨p, q⟩, hpq⟩` from `IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) c`. Use `⟨(q : NumberField.RingOfIntegers E) * a, mul_ne_zero (nonZeroDivisors.ne_zero q.2) ha, ?_⟩` and prove the remaining obligations. Establish `key : ((q : NumberField.RingOfIntegers E) * a) • c • y = p • a • y`. Rewrite using `[← algebraMap_smul E ((q : NumberField.RingOfIntegers E) * a), ← algebraMap_smul E p, ← algebraMap_smul E a y, smul_smul, smul_smul, map_mul]`. Simplify using `only at hpq`.

Rewrite using `[← hpq]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Conclude with `A.smul_mem p hay`.
-/
theorem exists_ne_zero_smul_mem_of_mem_span {E : Type} [Field E] [NumberField E] {n : ℕ}
    (A : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) {x : Fin n → E}
    (hx : x ∈ Submodule.span E (↑A : Set (Fin n → E))) :
    ∃ (o : NumberField.RingOfIntegers E), o ≠ (0 : NumberField.RingOfIntegers E) ∧ o • x ∈ A := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine A.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact A.smul_mem b hay
    · rw [mul_smul]
      exact A.smul_mem a hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨p, q⟩, hpq⟩ :=
      IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) c
    refine ⟨(q : NumberField.RingOfIntegers E) * a,
      mul_ne_zero (nonZeroDivisors.ne_zero q.2) ha, ?_⟩
    have key : ((q : NumberField.RingOfIntegers E) * a) • c • y = p • a • y := by
      rw [← algebraMap_smul E ((q : NumberField.RingOfIntegers E) * a),
        ← algebraMap_smul E p, ← algebraMap_smul E a y, smul_smul, smul_smul, map_mul]
      simp only at hpq
      rw [← hpq]
      congr 1
      ring
    rw [key]
    exact A.smul_mem p hay

end GlobalTheory.NonzeroSmulMemSpan
