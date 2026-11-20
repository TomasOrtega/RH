import Mathlib

namespace GlobalTheory.TargetLemmaCollection

open NumberField

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨d₁, hd₁, h₁⟩` from `hy`.

Take `⟨d₂, hd₂, h₂⟩` from `hz`. Use `⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Establish `e1 : (d₁ * d₂) • y = d₂ • (d₁ • y)` using `by rw [mul_comm, mul_smul]`. Establish `e2 : (d₁ * d₂) • z = d₁ • (d₂ • z)` using `by rw [mul_smul]`.

Rewrite using `[e1, e2]`. Conclude with `A.add_mem (A.smul_mem _ h₁) (A.smul_mem _ h₂)`. Consider the case `smul c y _ hy`. Take `⟨d, hd, h⟩` from `hy`. Take `⟨⟨a, b⟩, hab⟩` from `IsLocalization.surj (nonZeroDivisors (RingOfIntegers K)) c`.

Simplify using `only at hab`. Establish `hb : (b : RingOfIntegers K) ≠ 0` using `nonZeroDivisors.coe_ne_zero b`. Use `⟨(b : RingOfIntegers K) * d, mul_ne_zero hb hd, ?_⟩` and prove the remaining obligations. Establish `key : ((b : RingOfIntegers K) * d) • (c • y) = a • (d • y)`. Rewrite using `[← smul_assoc, Algebra.smul_def, map_mul, mul_comm (algebraMap _ K (b : RingOfIntegers K)), mul_assoc, mul_comm _ c, hab, ← map_mul, algebraMap_smul, mul_comm, mul_smul]`.

Rewrite using `[key]`. Conclude with `A.smul_mem _ h`.
-/
theorem main {K : Type} [Field K] [NumberField K] {Z : Type} [AddCommGroup Z] [Module K Z]
    [Module (RingOfIntegers K) Z] [IsScalarTower (RingOfIntegers K) K Z]
    {A : Submodule (RingOfIntegers K) Z} {x : Z} (hx : x ∈ Submodule.span K (A : Set Z)) :
    ∃ d : RingOfIntegers K, d ≠ 0 ∧ d • x ∈ A := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d₁, hd₁, h₁⟩ := hy
    obtain ⟨d₂, hd₂, h₂⟩ := hz
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    have e1 : (d₁ * d₂) • y = d₂ • (d₁ • y) := by rw [mul_comm, mul_smul]
    have e2 : (d₁ * d₂) • z = d₁ • (d₂ • z) := by rw [mul_smul]
    rw [e1, e2]
    exact A.add_mem (A.smul_mem _ h₁) (A.smul_mem _ h₂)
  | smul c y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (RingOfIntegers K)) c
    simp only at hab
    have hb : (b : RingOfIntegers K) ≠ 0 := nonZeroDivisors.coe_ne_zero b
    refine ⟨(b : RingOfIntegers K) * d, mul_ne_zero hb hd, ?_⟩
    have key : ((b : RingOfIntegers K) * d) • (c • y) = a • (d • y) := by
      rw [← smul_assoc, Algebra.smul_def, map_mul, mul_comm (algebraMap _ K (b : RingOfIntegers K)),
        mul_assoc, mul_comm _ c, hab, ← map_mul, algebraMap_smul, mul_comm, mul_smul]
    rw [key]
    exact A.smul_mem _ h

end GlobalTheory.TargetLemmaCollection

/- English proof (translation)
Introduce `hx` and use `GlobalTheory.TargetLemmaCollection.main hx`.
-/
theorem GlobalTheory.TargetLemmaCollection.target : ∀ {K : Type} [inst : Field K] [NumberField K] {Z : Type} [inst_2 : AddCommGroup Z] [inst_3 : Module K Z] [inst_4 : Module (NumberField.RingOfIntegers K) Z] [IsScalarTower (NumberField.RingOfIntegers K) K Z] {A : Submodule (NumberField.RingOfIntegers K) Z} {x : Z}, x ∈ Submodule.span K (↑A : Set Z) → ∃ (d : NumberField.RingOfIntegers K), d ≠ (0 : NumberField.RingOfIntegers K) ∧ d • x ∈ A :=
  fun hx => GlobalTheory.TargetLemmaCollection.main hx
