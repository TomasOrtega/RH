import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open NumberField IsDedekindDomain
open scoped Matrix

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ w`. Establish `hint : ∀ f : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) → IsIntegral ℤ ((NumberField.discr E : E) * f)`. Introduce `f hf`. Establish `hmem : f ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E)`. Rewrite using `[Submodule.mem_traceDual]`.

Introduce `a ha`. Take `⟨y, rfl⟩` from `Submodule.mem_one.mp ha`. Establish `h` using `hf y`. Rewrite `h` using `[IsIntegrallyClosed.isIntegral_iff]`. Take `⟨k, hk⟩` from `h`.

Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.traceForm_apply, hk, mul_comm]`. Establish `hb : ∀ i, IsIntegral ℤ (integralBasis E i)` using `fun i => by`. Rewrite using `[integralBasis_apply]`. Conclude with `RingOfIntegers.isIntegral_coe _`.

Establish `h1 : (1 : E) ∈ (1 : Submodule (𝓞 E) E)` using `Submodule.mem_one.mpr ⟨1, map_one _⟩`. Use `isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ) (1 : Submodule (𝓞 E) E) hb h1 hmem` as an intermediate fact. Rewrite `this` using `[← coe_discr, Algebra.smul_def, mul_one]`. Simplify using `using this`. Establish `hle : ∀ f : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) → w.valuation E ((NumberField.discr E : E) * f) ≤ 1`.

Introduce `f hf`. Take `⟨y, hy⟩` from `(IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp (hint f hf)`. Rewrite using `[← hy]`. Conclude with `w.valuation_le_one y`. Establish `hd0 : (NumberField.discr E : E) ≠ 0` using `by exact_mod_cast NumberField.discr_ne_zero E`.

Establish `hvd : w.valuation E (NumberField.discr E : E) ≠ 0` using `by simpa using hd0`. Establish `hP1 : ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * 1))` using `fun o => by`. Rewrite using `[mul_one]`. Conclude with `Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe o)`. Set `S : ℤ → Prop` to `fun k => ∃ f : E, f ≠ 0 ∧ (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) ∧ WithZero.log (w.valuation E f) = k`.

Establish `hbdd : ∃ b, ∀ z, S z → z ≤ b`. Use `⟨-WithZero.log (w.valuation E (NumberField.discr E : E)), ?_⟩` and prove the remaining obligations. Introduce and unpack `z ⟨f, hf0, hf, rfl⟩`. Establish `hvf : w.valuation E f ≠ 0` using `by simpa using hf0`. Establish `h` using `hle f hf`.

Rewrite `h` using `[map_mul, ← WithZero.exp_log hvd, ← WithZero.exp_log hvf, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Establish `hne : ∃ z, S z` using `⟨_, 1, one_ne_zero, hP1, rfl⟩`. Take `⟨k, ⟨e, he0, he, rfl⟩, hmax⟩` from `Int.exists_greatest_of_bdd hbdd hne`. Use `⟨e, he0, he, fun f hf => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hf0 : f = 0`. Substitute `hf0` using the available equality. Simplify using the standard rewrite rules. Establish `hvf : w.valuation E f ≠ 0` using `by simpa using hf0`. Establish `hve : w.valuation E e ≠ 0` using `by simpa using he0`.

Establish `h` using `hmax _ ⟨f, hf0, hf, rfl⟩`. Rewrite using `[← WithZero.exp_log hvf, ← WithZero.exp_log hve, WithZero.exp_le_exp]`. Conclude with `h`.
-/
theorem invDifferent_exists_max_valuation :
    ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), ∃ e : E, e ≠ 0 ∧
      (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) ∧
      ∀ f : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) →
        w.valuation E f ≤ w.valuation E e := by
  intro E _ _ w
  classical

  have hint : ∀ f : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) →
      IsIntegral ℤ ((NumberField.discr E : E) * f) := by
    intro f hf
    have hmem : f ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
      rw [Submodule.mem_traceDual]
      intro a ha
      obtain ⟨y, rfl⟩ := Submodule.mem_one.mp ha
      have h := hf y
      rw [IsIntegrallyClosed.isIntegral_iff] at h
      obtain ⟨k, hk⟩ := h
      refine ⟨k, ?_⟩
      rw [Algebra.traceForm_apply, hk, mul_comm]
    have hb : ∀ i, IsIntegral ℤ (integralBasis E i) := fun i => by
      rw [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _
    have h1 : (1 : E) ∈ (1 : Submodule (𝓞 E) E) := Submodule.mem_one.mpr ⟨1, map_one _⟩
    have := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ)
      (1 : Submodule (𝓞 E) E) hb h1 hmem
    rw [← coe_discr, Algebra.smul_def, mul_one] at this
    simpa using this
  have hle : ∀ f : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) →
      w.valuation E ((NumberField.discr E : E) * f) ≤ 1 := by
    intro f hf
    obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp (hint f hf)
    rw [← hy]
    exact w.valuation_le_one y
  have hd0 : (NumberField.discr E : E) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero E
  have hvd : w.valuation E (NumberField.discr E : E) ≠ 0 := by simpa using hd0
  have hP1 : ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * 1)) := fun o => by
    rw [mul_one]; exact Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe o)
  let S : ℤ → Prop := fun k => ∃ f : E, f ≠ 0 ∧
    (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) ∧
      WithZero.log (w.valuation E f) = k
  have hbdd : ∃ b, ∀ z, S z → z ≤ b := by
    refine ⟨-WithZero.log (w.valuation E (NumberField.discr E : E)), ?_⟩
    rintro z ⟨f, hf0, hf, rfl⟩
    have hvf : w.valuation E f ≠ 0 := by simpa using hf0
    have h := hle f hf
    rw [map_mul, ← WithZero.exp_log hvd, ← WithZero.exp_log hvf, ← WithZero.exp_add,
      ← WithZero.exp_zero, WithZero.exp_le_exp] at h
    omega
  have hne : ∃ z, S z := ⟨_, 1, one_ne_zero, hP1, rfl⟩
  obtain ⟨k, ⟨e, he0, he, rfl⟩, hmax⟩ := Int.exists_greatest_of_bdd hbdd hne
  refine ⟨e, he0, he, fun f hf => ?_⟩
  by_cases hf0 : f = 0
  · subst hf0; simp
  have hvf : w.valuation E f ≠ 0 := by simpa using hf0
  have hve : w.valuation E e ≠ 0 := by simpa using he0
  have h := hmax _ ⟨f, hf0, hf, rfl⟩
  rw [← WithZero.exp_log hvf, ← WithZero.exp_log hve, WithZero.exp_le_exp]
  exact h

end GlobalTheory
