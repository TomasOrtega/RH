import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => intro y _`. Simplify using `using hint y`. Consider the case `succ k ih`. Introduce `y hy`.

Rewrite `hy` using `[pow_succ]`. Use `Submodule.mul_induction_on hy ?_ ?_` and prove the remaining obligations. Introduce `a ha b hb`. Establish `: ((a * b : 𝓞 K) : K) = (a : K) * (b : K)` using `by simp`. Rewrite using `[this, map_mul, pow_succ]`.

Conclude with `mul_le_mul (ih a ha) (hM b hb) (h0 _) (pow_nonneg hM0 _)`. Introduce `a b ha hb`. Establish `: ((a + b : 𝓞 K) : K) = (a : K) + (b : K)` using `by simp`. Rewrite using `[this]`. Conclude with `(hadd _ _).trans (max_le ha hb)`.
-/
theorem nonarch_le_pow_of_mem_ideal_pow {K : Type} [Field K] [NumberField K] (J : Ideal (𝓞 K))
    (v : K →*₀ ℝ) (h0 : ∀ x, 0 ≤ v x) (hadd : ∀ x y, v (x + y) ≤ max (v x) (v y))
    (hint : ∀ c : 𝓞 K, v (c : K) ≤ 1) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ y ∈ J, v (y : K) ≤ M) (k : ℕ) : ∀ y ∈ J ^ k, v (y : K) ≤ M ^ k := by
  induction k with
  | zero => intro y _; simpa using hint y
  | succ k ih =>
    intro y hy
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro a ha b hb
      have : ((a * b : 𝓞 K) : K) = (a : K) * (b : K) := by simp
      rw [this, map_mul, pow_succ]
      exact mul_le_mul (ih a ha) (hM b hb) (h0 _) (pow_nonneg hM0 _)
    · intro a b ha hb
      have : ((a + b : 𝓞 K) : K) = (a : K) + (b : K) := by simp
      rw [this]
      exact (hadd _ _).trans (max_le ha hb)

/- English proof (translation)
Introduce `K _ _ I hI ⟨n, hn, hnI⟩`. Establish `hnK : (n : K) ≠ 0` using `Nat.cast_ne_zero.mpr hn.ne'`. Set `J : Ideal (𝓞 K)` to `{ carrier := {c | ∃ x ∈ I, (c : K) = (n : K) * x} zero_mem' := ⟨0, I.zero_mem, by simp⟩ add_mem' := by`. Introduce and unpack `a b ⟨x, hx, ha⟩ ⟨y, hy, hb⟩`. Use `⟨x + y, I.add_mem hx hy, ?_⟩` and prove the remaining obligations.

Establish `: ((a + b : 𝓞 K) : K) = (a : K) + (b : K)` using `by simp`. Rewrite using `[this, ha, hb]`. Expand and normalize the polynomial expressions, which then agree. Use the proof step `smul_mem' := by`. Introduce and unpack `c a ⟨x, hx, ha⟩`.

Use `⟨c • x, I.smul_mem c hx, ?_⟩` and prove the remaining obligations. Establish `: ((c • a : 𝓞 K) : K) = (c : K) * (a : K)` using `by simp`. Establish `h2 : c • x = (c : K) * x` using `Algebra.smul_def c x`. Rewrite using `[this, ha, h2]`. Use `ring }`.

Establish `hmem : ∀ x ∈ I, ∃ c ∈ J, (c : K) = (n : K) * x`. Introduce `x hx`. Take `⟨c, hc⟩` from `hnI x hx`. Conclude with `⟨c, ⟨x, hx, hc⟩, hc⟩`. Establish `hJ : J ≠ 0`.

Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hI`. Take `⟨c, hc, hcx⟩` from `hmem x hx`. Introduce `h`. Rewrite `hc` using `[h]`. Establish `: c = 0` using `by simpa using hc`.

Rewrite `hcx` using `[this]`. Conclude with `mul_ne_zero hnK hx0 (by simpa using hcx.symm)`. Establish `hJ' : J ∈ nonZeroDivisors (Ideal (𝓞 K))` using `mem_nonZeroDivisors_of_ne_zero hJ`. Use `set h := Fintype.card (ClassGroup (𝓞 K)) with hh`. Establish `hpos : 0 < h` using `Fintype.card_pos`.

Establish `hprin : (J ^ h).IsPrincipal`. Establish `h1 : ClassGroup.mk0 (⟨J, hJ'⟩ ^ h : nonZeroDivisors (Ideal (𝓞 K))) = 1`. Rewrite using `[map_pow]`. Conclude with `pow_card_eq_one`. Conclude with `(ClassGroup.mk0_eq_one_iff (pow_mem hJ' h)).mp h1`.

Take `⟨a, ha⟩` from `hprin`. Establish `ha0 : a ≠ 0`. Introduce `h0`. Apply `pow_ne_zero h hJ` to reduce the goal to its premises. Rewrite using `[ha, h0]`.

Simplify using the standard rewrite rules. Establish `haK : (a : K) ≠ 0` using `by simpa using ha0`. Use `⟨h, (a : K) / (n : K) ^ h, hpos, div_ne_zero haK (pow_ne_zero _ hnK), ?_⟩` and prove the remaining obligations. Introduce `v h0 hadd hint x₀ hx₀ hmax`. Establish `hvn : v (n : K) ≠ 0` using `(map_ne_zero v).mpr hnK`.

Establish `hM : ∀ y ∈ J, v (y : K) ≤ v (n : K) * v x₀`. Introduce and unpack `y ⟨x, hx, hy⟩`. Rewrite using `[hy, map_mul]`. Conclude with `mul_le_mul_of_nonneg_left (hmax x hx) (h0 _)`. Establish `h1 : v (a : K) ≤ (v (n : K) * v x₀) ^ h` using `nonarch_le_pow_of_mem_ideal_pow J v h0 hadd hint _ (mul_nonneg (h0 _) (h0 _)) hM h a (by rw [ha]; exact Submodule.mem_span_singleton_self a)`.

Establish `h2 : (v (n : K) * v x₀) ^ h ≤ v (a : K)`. Take `⟨c, hc, hcx⟩` from `hmem x₀ hx₀`. Establish `hch : c ^ h ∈ J ^ h` using `Ideal.pow_mem_pow hc h`. Rewrite `hch` using `[ha]`. Take `⟨d, hd⟩` from `Submodule.mem_span_singleton.mp hch`.

Establish `hd' : (d : K) * (a : K) = (c : K) ^ h`. Use `congrArg (algebraMap (𝓞 K) K) hd` as an intermediate fact. Simplify using `using this`. Rewrite using `[← map_mul, ← hcx, ← map_pow, ← hd', map_mul]`. Conclude with `mul_le_of_le_one_left (h0 _) (hint d)`.

Rewrite using `[map_div₀, map_pow, le_antisymm h1 h2, mul_pow]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_generator_pow_fractional_size : ∀ (K : Type) [Field K] [NumberField K] (I : Submodule (𝓞 K) K), I ≠ ⊥ → (∃ n : ℕ, 0 < n ∧ ∀ x ∈ I, (n : K) * x ∈ (algebraMap (𝓞 K) K).range) → ∃ (h : ℕ) (α : K), 0 < h ∧ α ≠ 0 ∧ ∀ v : K →*₀ ℝ, (∀ x, 0 ≤ v x) → (∀ x y, v (x + y) ≤ max (v x) (v y)) → (∀ c : 𝓞 K, v (c : K) ≤ 1) → ∀ x₀ ∈ I, (∀ x ∈ I, v x ≤ v x₀) → v α = v x₀ ^ h := by
  intro K _ _ I hI ⟨n, hn, hnI⟩
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  let J : Ideal (𝓞 K) :=
    { carrier := {c | ∃ x ∈ I, (c : K) = (n : K) * x}
      zero_mem' := ⟨0, I.zero_mem, by simp⟩
      add_mem' := by
        rintro a b ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
        refine ⟨x + y, I.add_mem hx hy, ?_⟩
        have : ((a + b : 𝓞 K) : K) = (a : K) + (b : K) := by simp
        rw [this, ha, hb]; ring
      smul_mem' := by
        rintro c a ⟨x, hx, ha⟩
        refine ⟨c • x, I.smul_mem c hx, ?_⟩
        have : ((c • a : 𝓞 K) : K) = (c : K) * (a : K) := by simp
        have h2 : c • x = (c : K) * x := Algebra.smul_def c x
        rw [this, ha, h2]; ring }
  have hmem : ∀ x ∈ I, ∃ c ∈ J, (c : K) = (n : K) * x := by
    intro x hx
    obtain ⟨c, hc⟩ := hnI x hx
    exact ⟨c, ⟨x, hx, hc⟩, hc⟩
  have hJ : J ≠ 0 := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    obtain ⟨c, hc, hcx⟩ := hmem x hx
    intro h
    rw [h] at hc
    have : c = 0 := by simpa using hc
    rw [this] at hcx
    exact mul_ne_zero hnK hx0 (by simpa using hcx.symm)
  have hJ' : J ∈ nonZeroDivisors (Ideal (𝓞 K)) := mem_nonZeroDivisors_of_ne_zero hJ
  set h := Fintype.card (ClassGroup (𝓞 K)) with hh
  have hpos : 0 < h := Fintype.card_pos
  have hprin : (J ^ h).IsPrincipal := by
    have h1 : ClassGroup.mk0 (⟨J, hJ'⟩ ^ h : nonZeroDivisors (Ideal (𝓞 K))) = 1 := by
      rw [map_pow]; exact pow_card_eq_one
    exact (ClassGroup.mk0_eq_one_iff (pow_mem hJ' h)).mp h1
  obtain ⟨a, ha⟩ := hprin
  have ha0 : a ≠ 0 := by
    intro h0
    apply pow_ne_zero h hJ
    rw [ha, h0]; simp
  have haK : (a : K) ≠ 0 := by simpa using ha0
  refine ⟨h, (a : K) / (n : K) ^ h, hpos, div_ne_zero haK (pow_ne_zero _ hnK), ?_⟩
  intro v h0 hadd hint x₀ hx₀ hmax
  have hvn : v (n : K) ≠ 0 := (map_ne_zero v).mpr hnK
  have hM : ∀ y ∈ J, v (y : K) ≤ v (n : K) * v x₀ := by
    rintro y ⟨x, hx, hy⟩
    rw [hy, map_mul]
    exact mul_le_mul_of_nonneg_left (hmax x hx) (h0 _)
  have h1 : v (a : K) ≤ (v (n : K) * v x₀) ^ h :=
    nonarch_le_pow_of_mem_ideal_pow J v h0 hadd hint _ (mul_nonneg (h0 _) (h0 _)) hM h a
      (by rw [ha]; exact Submodule.mem_span_singleton_self a)
  have h2 : (v (n : K) * v x₀) ^ h ≤ v (a : K) := by
    obtain ⟨c, hc, hcx⟩ := hmem x₀ hx₀
    have hch : c ^ h ∈ J ^ h := Ideal.pow_mem_pow hc h
    rw [ha] at hch
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hch
    have hd' : (d : K) * (a : K) = (c : K) ^ h := by
      have := congrArg (algebraMap (𝓞 K) K) hd
      simpa using this
    rw [← map_mul, ← hcx, ← map_pow, ← hd', map_mul]
    exact mul_le_of_le_one_left (h0 _) (hint d)
  rw [map_div₀, map_pow, le_antisymm h1 h2, mul_pow]
  field_simp

end GlobalTheory
