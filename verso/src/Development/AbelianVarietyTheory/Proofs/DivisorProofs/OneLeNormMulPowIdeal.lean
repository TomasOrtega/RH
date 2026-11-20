import Mathlib
open NumberField

open scoped Pointwise

namespace GlobalTheory

/- English proof (translation)
Establish `mem_one : ∀ x : K, IsIntegral ℤ x → x ∈ (1 : Submodule (𝓞 K) K)`. Introduce `x hx`. Conclude with `Submodule.mem_one.mpr ⟨⟨x, hx⟩, rfl⟩`. Rewrite using `[Submodule.mul_le]`. Introduce `y hy x hx`.

Rewrite `hx` using `[Submodule.pow_eq_span_pow_set]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f, rfl⟩` from `Set.mem_pow.mp hx`. Apply `mem_one` to reduce the goal to its premises.

Rewrite using `[List.prod_ofFn]`. Break down `Nat.eq_zero_or_pos i with rfl | hi` into its components or cases. Simplify using `using h y hy 0 J.zero_mem`. Apply `IsIntegral.of_pow hi` to reduce the goal to its premises. Establish `e : (y * ∏ k, (f k : K)) ^ i = ∏ k : Fin i, ((f k : K) ^ i * y)`.

Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow, Finset.prod_pow, mul_comm]`. Rewrite using `[e]`. Conclude with `IsIntegral.prod _ (fun k _ => h y hy _ (f k).2)`. Consider the case `zero => simp`. Consider the case `add x z _ _ hx hz => rw [mul_add]`.

Conclude with `add_mem hx hz`. Consider the case `smul r x _ hx => rw [mul_smul_comm]`. Conclude with `Submodule.smul_mem _ r hx`.
-/
theorem mul_pow_le_one_of_forall_isIntegral {K : Type} [Field K] [NumberField K]
    (I J : Submodule (𝓞 K) K) (i : ℕ) (h : ∀ y ∈ I, ∀ b ∈ J, IsIntegral ℤ (b ^ i * y)) :
    I * J ^ i ≤ 1 := by
  have mem_one : ∀ x : K, IsIntegral ℤ x → x ∈ (1 : Submodule (𝓞 K) K) := by
    intro x hx
    exact Submodule.mem_one.mpr ⟨⟨x, hx⟩, rfl⟩
  rw [Submodule.mul_le]
  intro y hy x hx
  rw [Submodule.pow_eq_span_pow_set] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, rfl⟩ := Set.mem_pow.mp hx
    apply mem_one
    rw [List.prod_ofFn]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simpa using h y hy 0 J.zero_mem
    · apply IsIntegral.of_pow hi
      have e : (y * ∏ k, (f k : K)) ^ i = ∏ k : Fin i, ((f k : K) ^ i * y) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          mul_pow, Finset.prod_pow, mul_comm]
      rw [e]
      exact IsIntegral.prod _ (fun k _ => h y hy _ (f k).2)
  | zero => simp
  | add x z _ _ hx hz => rw [mul_add]; exact add_mem hx hz
  | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx

/- English proof (translation)
Introduce `K _ _ I J hI hJ i hI0 hJ0 h`. Use `set A : FractionalIdeal (nonZeroDivisors (𝓞 K)) K := ⟨I, FractionalIdeal.isFractional_of_fg hI⟩ with hAdef`. Use `set B : FractionalIdeal (nonZeroDivisors (𝓞 K)) K := ⟨J, FractionalIdeal.isFractional_of_fg hJ⟩ with hBdef`. Establish `hA : A ≠ 0`. Introduce `h0`.

Apply `hI0` to reduce the goal to its premises. Use `congrArg (fun F : FractionalIdeal (nonZeroDivisors (𝓞 K)) K => (F : Submodule (𝓞 K) K)) h0` as an intermediate fact. Simplify `this` using `[hAdef]`. Establish `hB : B ≠ 0`. Introduce `h0`.

Apply `hJ0` to reduce the goal to its premises. Use `congrArg (fun F : FractionalIdeal (nonZeroDivisors (𝓞 K)) K => (F : Submodule (𝓞 K) K)) h0` as an intermediate fact. Simplify `this` using `[hBdef]`. Establish `hle : A * B ^ i ≤ 1`. Rewrite using `[← FractionalIdeal.coe_le_coe, FractionalIdeal.coe_mul, FractionalIdeal.coe_pow, FractionalIdeal.coe_one]`.

Conclude with `mul_pow_le_one_of_forall_isIntegral I J i h`. Take `⟨Q, hQ⟩` from `FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle`. Establish `hne : A * B ^ i ≠ 0` using `mul_ne_zero hA (pow_ne_zero _ hB)`. Establish `hQ0 : Q ≠ ⊥`. Introduce and unpack `rfl`.

Apply `hne` to reduce the goal to its premises. Rewrite using `[← hQ, FractionalIdeal.coeIdeal_bot]`. Rewrite using `[← map_pow, ← map_mul, ← hQ, FractionalIdeal.coeIdeal_absNorm]`. Establish `: Ideal.absNorm Q ≠ 0` using `fun h0 => hQ0 (Ideal.absNorm_eq_zero_iff.mp h0)`. Conclude with `Nat.one_le_iff_ne_zero.mpr this` after adjusting the coercions.
-/
theorem one_le_absNorm_mul_absNorm_pow_of_forall_isIntegral :
    ∀ (K : Type) [Field K] [NumberField K] (I J : Submodule (𝓞 K) K) (hI : I.FG) (hJ : J.FG)
      (i : ℕ), I ≠ ⊥ → J ≠ ⊥ → (∀ y ∈ I, ∀ b ∈ J, IsIntegral ℤ (b ^ i * y)) →
      1 ≤ FractionalIdeal.absNorm
          (⟨I, FractionalIdeal.isFractional_of_fg hI⟩ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) *
        FractionalIdeal.absNorm
          (⟨J, FractionalIdeal.isFractional_of_fg hJ⟩ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ i := by
  intro K _ _ I J hI hJ i hI0 hJ0 h
  set A : FractionalIdeal (nonZeroDivisors (𝓞 K)) K := ⟨I, FractionalIdeal.isFractional_of_fg hI⟩ with hAdef
  set B : FractionalIdeal (nonZeroDivisors (𝓞 K)) K := ⟨J, FractionalIdeal.isFractional_of_fg hJ⟩ with hBdef
  have hA : A ≠ 0 := by
    intro h0
    apply hI0
    have := congrArg (fun F : FractionalIdeal (nonZeroDivisors (𝓞 K)) K => (F : Submodule (𝓞 K) K)) h0
    simpa [hAdef] using this
  have hB : B ≠ 0 := by
    intro h0
    apply hJ0
    have := congrArg (fun F : FractionalIdeal (nonZeroDivisors (𝓞 K)) K => (F : Submodule (𝓞 K) K)) h0
    simpa [hBdef] using this
  have hle : A * B ^ i ≤ 1 := by
    rw [← FractionalIdeal.coe_le_coe, FractionalIdeal.coe_mul, FractionalIdeal.coe_pow,
      FractionalIdeal.coe_one]
    exact mul_pow_le_one_of_forall_isIntegral I J i h
  obtain ⟨Q, hQ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  have hne : A * B ^ i ≠ 0 := mul_ne_zero hA (pow_ne_zero _ hB)
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply hne
    rw [← hQ, FractionalIdeal.coeIdeal_bot]
  rw [← map_pow, ← map_mul, ← hQ, FractionalIdeal.coeIdeal_absNorm]
  have : Ideal.absNorm Q ≠ 0 := fun h0 => hQ0 (Ideal.absNorm_eq_zero_iff.mp h0)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr this

end GlobalTheory
