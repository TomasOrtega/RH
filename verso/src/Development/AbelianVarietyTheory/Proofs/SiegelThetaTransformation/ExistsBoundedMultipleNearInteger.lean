import Mathlib

namespace GlobalTheory.SimultaneousDiophantineApprox

open NumberField

/- English proof (translation)
Establish `hNq : (0 : ℚ) < N` using `by exact_mod_cast hN`. Establish `hbox : ∀ (j : ℕ) (i : ι), (⌊Int.fract ((j : ℚ) * a i) * N⌋).toNat < N`. Introduce `j i`. Establish `h0 : 0 ≤ Int.fract ((j : ℚ) * a i) * N` using `mul_nonneg (Int.fract_nonneg _) hNq.le`. Establish `h1 : Int.fract ((j : ℚ) * a i) * N < N`.

Use `Int.fract_lt_one ((j : ℚ) * a i)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hlt : ⌊Int.fract ((j : ℚ) * a i) * N⌋ < (N : ℤ)` using `Int.floor_lt.mpr (by exact_mod_cast h1)`. Establish `hnn : 0 ≤ ⌊Int.fract ((j : ℚ) * a i) * N⌋` using `Int.floor_nonneg.mpr h0`. Use linear arithmetic over natural numbers and integers.

Set `f : Fin (N ^ Fintype.card ι + 1) → (ι → Fin N)` to `fun j i => ⟨_, hbox j i⟩`. Establish `key : ∀ x y : Fin (N ^ Fintype.card ι + 1), x < y → f x = f y → ∃ m : ℕ, 0 < m ∧ m ≤ N ^ Fintype.card ι ∧ ∃ z : ι → ℤ, ∀ i, |(m : ℚ) * a i - z i| ≤ 1 / N`. Introduce `x y hxy hf`. Establish `hxy' : (x : ℕ) < y` using `hxy`. Establish `hy` using `y.2`.

Use `⟨y - x, by omega, by omega, fun i => ⌊(y : ℚ) * a i⌋ - ⌊(x : ℚ) * a i⌋, fun i => ?_⟩` and prove the remaining obligations. Establish `hv` using `congrArg Fin.val (congrFun hf i)`. Simplify using `only [f] at hv`. Establish `hx0 : 0 ≤ Int.fract ((x : ℕ) * a i) * (N : ℚ)` using `mul_nonneg (Int.fract_nonneg _) hNq.le`. Establish `hy0 : 0 ≤ Int.fract ((y : ℕ) * a i) * (N : ℚ)` using `mul_nonneg (Int.fract_nonneg _) hNq.le`.

Establish `hfl : ⌊Int.fract (((x : ℕ) : ℚ) * a i) * N⌋ = ⌊Int.fract (((y : ℕ) : ℚ) * a i) * N⌋`. Use `Int.floor_nonneg.mpr hx0` as an intermediate fact. Use `Int.floor_nonneg.mpr hy0` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hclose` using `Int.abs_sub_lt_one_of_floor_eq_floor hfl`.

Establish `heq : (((y - x : ℕ) : ℕ) : ℚ) * a i - ((⌊(y : ℚ) * a i⌋ - ⌊(x : ℚ) * a i⌋ : ℤ) : ℚ) = Int.fract (((y : ℕ) : ℚ) * a i) - Int.fract (((x : ℕ) : ℚ) * a i)`. Rewrite using `[Nat.cast_sub hxy'.le]`. Unfold `Int.fract`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[heq, le_div_iff₀ hNq]`. Establish `hm : |Int.fract (((y : ℕ) : ℚ) * a i) - Int.fract (((x : ℕ) : ℚ) * a i)| * N = |Int.fract (((x : ℕ) : ℚ) * a i) * N - Int.fract (((y : ℕ) : ℚ) * a i) * N|`. Rewrite using `[← sub_mul, abs_mul, abs_of_pos hNq, abs_sub_comm]`. Rewrite using `[hm]`. Conclude with `hclose.le`.

Take `⟨x, y, hne, hf⟩` from `Fintype.exists_ne_map_eq_of_card_lt f (by simp)`. Break down `lt_or_gt_of_ne hne with h | h` into its components or cases. Conclude with `key x y h hf`. Conclude with `key y x h hf.symm`.
-/
theorem simultaneous_approx {ι : Type} [Fintype ι] (N : ℕ) (hN : 0 < N) (a : ι → ℚ) :
    ∃ m : ℕ, 0 < m ∧ m ≤ N ^ Fintype.card ι ∧ ∃ z : ι → ℤ,
      ∀ i, |(m : ℚ) * a i - z i| ≤ 1 / N := by
  classical
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN

  have hbox : ∀ (j : ℕ) (i : ι), (⌊Int.fract ((j : ℚ) * a i) * N⌋).toNat < N := by
    intro j i
    have h0 : 0 ≤ Int.fract ((j : ℚ) * a i) * N := mul_nonneg (Int.fract_nonneg _) hNq.le
    have h1 : Int.fract ((j : ℚ) * a i) * N < N := by
      have := Int.fract_lt_one ((j : ℚ) * a i)
      nlinarith
    have hlt : ⌊Int.fract ((j : ℚ) * a i) * N⌋ < (N : ℤ) := Int.floor_lt.mpr (by exact_mod_cast h1)
    have hnn : 0 ≤ ⌊Int.fract ((j : ℚ) * a i) * N⌋ := Int.floor_nonneg.mpr h0
    omega
  let f : Fin (N ^ Fintype.card ι + 1) → (ι → Fin N) := fun j i => ⟨_, hbox j i⟩

  have key : ∀ x y : Fin (N ^ Fintype.card ι + 1), x < y → f x = f y →
      ∃ m : ℕ, 0 < m ∧ m ≤ N ^ Fintype.card ι ∧ ∃ z : ι → ℤ,
        ∀ i, |(m : ℚ) * a i - z i| ≤ 1 / N := by
    intro x y hxy hf
    have hxy' : (x : ℕ) < y := hxy
    have hy := y.2
    refine ⟨y - x, by omega, by omega, fun i => ⌊(y : ℚ) * a i⌋ - ⌊(x : ℚ) * a i⌋, fun i => ?_⟩
    have hv := congrArg Fin.val (congrFun hf i)
    simp only [f] at hv
    have hx0 : 0 ≤ Int.fract ((x : ℕ) * a i) * (N : ℚ) := mul_nonneg (Int.fract_nonneg _) hNq.le
    have hy0 : 0 ≤ Int.fract ((y : ℕ) * a i) * (N : ℚ) := mul_nonneg (Int.fract_nonneg _) hNq.le
    have hfl : ⌊Int.fract (((x : ℕ) : ℚ) * a i) * N⌋ = ⌊Int.fract (((y : ℕ) : ℚ) * a i) * N⌋ := by
      have := Int.floor_nonneg.mpr hx0
      have := Int.floor_nonneg.mpr hy0
      omega
    have hclose := Int.abs_sub_lt_one_of_floor_eq_floor hfl
    have heq : (((y - x : ℕ) : ℕ) : ℚ) * a i - ((⌊(y : ℚ) * a i⌋ - ⌊(x : ℚ) * a i⌋ : ℤ) : ℚ) =
        Int.fract (((y : ℕ) : ℚ) * a i) - Int.fract (((x : ℕ) : ℚ) * a i) := by
      rw [Nat.cast_sub hxy'.le]
      unfold Int.fract
      push_cast
      ring
    rw [heq, le_div_iff₀ hNq]
    have hm : |Int.fract (((y : ℕ) : ℚ) * a i) - Int.fract (((x : ℕ) : ℚ) * a i)| * N =
        |Int.fract (((x : ℕ) : ℚ) * a i) * N - Int.fract (((y : ℕ) : ℚ) * a i) * N| := by
      rw [← sub_mul, abs_mul, abs_of_pos hNq, abs_sub_comm]
    rw [hm]
    exact hclose.le
  obtain ⟨x, y, hne, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  rcases lt_or_gt_of_ne hne with h | h
  · exact key x y h hf
  · exact key y x h hf.symm

/- English proof (translation)
Use `set b := integralBasis E`. Use `set C : ℝ := ∑ i, ∑ σ : E →+* ℂ, ‖σ (b i)‖ with hC`. Establish `hC0 : 0 ≤ C` using `Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun σ _ => norm_nonneg _`. Take `⟨N, hN⟩` from `exists_nat_gt C`. Establish `hN0 : 0 < N` using `by exact_mod_cast hC0.trans_lt hN`.

Establish `hNr : (0 : ℝ) < N` using `by exact_mod_cast hN0`. Use `⟨N ^ Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)), fun x => ?_⟩` and prove the remaining obligations. Take `⟨m, hm0, hmN, z, hz⟩` from `simultaneous_approx N hN0 (b.repr x)`. Use `⟨m, ∑ i, (z i : E) * b i, hm0, hmN, ?_, ?_⟩` and prove the remaining obligations. Use `IsIntegral.sum _ fun i _ => IsIntegral.mul ?_ ?_` and prove the remaining obligations.

Simplify using `using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ E (z i)))`. Rewrite using `[integralBasis_apply]`. Conclude with `RingOfIntegers.isIntegral_coe _`. Establish `hx : (m : E) * x - ∑ i, (z i : E) * b i = ∑ i, ((((m : ℚ) * b.repr x i - z i : ℚ)) : E) * b i` using `by conv_lhs => rw [← b.sum_repr x]`. Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Rat.smul_def]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hx, pi_norm_lt_iff one_pos]`.

Introduce `σ`. Rewrite using `[canonicalEmbedding.apply_at, map_sum]`. Use `lt_of_le_of_lt (norm_sum_le _ _) ?_` and prove the remaining obligations. Use `lt_of_le_of_lt (Finset.sum_le_sum (g := fun i => 1 / (N : ℝ) * ∑ τ : E →+* ℂ, ‖τ (b i)‖) fun i _ => ?_) ?_` and prove the remaining obligations. Rewrite using `[map_mul, norm_mul, map_ratCast, Complex.norm_ratCast]`.

Use `mul_le_mul ?_ (Finset.single_le_sum (f := fun τ : E →+* ℂ => ‖τ (b i)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ σ)) (norm_nonneg _) (by positivity)` and prove the remaining obligations. Establish `h` using `Rat.cast_le (K := ℝ) |>.mpr (hz i)`. Rewrite `h` using `[Rat.cast_div, Rat.cast_one, Rat.cast_natCast, Rat.cast_abs]`. Then use the resulting hypothesis. Rewrite using `[← Finset.mul_sum, ← hC, one_div_mul_eq_div, div_lt_one hNr]`. Conclude with `hN`.
-/
theorem exists_bounded_multiple_near_integer (E : Type) [Field E] [NumberField E] :
    ∃ M : ℕ, ∀ x : E, ∃ (m : ℕ) (y : E), 0 < m ∧ m ≤ M ∧ IsIntegral ℤ y ∧
      ‖canonicalEmbedding E ((m : E) * x - y)‖ < 1 := by
  classical
  set b := integralBasis E

  set C : ℝ := ∑ i, ∑ σ : E →+* ℂ, ‖σ (b i)‖ with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun σ _ => norm_nonneg _
  obtain ⟨N, hN⟩ := exists_nat_gt C
  have hN0 : 0 < N := by exact_mod_cast hC0.trans_lt hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  refine ⟨N ^ Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)), fun x => ?_⟩
  obtain ⟨m, hm0, hmN, z, hz⟩ := simultaneous_approx N hN0 (b.repr x)
  refine ⟨m, ∑ i, (z i : E) * b i, hm0, hmN, ?_, ?_⟩
  · refine IsIntegral.sum _ fun i _ => IsIntegral.mul ?_ ?_
    · simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ E (z i)))
    · rw [integralBasis_apply]
      exact RingOfIntegers.isIntegral_coe _
  ·
    have hx : (m : E) * x - ∑ i, (z i : E) * b i =
        ∑ i, ((((m : ℚ) * b.repr x i - z i : ℚ)) : E) * b i := by
      conv_lhs => rw [← b.sum_repr x]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Rat.smul_def]
      push_cast
      ring
    rw [hx, pi_norm_lt_iff one_pos]
    intro σ
    rw [canonicalEmbedding.apply_at, map_sum]
    refine lt_of_le_of_lt (norm_sum_le _ _) ?_
    refine lt_of_le_of_lt (Finset.sum_le_sum (g := fun i => 1 / (N : ℝ) * ∑ τ : E →+* ℂ, ‖τ (b i)‖)
      fun i _ => ?_) ?_
    · rw [map_mul, norm_mul, map_ratCast, Complex.norm_ratCast]
      refine mul_le_mul ?_ (Finset.single_le_sum (f := fun τ : E →+* ℂ => ‖τ (b i)‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ σ)) (norm_nonneg _) (by positivity)
      have h := Rat.cast_le (K := ℝ) |>.mpr (hz i)
      rwa [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, Rat.cast_abs] at h
    · rw [← Finset.mul_sum, ← hC, one_div_mul_eq_div, div_lt_one hNr]
      exact hN

end GlobalTheory.SimultaneousDiophantineApprox
