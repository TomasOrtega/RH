import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot

noncomputable section

namespace GlobalTheory.BK

open PowerSeries

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Establish `hf : (i.factorial : K) ≠ 0` using `natCast_ne_zero' l i.factorial_ne_zero`. Establish `hc : ((i.factorial : S O K e) : K⟦X⟧) = C (i.factorial : K)`. Rewrite using `[map_natCast]`. Both sides reduce to the same expression.

Simplify using `only [SubmonoidClass.coe_pow, coe_EIn, Subalgebra.coe_mul, Ediv, hc]`. Rewrite using `[← mul_assoc, ← map_mul, mul_inv_cancel₀ hf, map_one, one_mul]`.
-/
theorem EIn_pow_eq_factorial_mul_Ediv (i : ℕ) :
    EIn l e (S O K e) ^ i = (i.factorial : S O K e) * ⟨Ediv K l e i, Ediv_mem_S l e i⟩ := by
  apply Subtype.ext
  have hf : (i.factorial : K) ≠ 0 := natCast_ne_zero' l i.factorial_ne_zero
  have hc : ((i.factorial : S O K e) : K⟦X⟧) = C (i.factorial : K) := by
    rw [map_natCast]; rfl
  simp only [SubmonoidClass.coe_pow, coe_EIn, Subalgebra.coe_mul, Ediv, hc]
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hf, map_one, one_mul]

/- English proof (translation)
Establish `hu : uIn (S O K e) ^ e = EIn l e (S O K e) + -(l : S O K e)`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[E]`. Use `⟨∑ i ∈ Finset.range j, EIn l e (S O K e) ^ i * (-1) ^ (l - i) * (l : S O K e) ^ (j - i) * (l.choose i : S O K e), ∑ i ∈ Finset.Ico j (l + 1), EIn l e (S O K e) ^ i * (-(l : S O K e)) ^ (l - i) * (l.choose i : S O K e), ?_, ?_⟩` and prove the remaining obligations. Use `Ideal.sum_mem _ fun i hi => ?_` and prove the remaining obligations.

Establish `hi' : j ≤ i` using `(Finset.mem_Ico.1 hi).1`. Rewrite using `[EIn_pow_eq_factorial_mul_Ediv]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ediv_mem_Fil l e hi')))`. Rewrite using `[pow_mul, hu, add_pow, ← Finset.sum_range_add_sum_Ico _ (by omega : j ≤ l + 1), Finset.mul_sum]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hi' : i < j` using `Finset.mem_range.1 hi`. Establish `h1 : l - i = (l - j) + (j - i)` using `by omega`. Rewrite using `[neg_pow, h1, pow_add, pow_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_uIn_pow_eq (j : ℕ) (hj : j ≤ l) : ∃ σ : S O K e, ∃ φ ∈ Fil O K l e j,
    uIn (S O K e) ^ (e * l) = (l : S O K e) ^ (l - j) * σ + φ := by
  have hu : uIn (S O K e) ^ e = EIn l e (S O K e) + -(l : S O K e) := by
    apply Subtype.ext
    simp [E]
  refine ⟨∑ i ∈ Finset.range j, EIn l e (S O K e) ^ i * (-1) ^ (l - i) * (l : S O K e) ^ (j - i) *
      (l.choose i : S O K e),
    ∑ i ∈ Finset.Ico j (l + 1), EIn l e (S O K e) ^ i * (-(l : S O K e)) ^ (l - i) *
      (l.choose i : S O K e), ?_, ?_⟩
  · refine Ideal.sum_mem _ fun i hi => ?_
    have hi' : j ≤ i := (Finset.mem_Ico.1 hi).1
    rw [EIn_pow_eq_factorial_mul_Ediv]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ediv_mem_Fil l e hi')))
  · rw [pow_mul, hu, add_pow, ← Finset.sum_range_add_sum_Ico _ (by omega : j ≤ l + 1),
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < j := Finset.mem_range.1 hi
    have h1 : l - i = (l - j) + (j - i) := by omega
    rw [neg_pow, h1, pow_add, pow_add]
    ring

/- English proof (translation)
Take `⟨σ, φ, hφ, h⟩` from `exists_uIn_pow_eq (O := O) (K := K) (l := l) (e := e) j hj`. Use `⟨σ • w, P.MM.smul_mem σ hw, φ • w, Submodule.smul_mem_smul hφ hw, ?_⟩` and prove the remaining obligations. Establish `h2 : (X : K⟦X⟧) ^ (e * l) • w = (uIn (S O K e) ^ (e * l)) • w`. Rewrite using `[Subalgebra.smul_def]`. Simplify using the standard rewrite rules.

Establish `h3 : ((l : S O K e) ^ (l - j)) • (σ • w) = (l : K) ^ (l - j) • (σ • w)`. Rewrite using `[← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]`. Rewrite using `[h2, h, add_smul, mul_smul, h3]`.
-/
theorem X_pow_smul_mem_l_pow_MM_add_FilMM (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι) (j : ℕ) (hj : j ≤ l)
    (w : Vec K a ι) (hw : w ∈ P.MM) : ∃ s ∈ P.MM, ∃ f ∈ P.FilMM j,
      (X : K⟦X⟧) ^ (e * l) • w = (l : K) ^ (l - j) • s + f := by
  obtain ⟨σ, φ, hφ, h⟩ := exists_uIn_pow_eq (O := O) (K := K) (l := l) (e := e) j hj
  refine ⟨σ • w, P.MM.smul_mem σ hw, φ • w, Submodule.smul_mem_smul hφ hw, ?_⟩
  have h2 : (X : K⟦X⟧) ^ (e * l) • w = (uIn (S O K e) ^ (e * l)) • w := by
    rw [Subalgebra.smul_def]
    simp
  have h3 : ((l : S O K e) ^ (l - j)) • (σ • w) = (l : K) ^ (l - j) • (σ • w) := by
    rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [h2, h, add_smul, mul_smul, h3]

end GlobalTheory.BK
