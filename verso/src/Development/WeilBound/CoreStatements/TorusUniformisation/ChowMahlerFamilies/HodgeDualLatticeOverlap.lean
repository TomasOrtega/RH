import Mathlib
import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

namespace PositivityTheory.Xgn.HodgeDualOverlap

/- English proof (translation)
Simplify using `[dotDual, AddSubgroup.mem_iInf]`.
-/
theorem mem_dotDual {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] (R : Subalgebra O Ω) {r : ℕ}
    (L : AddSubgroup (Fin r → Ω)) (e : Fin r → Ω) :
    e ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ e ∈ R := by
  simp [dotDual, AddSubgroup.mem_iInf]

end PositivityTheory.Xgn.HodgeDualOverlap

/- English proof (translation)
Establish `hq : x i / x j ∈ chartRing O x j` using `Algebra.subset_adjoin ⟨i, rfl⟩`. Establish `mono : ∀ z : Ω, ∀ d n : ℕ, d ≤ n → (x i / x j) ^ d * z ∈ chartRing O x j → (x i / x j) ^ n * z ∈ chartRing O x j`. Introduce `z d n hdn hz`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hdn`. Rewrite using `[pow_add, mul_comm ((x i / x j) ^ d), mul_assoc]`.

Conclude with `Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hq _) hz`. Proceed by induction on `hy using Algebra.adjoin_induction with`. Consider the case `mem z hz`. Take `⟨t, rfl⟩` from `hz`. Use `⟨1, ?_⟩` and prove the remaining obligations.

Establish `h : (x i / x j) ^ 1 * (x t / x i) = x t / x j`. Rewrite using `[pow_one, div_mul_div_comm, mul_comm (x i), mul_div_mul_right _ _ hi]`. Rewrite using `[h]`. Conclude with `Algebra.subset_adjoin ⟨t, rfl⟩`. Consider the case `algebraMap r => exact ⟨0, by simpa using Subalgebra.algebraMap_mem _ r⟩`.

Consider the case `add a b _ _ ha hb`. Take `⟨d, hd⟩` from `ha`. Take `⟨e, he⟩` from `hb`. Use `⟨d + e, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_add]`.

Conclude with `Subalgebra.add_mem _ (mono _ d _ (by omega) hd) (mono _ e _ (by omega) he)`. Consider the case `mul a b _ _ ha hb`. Take `⟨d, hd⟩` from `ha`. Take `⟨e, he⟩` from `hb`. Use `⟨d + e, ?_⟩` and prove the remaining obligations.

Establish `h : (x i / x j) ^ (d + e) * (a * b) = ((x i / x j) ^ d * a) * ((x i / x j) ^ e * b)`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h]`. Conclude with `Subalgebra.mul_mem _ hd he`.
-/
private theorem exists_div_pow_mul_mem_chartRing {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] {ι : Type}
    (x : ι → Ω) (i j : ι) (hi : x i ≠ 0) (y : Ω) (hy : y ∈ chartRing O x i) :
    ∃ d : ℕ, (x i / x j) ^ d * y ∈ chartRing O x j := by
  have hq : x i / x j ∈ chartRing O x j := Algebra.subset_adjoin ⟨i, rfl⟩
  have mono : ∀ z : Ω, ∀ d n : ℕ, d ≤ n → (x i / x j) ^ d * z ∈ chartRing O x j →
      (x i / x j) ^ n * z ∈ chartRing O x j := by
    intro z d n hdn hz
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hdn
    rw [pow_add, mul_comm ((x i / x j) ^ d), mul_assoc]
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hq _) hz
  induction hy using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨t, rfl⟩ := hz
    refine ⟨1, ?_⟩
    have h : (x i / x j) ^ 1 * (x t / x i) = x t / x j := by
      rw [pow_one, div_mul_div_comm, mul_comm (x i), mul_div_mul_right _ _ hi]
    rw [h]
    exact Algebra.subset_adjoin ⟨t, rfl⟩
  | algebraMap r => exact ⟨0, by simpa using Subalgebra.algebraMap_mem _ r⟩
  | add a b _ _ ha hb =>
    obtain ⟨d, hd⟩ := ha
    obtain ⟨e, he⟩ := hb
    refine ⟨d + e, ?_⟩
    rw [mul_add]
    exact Subalgebra.add_mem _ (mono _ d _ (by omega) hd) (mono _ e _ (by omega) he)
  | mul a b _ _ ha hb =>
    obtain ⟨d, hd⟩ := ha
    obtain ⟨e, he⟩ := hb
    refine ⟨d + e, ?_⟩
    have h : (x i / x j) ^ (d + e) * (a * b) = ((x i / x j) ^ d * a) * ((x i / x j) ^ e * b) := by
      ring
    rw [h]
    exact Subalgebra.mul_mem _ hd he

open PositivityTheory.Xgn.HodgeDualOverlap in
/- English proof (translation)
Introduce `O _ Ω _ _ ι x r L _ h2 h3 i j hi hj e he`. Rewrite `he` using `[mem_dotDual]`. Establish `hq : x i / x j ∈ chartRing O x j` using `Algebra.subset_adjoin ⟨i, rfl⟩`. Take `⟨n, s, hs, hgen⟩` from `h3 j hj`. Establish `hk : ∀ k, ∃ m : ℕ, (x i / x j) ^ m * (s k ⬝ᵥ e) ∈ chartRing O x j`.

Introduce `k`. Take `⟨a, ha⟩` from `h2 j i hj hi (s k) (hs k)`. Establish `hmem` using `he _ ha`. Rewrite `hmem` using `[smul_dotProduct, smul_eq_mul]`. Take `⟨d, hd⟩` from `exists_div_pow_mul_mem_chartRing x i j hi _ hmem`.

Use `⟨d, ?_⟩` and prove the remaining obligations. Establish `hc1 : x i / x j * (x j / x i) = 1` using `by field_simp`. Establish `hc : (x i / x j) ^ a * (x j / x i) ^ a = 1` using `by rw [← mul_pow, hc1, one_pow]`. Establish `h : (x i / x j) ^ d * (s k ⬝ᵥ e) = (x i / x j) ^ a * ((x i / x j) ^ d * ((x j / x i) ^ a * (s k ⬝ᵥ e)))`. Take the linear combination `(-((x i / x j) ^ d * (s k ⬝ᵥ e))) * hc`.

Rewrite using `[h]`. Conclude with `Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hq _) hd`. Use `choose m hm using hk`. Use `⟨∑ k, m k, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_dotDual]`.

Introduce `l hl`. Take `⟨c, hc, rfl⟩` from `hgen l hl`. Rewrite using `[sum_dotProduct]`. Use `Subalgebra.sum_mem _ (fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]`.

Use `Subalgebra.mul_mem _ (hc k) ?_` and prove the remaining obligations. Establish `hle : m k ≤ ∑ k, m k` using `Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)`. Take `⟨t, ht⟩` from `Nat.exists_eq_add_of_le hle`. Rewrite using `[ht, pow_add, mul_comm ((x i / x j) ^ m k), mul_assoc]`. Conclude with `Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hq _) (hm k)`.
-/
theorem PositivityTheory.Xgn.hodge_dual_lattice_overlap : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (ι : Type) (x : ι → Ω) (r : ℕ)
    (L : ι → AddSubgroup (Fin r → Ω)),
    (∀ c, ∀ a ∈ chartRing O x c, ∀ e ∈ L c, a • e ∈ L c) →
    (∀ i j, x i ≠ 0 → x j ≠ 0 → ∀ e ∈ L i, ∃ m : ℕ, (x i / x j) ^ m • e ∈ L j) →
    (∀ c, x c ≠ 0 → ∃ (n : ℕ) (s : Fin n → Fin r → Ω), (∀ k, s k ∈ L c) ∧
      ∀ e ∈ L c, ∃ a : Fin n → Ω, (∀ k, a k ∈ chartRing O x c) ∧ e = ∑ k, a k • s k) →
    ∀ i j, x i ≠ 0 → x j ≠ 0 → ∀ e ∈ dotDual (chartRing O x i) (L i),
      ∃ m : ℕ, (x i / x j) ^ m • e ∈ dotDual (chartRing O x j) (L j) := by
  intro O _ Ω _ _ ι x r L _ h2 h3 i j hi hj e he
  rw [mem_dotDual] at he
  have hq : x i / x j ∈ chartRing O x j := Algebra.subset_adjoin ⟨i, rfl⟩
  obtain ⟨n, s, hs, hgen⟩ := h3 j hj
  have hk : ∀ k, ∃ m : ℕ, (x i / x j) ^ m * (s k ⬝ᵥ e) ∈ chartRing O x j := by
    intro k
    obtain ⟨a, ha⟩ := h2 j i hj hi (s k) (hs k)
    have hmem := he _ ha
    rw [smul_dotProduct, smul_eq_mul] at hmem
    obtain ⟨d, hd⟩ := exists_div_pow_mul_mem_chartRing x i j hi _ hmem
    refine ⟨d, ?_⟩
    have hc1 : x i / x j * (x j / x i) = 1 := by field_simp
    have hc : (x i / x j) ^ a * (x j / x i) ^ a = 1 := by rw [← mul_pow, hc1, one_pow]
    have h : (x i / x j) ^ d * (s k ⬝ᵥ e) =
        (x i / x j) ^ a * ((x i / x j) ^ d * ((x j / x i) ^ a * (s k ⬝ᵥ e))) := by
      linear_combination (-((x i / x j) ^ d * (s k ⬝ᵥ e))) * hc
    rw [h]
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hq _) hd
  choose m hm using hk
  refine ⟨∑ k, m k, ?_⟩
  rw [mem_dotDual]
  intro l hl
  obtain ⟨c, hc, rfl⟩ := hgen l hl
  rw [sum_dotProduct]
  refine Subalgebra.sum_mem _ (fun k _ => ?_)
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  refine Subalgebra.mul_mem _ (hc k) ?_
  have hle : m k ≤ ∑ k, m k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hle
  rw [ht, pow_add, mul_comm ((x i / x j) ^ m k), mul_assoc]
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hq _) (hm k)
