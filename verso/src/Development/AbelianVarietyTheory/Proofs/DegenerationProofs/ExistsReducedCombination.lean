import Mathlib

open Module

namespace GlobalTheory

namespace LatticeIneq

variable {X : Type} [AddCommGroup X]

/- English proof (translation)
Establish `h1 : q (a + b) = q a + q b + QuadraticMap.polar q a b`. Simplify using `[QuadraticMap.polar]`. Establish `h2 : q (a + (-(j : ℤ)) • b) = q a + q ((-(j : ℤ)) • b) + QuadraticMap.polar q a ((-(j : ℤ)) • b)`. Simplify using `only [QuadraticMap.polar]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h2` using `[QuadraticMap.polar_smul_right, QuadraticMap.map_smul]`. Establish `h3` using `hq (a + (-(j : ℤ)) • b)`. Rewrite `h3` using `[h2]`. Simplify using `only [zsmul_eq_mul] at h3`. Move the coercions through the operations in `at h3`.

Rewrite using `[h1]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem weighted_add_le (q : QuadraticMap ℤ X ℝ) (hq : ∀ x, 0 ≤ q x) (j : ℕ) (a b : X) :
    (j : ℝ) * q (a + b) ≤ (j + 1) * q a + j * (j + 1) * q b := by
  have h1 : q (a + b) = q a + q b + QuadraticMap.polar q a b := by
    simp [QuadraticMap.polar]
  have h2 : q (a + (-(j : ℤ)) • b) = q a + q ((-(j : ℤ)) • b)
      + QuadraticMap.polar q a ((-(j : ℤ)) • b) := by
    simp only [QuadraticMap.polar]; ring
  rw [QuadraticMap.polar_smul_right, QuadraticMap.map_smul] at h2
  have h3 := hq (a + (-(j : ℤ)) • b)
  rw [h2] at h3
  simp only [zsmul_eq_mul] at h3
  push_cast at h3
  rw [h1]
  nlinarith

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.sum_insert hi, Finset.sum_insert hi, Finset.card_insert_of_notMem hi]`. Break down `s.eq_empty_or_nonempty with rfl | hs` into its components or cases.

Simplify using the standard rewrite rules. Establish `hpos : (0 : ℝ) < s.card` using `by exact_mod_cast hs.card_pos`. Establish `h` using `weighted_add_le q hq s.card (∑ x ∈ s, v x) (v i)`. Rewrite using `[add_comm (v i)]`. Use `push_cast`.

Use `le_of_mul_le_mul_left ?_ hpos` and prove the remaining obligations. Establish `h2` using `mul_le_mul_of_nonneg_left ih (by positivity : (0 : ℝ) ≤ (s.card : ℝ) + 1)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem map_sum_le (q : QuadraticMap ℤ X ℝ) (hq : ∀ x, 0 ≤ q x) {I : Type} (s : Finset I)
    (v : I → X) : q (∑ x ∈ s, v x) ≤ s.card * ∑ x ∈ s, q (v x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.card_insert_of_notMem hi]
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
    · have hpos : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
      have h := weighted_add_le q hq s.card (∑ x ∈ s, v x) (v i)
      rw [add_comm (v i)]
      push_cast
      refine le_of_mul_le_mul_left ?_ hpos
      have h2 := mul_le_mul_of_nonneg_left ih (by positivity : (0 : ℝ) ≤ (s.card : ℝ) + 1)
      nlinarith

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Break down `hy with ⟨i, rfl⟩ | ⟨μ, rfl⟩` into its components or cases. Take `⟨μ, hμ⟩` from `hw i`. Use `⟨Pi.single i 1, μ, ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.sum_eq_single i]`. Simplify using `[hμ]`. Introduce `b _ hb`. Simplify using `[Pi.single_eq_of_ne hb]`. Simplify using the standard rewrite rules.

Conclude with `⟨0, -μ, by simp⟩`. Consider the case `zero => exact ⟨0, 0, by simp⟩`. Consider the case `add a b _ _ ha hb`. Take `⟨k, μ, h⟩` from `ha`. Take `⟨k', μ', h'⟩` from `hb`.

Use `⟨k + k', μ + μ', ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.add_apply, add_smul, Finset.sum_add_distrib, ← h, ← h', smul_add]`. Normalize the expressions using the abelian group laws. Consider the case `neg a _ ha`. Take `⟨k, μ, h⟩` from `ha`.

Use `⟨-k, -μ, ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, ← h, smul_neg]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_int_combination {I : Type} [Fintype I] (N : ℕ) (yy w : I → X)
    (hw : ∀ x, ∃ μ, w x = yy x + N • μ) (z : X)
    (hz : z ∈ AddSubgroup.closure (Set.range yy ∪ Set.range fun μ : X => N • μ)) :
    ∃ (k : I → ℤ) (μ : X), z + N • μ = ∑ x, k x • w x := by
  classical
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    rcases hy with ⟨i, rfl⟩ | ⟨μ, rfl⟩
    · obtain ⟨μ, hμ⟩ := hw i
      refine ⟨Pi.single i 1, μ, ?_⟩
      rw [Finset.sum_eq_single i]
      · simp [hμ]
      · intro b _ hb; simp [Pi.single_eq_of_ne hb]
      · simp
    · exact ⟨0, -μ, by simp⟩
  | zero => exact ⟨0, 0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨k, μ, h⟩ := ha
    obtain ⟨k', μ', h'⟩ := hb
    refine ⟨k + k', μ + μ', ?_⟩
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, ← h, ← h', smul_add]
    abel
  | neg a _ ha =>
    obtain ⟨k, μ, h⟩ := ha
    refine ⟨-k, -μ, ?_⟩
    simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, ← h, smul_neg]
    abel

/- English proof (translation)
Take `⟨k, μ, h⟩` from `exists_int_combination N yy w hw z hz`. Establish `hN' : (0 : ℤ) < N` using `by exact_mod_cast hN`. Use `⟨fun x => k x % N, μ - ∑ x, (k x / N) • w x, fun x => ⟨Int.emod_nonneg _ hN'.ne', (Int.emod_lt_of_pos _ hN').le⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_sub, ← add_sub_assoc, h, Finset.smul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations.

Rewrite using `[← natCast_zsmul, smul_smul, ← sub_smul]`. Simplify using `only [Int.emod_def]`.
-/
theorem exists_reduced_combination {I : Type} [Fintype I] (N : ℕ) (hN : 1 ≤ N) (yy w : I → X)
    (hw : ∀ x, ∃ μ, w x = yy x + N • μ) (z : X)
    (hz : z ∈ AddSubgroup.closure (Set.range yy ∪ Set.range fun μ : X => N • μ)) :
    ∃ (k : I → ℤ) (μ : X), (∀ x, 0 ≤ k x ∧ k x ≤ N) ∧ z + N • μ = ∑ x, k x • w x := by
  obtain ⟨k, μ, h⟩ := exists_int_combination N yy w hw z hz
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  refine ⟨fun x => k x % N, μ - ∑ x, (k x / N) • w x,
    fun x => ⟨Int.emod_nonneg _ hN'.ne', (Int.emod_lt_of_pos _ hN').le⟩, ?_⟩
  rw [smul_sub, ← add_sub_assoc, h, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← natCast_zsmul, smul_smul, ← sub_smul]
  simp only [Int.emod_def]

end LatticeIneq

open LatticeIneq in

/- English proof (translation)
Introduce `X _ q hq I _ N N' j hN hNN' _ yy w vth αs c vf' hw hwq hα hc`. Take `⟨m, rfl⟩` from `hNN'`. Establish `hw' : ∀ x, ∃ μ, w x = yy x + N • μ` using `fun x => by`. Take `⟨μ, hμ⟩` from `hw x`. Conclude with `⟨m • μ, by rw [hμ, mul_smul]⟩`.

Take `⟨k, μ, hk, h⟩` from `exists_reduced_combination N hN yy w hw' _ hc`. Use `⟨μ, ?_⟩` and prove the remaining obligations. Establish `hc' : c + N • μ = αs + ∑ x, k x • w x` using `by rw [← h]; abel`. Establish `hNpos : (0 : ℝ) < N` using `by exact_mod_cast hN`. Establish `h1` using `weighted_add_le q hq j αs (∑ x, k x • w x)`.

Establish `h2` using `map_sum_le q hq Finset.univ (fun x => k x • w x)`. Establish `h3 : ∑ x, q (k x • w x) ≤ (N : ℝ) ^ 2 * ((N * m : ℕ) : ℝ) ^ 2 * ∑ x, vth x`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun x _ => ?_` and prove the remaining obligations. Rewrite using `[QuadraticMap.map_smul, zsmul_eq_mul]`.

Establish `a0 : (0 : ℝ) ≤ k x` using `by exact_mod_cast (hk x).1`. Establish `a1 : (k x : ℝ) ≤ N` using `by exact_mod_cast (hk x).2`. Establish `a2 : ((k x * k x : ℤ) : ℝ) ≤ (N : ℝ) ^ 2` using `by push_cast; nlinarith`. Combine the equalities or inequalities in the displayed calculation. Rewrite `h2` using `[Finset.card_univ]`.

Establish `h4` using `h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))`. Establish `h5` using `mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ (j : ℝ) * (j + 1))`. Establish `h6` using `mul_le_mul_of_nonneg_left hα (by positivity : (0 : ℝ) ≤ (j : ℝ) + 1)`. Rewrite using `[hc', ← mul_div_assoc, div_le_iff₀ hNpos]`. Move the coercions through the operations in `at h5 ⊢`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lattice_inequality :
    ∀ (X : Type) [AddCommGroup X] (q : QuadraticMap ℤ X ℝ), (∀ x, 0 ≤ q x) → ∀ (I : Type) [Fintype I] (N N' j : ℕ), 1 ≤ N → N ∣ N' → 1 ≤ j → ∀ (yy w : I → X) (vth : I → ℝ) (αs c : X) (vf' : ℝ), (∀ x, ∃ μ, w x = yy x + N' • μ) → (∀ x, q (w x) ≤ (N' : ℝ) ^ 2 * vth x) → q αs ≤ N * vf' → c - αs ∈ AddSubgroup.closure (Set.range yy ∪ Set.range fun μ : X => N • μ) → ∃ μ : X, j * (q (c + N • μ) / N) ≤ (j + 1) * vf' + (j * (j + 1) * Fintype.card I * N * N' ^ 2 : ℕ) * ∑ x, vth x := by
  intro X _ q hq I _ N N' j hN hNN' _ yy w vth αs c vf' hw hwq hα hc
  obtain ⟨m, rfl⟩ := hNN'
  have hw' : ∀ x, ∃ μ, w x = yy x + N • μ := fun x => by
    obtain ⟨μ, hμ⟩ := hw x
    exact ⟨m • μ, by rw [hμ, mul_smul]⟩
  obtain ⟨k, μ, hk, h⟩ := exists_reduced_combination N hN yy w hw' _ hc
  refine ⟨μ, ?_⟩
  have hc' : c + N • μ = αs + ∑ x, k x • w x := by rw [← h]; abel
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := weighted_add_le q hq j αs (∑ x, k x • w x)
  have h2 := map_sum_le q hq Finset.univ (fun x => k x • w x)
  have h3 : ∑ x, q (k x • w x) ≤ (N : ℝ) ^ 2 * ((N * m : ℕ) : ℝ) ^ 2 * ∑ x, vth x := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [QuadraticMap.map_smul, zsmul_eq_mul]
    have a0 : (0 : ℝ) ≤ k x := by exact_mod_cast (hk x).1
    have a1 : (k x : ℝ) ≤ N := by exact_mod_cast (hk x).2
    have a2 : ((k x * k x : ℤ) : ℝ) ≤ (N : ℝ) ^ 2 := by push_cast; nlinarith
    calc _ ≤ (N : ℝ) ^ 2 * q (w x) := mul_le_mul_of_nonneg_right a2 (hq _)
      _ ≤ (N : ℝ) ^ 2 * (((N * m : ℕ) : ℝ) ^ 2 * vth x) :=
        mul_le_mul_of_nonneg_left (hwq x) (by positivity)
      _ = _ := by ring
  rw [Finset.card_univ] at h2
  have h4 := h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
  have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ (j : ℝ) * (j + 1))
  have h6 := mul_le_mul_of_nonneg_left hα (by positivity : (0 : ℝ) ≤ (j : ℝ) + 1)
  rw [hc', ← mul_div_assoc, div_le_iff₀ hNpos]
  push_cast at h5 ⊢
  linarith

end GlobalTheory
