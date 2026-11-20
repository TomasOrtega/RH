import Mathlib

open Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.T2

/- English proof (translation)
Take `⟨m, rfl⟩` from `Nat.exists_eq_add_of_le hka`. Establish `hx : (5 * x) ^ (k + m) * (x / 5) ^ k = 5 ^ m * x ^ (k + m + k)`. Rewrite using `[mul_pow, div_pow]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hx]`. Establish `h1 : (1 : ℝ) ≤ 5 ^ m` using `one_le_pow₀ (by norm_num)`. Conclude with `le_mul_of_one_le_left (by positivity) h1`.
-/
theorem pow_key (x : ℝ) (hx0 : 0 < x) (a k : ℕ) (hka : k ≤ a) :
    x ^ (a + k) ≤ (5 * x) ^ a * (x / 5) ^ k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hka
  have hx : (5 * x) ^ (k + m) * (x / 5) ^ k = 5 ^ m * x ^ (k + m + k) := by
    rw [mul_pow, div_pow]
    field_simp
    ring
  rw [hx]
  have h1 : (1 : ℝ) ≤ 5 ^ m := one_le_pow₀ (by norm_num)
  exact le_mul_of_one_le_left (by positivity) h1

/- English proof (translation)
Establish `hsplit : (∏ j ∈ s \ S, |ρ - t j|) * ∏ j ∈ S, |ρ - t j| = ∏ j ∈ s, |ρ - t j|` using `Finset.prod_sdiff hS`. Establish `hfar' : (r / 5) ^ (s \ S).card ≤ ∏ j ∈ s \ S, |ρ - t j|`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.prod_le_prod` to reduce the goal to its premises. Introduce `i _`.

Check the signs of the components of the expression. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_sdiff]`. Conclude with `hfar i hi.1 hi.2`. Establish `hcard : (s \ S).card + S.card = s.card` using `Finset.card_sdiff_add_card_eq_card hS`.

Establish `hka : S.card ≤ (s \ S).card` using `by omega`. Establish `key` using `pow_key (r / 25) (by positivity) (s \ S).card S.card hka`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[show 5 * (r / 25) = r / 5 by ring, show r / 25 / 5 = r / 5 / 25 by ring]`. Use `_ ≤ (∏ j ∈ s \ S, |ρ - t j|) * ∏ j ∈ S, |ρ - t j| := mul_le_mul hfar' hin (by positivity) (Finset.prod_nonneg (fun i _ => abs_nonneg _))`.

Use `_ = ∏ j ∈ s, |ρ - t j| := hsplit`.
-/
theorem prodDist_step {ι : Type*} [DecidableEq ι] (t : ι → ℝ) (s S : Finset ι) (hS : S ⊆ s)
    (h3 : 3 * S.card ≤ s.card) (r ρ : ℝ) (hr : 0 < r)
    (hfar : ∀ j ∈ s, j ∉ S → r / 5 ≤ |ρ - t j|)
    (hin : ((r / 5) / 25) ^ S.card ≤ ∏ j ∈ S, |ρ - t j|) :
    (r / 25) ^ s.card ≤ ∏ j ∈ s, |ρ - t j| := by
  have hsplit : (∏ j ∈ s \ S, |ρ - t j|) * ∏ j ∈ S, |ρ - t j| = ∏ j ∈ s, |ρ - t j| :=
    Finset.prod_sdiff hS
  have hfar' : (r / 5) ^ (s \ S).card ≤ ∏ j ∈ s \ S, |ρ - t j| := by
    calc (r / 5) ^ (s \ S).card = ∏ _j ∈ s \ S, (r / 5) := (Finset.prod_const _).symm
      _ ≤ ∏ j ∈ s \ S, |ρ - t j| := by
        apply Finset.prod_le_prod
        · intro i _
          positivity
        · intro i hi
          rw [Finset.mem_sdiff] at hi
          exact hfar i hi.1 hi.2
  have hcard : (s \ S).card + S.card = s.card := Finset.card_sdiff_add_card_eq_card hS
  have hka : S.card ≤ (s \ S).card := by omega
  have key := pow_key (r / 25) (by positivity) (s \ S).card S.card hka
  calc (r / 25) ^ s.card = (r / 25) ^ ((s \ S).card + S.card) := by rw [hcard]
    _ ≤ (5 * (r / 25)) ^ (s \ S).card * (r / 25 / 5) ^ S.card := key
    _ = (r / 5) ^ (s \ S).card * ((r / 5) / 25) ^ S.card := by
        rw [show 5 * (r / 25) = r / 5 by ring, show r / 25 / 5 = r / 5 / 25 by ring]
    _ ≤ (∏ j ∈ s \ S, |ρ - t j|) * ∏ j ∈ S, |ρ - t j| :=
        mul_le_mul hfar' hin (by positivity)
          (Finset.prod_nonneg (fun i _ => abs_nonneg _))
    _ = ∏ j ∈ s, |ρ - t j| := hsplit

/- English proof (translation)
Use `set S1 := s.filter (fun j => |t j - (c - 4 * r / 5)| < 2 * r / 5) with hS1`. Use `set S2 := s.filter (fun j => |t j - c| < 2 * r / 5) with hS2`. Use `set S3 := s.filter (fun j => |t j - (c + 4 * r / 5)| < 2 * r / 5) with hS3`. Establish `d12 : Disjoint S1 S2`. Rewrite using `[hS1, hS2, Finset.disjoint_filter]`.

Introduce `j _ h1 h2`. Rewrite `h1`, `h2` using `[abs_lt]`. Combine the linear relations using `[h1.1, h1.2, h2.1, h2.2]`. Establish `d13 : Disjoint S1 S3`. Rewrite using `[hS1, hS3, Finset.disjoint_filter]`.

Introduce `j _ h1 h2`. Rewrite `h1`, `h2` using `[abs_lt]`. Combine the linear relations using `[h1.1, h1.2, h2.1, h2.2]`. Establish `d23 : Disjoint S2 S3`. Rewrite using `[hS2, hS3, Finset.disjoint_filter]`.

Introduce `j _ h1 h2`. Rewrite `h1`, `h2` using `[abs_lt]`. Combine the linear relations using `[h1.1, h1.2, h2.1, h2.2]`. Establish `hsub : S1 ∪ S2 ∪ S3 ⊆ s` using `Finset.union_subset (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)) (Finset.filter_subset _ _)`. Establish `hsum : S1.card + S2.card + S3.card ≤ s.card`.

Establish `h` using `Finset.card_le_card hsub`. Rewrite `h` using `[Finset.card_union_of_disjoint (Finset.disjoint_union_left.2 ⟨d13, d23⟩), Finset.card_union_of_disjoint d12]`. Then use the resulting hypothesis. Distinguish the cases in `h1 : 3 * S1.card ≤ s.card`. Use `⟨c - 4 * r / 5, ?_, h1⟩` and prove the remaining obligations. Rewrite using `[abs_le]`.

Apply the tactic sequence `constructor <;> linarith`. Distinguish the cases in `h2 : 3 * S2.card ≤ s.card`. Use `⟨c, ?_, h2⟩` and prove the remaining obligations. Rewrite using `[abs_le]`. Apply the tactic sequence `constructor <;> linarith`.

Use `⟨c + 4 * r / 5, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[abs_le]`. Apply the tactic sequence `constructor <;> linarith`. Establish `h3' : 3 * S3.card ≤ s.card` using `by omega`. Conclude with `h3'`.
-/
private theorem exists_center_near_with_few_points_close {ι : Type*} (t : ι → ℝ) (s : Finset ι) (c r : ℝ)
    (hr : 0 < r) :
    ∃ c' : ℝ, |c' - c| ≤ 4 * r / 5 ∧
      3 * (s.filter (fun j => |t j - c'| < 2 * r / 5)).card ≤ s.card := by
  classical
  set S1 := s.filter (fun j => |t j - (c - 4 * r / 5)| < 2 * r / 5) with hS1
  set S2 := s.filter (fun j => |t j - c| < 2 * r / 5) with hS2
  set S3 := s.filter (fun j => |t j - (c + 4 * r / 5)| < 2 * r / 5) with hS3
  have d12 : Disjoint S1 S2 := by
    rw [hS1, hS2, Finset.disjoint_filter]
    intro j _ h1 h2
    rw [abs_lt] at h1 h2
    linarith [h1.1, h1.2, h2.1, h2.2]
  have d13 : Disjoint S1 S3 := by
    rw [hS1, hS3, Finset.disjoint_filter]
    intro j _ h1 h2
    rw [abs_lt] at h1 h2
    linarith [h1.1, h1.2, h2.1, h2.2]
  have d23 : Disjoint S2 S3 := by
    rw [hS2, hS3, Finset.disjoint_filter]
    intro j _ h1 h2
    rw [abs_lt] at h1 h2
    linarith [h1.1, h1.2, h2.1, h2.2]
  have hsub : S1 ∪ S2 ∪ S3 ⊆ s :=
    Finset.union_subset (Finset.union_subset (Finset.filter_subset _ _)
      (Finset.filter_subset _ _)) (Finset.filter_subset _ _)
  have hsum : S1.card + S2.card + S3.card ≤ s.card := by
    have h := Finset.card_le_card hsub
    rwa [Finset.card_union_of_disjoint (Finset.disjoint_union_left.2 ⟨d13, d23⟩),
      Finset.card_union_of_disjoint d12] at h
  by_cases h1 : 3 * S1.card ≤ s.card
  · refine ⟨c - 4 * r / 5, ?_, h1⟩
    rw [abs_le]
    constructor <;> linarith
  by_cases h2 : 3 * S2.card ≤ s.card
  · refine ⟨c, ?_, h2⟩
    rw [abs_le]
    constructor <;> linarith
  · refine ⟨c + 4 * r / 5, ?_, ?_⟩
    · rw [abs_le]
      constructor <;> linarith
    · have h3' : 3 * S3.card ≤ s.card := by omega
      exact h3'

/- English proof (translation)
Introduce `N`. Proceed by induction on `N using Nat.strong_induction_on with`. Consider the case `_ N ih`. Introduce `s hs c r hr`. Break down `Nat.eq_zero_or_pos N with h0 | hpos` into its components or cases.

Substitute `h0` using the available equality. Rewrite `hs` using `[Finset.card_eq_zero]`. Substitute `hs` using the available equality. Use `⟨c, by simp [hr.le], by simp⟩` and prove the remaining obligations. Take `⟨c', hc', h3⟩` from `exists_center_near_with_few_points_close t s c r hr set S := s.filter (fun j => |t j - c'| < 2 * r / 5) with hSdef`.

Establish `hlt : S.card < N` using `by omega`. Take `⟨ρ, hρ, hin⟩` from `ih S.card hlt S rfl c' (r / 5) (by positivity)`. Use `⟨ρ, ?_, prodDist_step t s S (Finset.filter_subset _ _) h3 r ρ hr ?_ hin⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Introduce `j hj hjS`.

Establish `hn : 2 * r / 5 ≤ |t j - c'|` using `not_lt.mp (fun h => hjS (Finset.mem_filter.2 ⟨hj, h⟩))`. Establish `htri : |t j - c'| ≤ |t j - ρ| + |ρ - c'|` using `abs_sub_le (t j) ρ c'`. Rewrite `htri` using `[abs_sub_comm (t j) ρ]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_far_from_points {ι : Type*} [DecidableEq ι] (t : ι → ℝ) :
    ∀ (N : ℕ) (s : Finset ι), s.card = N → ∀ (c r : ℝ), 0 < r →
      ∃ ρ : ℝ, |ρ - c| ≤ r ∧ (r / 25) ^ s.card ≤ ∏ j ∈ s, |ρ - t j| := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro s hs c r hr
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0
      rw [Finset.card_eq_zero] at hs
      subst hs
      refine ⟨c, by simp [hr.le], by simp⟩
    · obtain ⟨c', hc', h3⟩ := exists_center_near_with_few_points_close t s c r hr
      set S := s.filter (fun j => |t j - c'| < 2 * r / 5) with hSdef
      have hlt : S.card < N := by omega
      obtain ⟨ρ, hρ, hin⟩ := ih S.card hlt S rfl c' (r / 5) (by positivity)
      refine ⟨ρ, ?_, prodDist_step t s S (Finset.filter_subset _ _) h3 r ρ hr ?_ hin⟩
      · calc |ρ - c| ≤ |ρ - c'| + |c' - c| := abs_sub_le ρ c' c
          _ ≤ r / 5 + 4 * r / 5 := add_le_add hρ hc'
          _ = r := by ring
      · intro j hj hjS
        have hn : 2 * r / 5 ≤ |t j - c'| :=
          not_lt.mp (fun h => hjS (Finset.mem_filter.2 ⟨hj, h⟩))
        have htri : |t j - c'| ≤ |t j - ρ| + |ρ - c'| := abs_sub_le (t j) ρ c'
        rw [abs_sub_comm (t j) ρ] at htri
        linarith

/- English proof (translation)
The claim follows from `exists_far_from_points t s.card s rfl c r hr`.
-/
theorem prodDist {ι : Type*} [DecidableEq ι] (t : ι → ℝ) (s : Finset ι) (c r : ℝ) (hr : 0 < r) :
    ∃ ρ : ℝ, |ρ - c| ≤ r ∧ (r / 25) ^ s.card ≤ ∏ j ∈ s, |ρ - t j| :=
  exists_far_from_points t s.card s rfl c r hr

end Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
