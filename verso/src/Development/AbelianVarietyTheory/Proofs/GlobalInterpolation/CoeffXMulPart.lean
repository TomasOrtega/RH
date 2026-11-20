import Mathlib

namespace GlobalTheory.PowerSeriesCoeffSum

open MvPowerSeries Finsupp

variable {O : Type} [CommRing O] {a : ℕ}

noncomputable def part (f : MvPowerSeries (Fin a) O) (i : Fin a) : MvPowerSeries (Fin a) O :=
  fun e => if (∀ j < i, e j = 0) then coeff (e + single i 1) f else 0

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma coeff_part (f : MvPowerSeries (Fin a) O) (i : Fin a) (e : Fin a →₀ ℕ) :
    coeff e (part f i) = if (∀ j < i, e j = 0) then coeff (e + single i 1) f else 0 := rfl

/- English proof (translation)
Rewrite using `[X, coeff_monomial_mul, one_mul]`. Distinguish the cases in `h1 : 1 ≤ m i`. Establish `hle : single i 1 ≤ m`. Introduce `k`. Distinguish the cases in `hk : k = i`.

Substitute `hk` using the available equality. Simplify using `using h1`. Simplify using `[single_apply, Ne.symm hk]`. Rewrite using `[if_pos hle, coeff_part, tsub_add_cancel_of_le hle]`. Establish `: (∀ j < i, (m - single i 1 : Fin a →₀ ℕ) j = 0) ↔ (∀ j < i, m j = 0)`.

Use `forall_congr' fun j => imp_congr_right fun hj => ?_` and prove the remaining obligations. Establish `: j ≠ i` using `ne_of_lt hj`. Simplify using `[single_apply, Ne.symm this]`. Simplify using `only [this, h1, true_and]`. Establish `hle : ¬ single i 1 ≤ m`.

Introduce `h; exact h1 (by simpa using h i)`. Simplify using `[hle, h1]`.
-/
lemma coeff_X_mul_part (f : MvPowerSeries (Fin a) O) (i : Fin a) (m : Fin a →₀ ℕ) :
    coeff m (X i * part f i) = if (1 ≤ m i ∧ ∀ j < i, m j = 0) then coeff m f else 0 := by
  rw [X, coeff_monomial_mul, one_mul]
  by_cases h1 : 1 ≤ m i
  · have hle : single i 1 ≤ m := by
      intro k
      by_cases hk : k = i
      · subst hk; simpa using h1
      · simp [single_apply, Ne.symm hk]
    rw [if_pos hle, coeff_part, tsub_add_cancel_of_le hle]
    have : (∀ j < i, (m - single i 1 : Fin a →₀ ℕ) j = 0) ↔ (∀ j < i, m j = 0) := by
      refine forall_congr' fun j => imp_congr_right fun hj => ?_
      have : j ≠ i := ne_of_lt hj
      simp [single_apply, Ne.symm this]
    simp only [this, h1, true_and]
  · have hle : ¬ single i 1 ≤ m := by
      intro h; exact h1 (by simpa using h i)
    simp [hle, h1]

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[map_sum]`. Simplify using `only [coeff_X_mul_part]`. Distinguish the cases in `hm : m = 0`. Substitute `hm` using the available equality.

Simplify using `[h0]`. Establish `hne : m.support.Nonempty` using `Finsupp.support_nonempty_iff.mpr hm set i0 := m.support.min' hne with hi0`. Establish `hi0mem : i0 ∈ m.support` using `Finset.min'_mem _ _`. Establish `key : ∀ i, (1 ≤ m i ∧ ∀ j < i, m j = 0) ↔ i = i0`. Introduce `i`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Apply `le_antisymm` to reduce the goal to its premises. Assume the negation of the conclusion as `hlt push_neg at hlt`. Conclude with `(Finsupp.mem_support_iff.mp hi0mem) (h2 _ hlt)`.

Conclude with `Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr (by omega))`. Introduce and unpack `rfl`. Use `⟨Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi0mem), fun j hj => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hj0`. Conclude with `absurd (Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr hj0)) (not_le.mpr hj)`.

Simplify using `only [key]`. Simplify using the standard rewrite rules.
-/
lemma eq_sum (f : MvPowerSeries (Fin a) O) (h0 : coeff 0 f = 0) :
    f = ∑ i, X i * part f i := by
  ext m
  rw [map_sum]
  simp only [coeff_X_mul_part]
  by_cases hm : m = 0
  · subst hm; simp [h0]
  · have hne : m.support.Nonempty := Finsupp.support_nonempty_iff.mpr hm
    set i0 := m.support.min' hne with hi0
    have hi0mem : i0 ∈ m.support := Finset.min'_mem _ _
    have key : ∀ i, (1 ≤ m i ∧ ∀ j < i, m j = 0) ↔ i = i0 := by
      intro i
      constructor
      · rintro ⟨h1, h2⟩
        apply le_antisymm
        · by_contra hlt
          push_neg at hlt
          exact (Finsupp.mem_support_iff.mp hi0mem) (h2 _ hlt)
        · exact Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr (by omega))
      · rintro rfl
        refine ⟨Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi0mem), fun j hj => ?_⟩
        by_contra hj0
        exact absurd (Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr hj0)) (not_le.mpr hj)
    simp only [key]
    simp

/- English proof (translation)
Introduce `O _ a n`. Proceed by induction on `n with`. Consider the case `zero => intro f _`. Simplify using the standard rewrite rules. Consider the case `succ n ih`.

Introduce `f hf`. Establish `h0 : coeff 0 f = 0` using `hf 0 (by simp)`. Rewrite using `[eq_sum f h0, pow_succ']`. Use `Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩) (ih _ ?_)` and prove the remaining obligations. Introduce `e he`.

Rewrite using `[coeff_part]`. Use `split_ifs`. Apply `hf` to reduce the goal to its premises. Rewrite using `[map_add, degree_single]`. Use linear arithmetic over natural numbers and integers.

Both sides reduce to the same expression.
-/
theorem main : ∀ (O : Type) [inst : CommRing O] (a n : ℕ) (f : MvPowerSeries (Fin a) O),
    (∀ (m : Fin a →₀ ℕ), (Finsupp.degree : (Fin a →₀ ℕ) → ℕ) m < n →
      (MvPowerSeries.coeff m : MvPowerSeries (Fin a) O → O) f = (0 : O)) →
    f ∈ Ideal.span (Set.range MvPowerSeries.X) ^ n := by
  intro O _ a n
  induction n with
  | zero => intro f _; simp
  | succ n ih =>
    intro f hf
    have h0 : coeff 0 f = 0 := hf 0 (by simp)
    rw [eq_sum f h0, pow_succ']
    refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩) (ih _ ?_)
    intro e he
    rw [coeff_part]
    split_ifs
    · apply hf
      rw [map_add, degree_single]; omega
    · rfl

end GlobalTheory.PowerSeriesCoeffSum
