import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.AEConst

noncomputable section

open MeasureTheory

namespace PositivityTheory.KB.SpectralGap.PGap

variable {Λ S : Type} [Group Λ] [Group S] (j : Λ →* S)

/- English proof (translation)
Introduce `γ hγ x` and use `hu γ (h hγ) x`.
-/
theorem linv_mono {E E' : Subgroup Λ} (h : E ≤ E') {u : S → ℝ} (hu : LInv j E' u) : LInv j E u :=
  fun γ hγ x => hu γ (h hγ) x

/- English proof (translation)
Introduce `γ hγ x`. Simplify using `only [hu γ hγ x, hv γ hγ x]`.
-/
theorem linv_sub {E : Subgroup Λ} {u v : S → ℝ} (hu : LInv j E u) (hv : LInv j E v) :
    LInv j E (fun x => u x - v x) := by
  intro γ hγ x
  simp only [hu γ hγ x, hv γ hγ x]

/- English proof (translation)
Introduce `γ hγ x`. Simplify using `only [hu γ hγ x, hv γ hγ x]`.
-/
theorem linv_mul {E : Subgroup Λ} {u v : S → ℝ} (hu : LInv j E u) (hv : LInv j E v) :
    LInv j E (fun x => u x * v x) := by
  intro γ hγ x
  simp only [hu γ hγ x, hv γ hγ x]

/- English proof (translation)
Introduce `γ hγ x`. Simplify using `only [hu γ hγ x]`.
-/
theorem linv_sq {E : Subgroup Λ} {u : S → ℝ} (hu : LInv j E u) : LInv j E (fun x => u x ^ 2) := by
  intro γ hγ x
  simp only [hu γ hγ x]

variable {B K : Subgroup Λ}

/- English proof (translation)
Rewrite using `[Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel (B.subgroupOf K))]`. Both sides reduce to the same expression.
-/
theorem card_cosets :
    Nat.card (Quotient (QuotientGroup.rightRel (B.subgroupOf K))) = (B.subgroupOf K).index := by
  rw [Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel (B.subgroupOf K))]
  rfl

/- English proof (translation)
The claim follows from `Nat.finite_of_card_ne_zero (by rw [card_cosets]; exact h)`.
-/
theorem finite_cosets (h : (B.subgroupOf K).index ≠ 0) :
    Finite (Quotient (QuotientGroup.rightRel (B.subgroupOf K))) :=
  Nat.finite_of_card_ne_zero (by rw [card_cosets]; exact h)

/- English proof (translation)
Use `haveI := finite_cosets (B := B) (K := K) h`. Use `letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel (B.subgroupOf K)))`. Simplify using `only [avg, finsum_eq_sum_of_fintype, Finset.sum_sub_distrib, mul_sub]`.
-/
theorem avg_sub (h : (B.subgroupOf K).index ≠ 0) (u v : S → ℝ) (x : S) :
    avg j B K (fun y => u y - v y) x = avg j B K u x - avg j B K v x := by
  haveI := finite_cosets (B := B) (K := K) h
  letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel (B.subgroupOf K)))
  simp only [avg, finsum_eq_sum_of_fintype, Finset.sum_sub_distrib, mul_sub]

/- English proof (translation)
Distinguish the cases in `h : (B.subgroupOf K).index = 0`. Simplify using `[avg, h]`. Use `haveI := finite_cosets (B := B) (K := K) h`. Use `letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel (B.subgroupOf K)))`. Simplify using `only [avg, finsum_eq_sum_of_fintype]`.

Establish `hc : ∀ c : Quotient (QuotientGroup.rightRel (B.subgroupOf K)), a (j (c.out : Λ) * x) * b (j (c.out : Λ) * x) = a x * b (j (c.out : Λ) * x)`. Introduce `c`. Rewrite using `[ha _ c.out.2 x]`. Simplify using `only [hc, ← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem avg_mul_left {a : S → ℝ} (ha : LInv j K a) (b : S → ℝ) (x : S) :
    avg j B K (fun y => a y * b y) x = a x * avg j B K b x := by
  by_cases h : (B.subgroupOf K).index = 0
  · simp [avg, h]
  haveI := finite_cosets (B := B) (K := K) h
  letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel (B.subgroupOf K)))
  simp only [avg, finsum_eq_sum_of_fintype]
  have hc : ∀ c : Quotient (QuotientGroup.rightRel (B.subgroupOf K)),
      a (j (c.out : Λ) * x) * b (j (c.out : Λ) * x) = a x * b (j (c.out : Λ) * x) := by
    intro c
    rw [ha _ c.out.2 x]
  simp only [hc, ← Finset.mul_sum]
  ring

/- English proof (translation)
Unfold `avg`. Apply `mul_nonneg` to reduce the goal to its premises. Check the signs of the components of the expression. Conclude with `finsum_nonneg fun c => hu _`.
-/
theorem avg_nonneg {u : S → ℝ} (hu : ∀ y, 0 ≤ u y) (x : S) : 0 ≤ avg j B K u x := by
  unfold avg
  apply mul_nonneg
  · positivity
  · exact finsum_nonneg fun c => hu _

/- English proof (translation)
Use `haveI := finite_cosets (B := B) (K := K) h`. Use `letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel (B.subgroupOf K)))`. Establish `hc : (Finset.univ : Finset (Quotient (QuotientGroup.rightRel (B.subgroupOf K)))).card = (B.subgroupOf K).index`. Rewrite using `[Finset.card_univ, ← Nat.card_eq_fintype_card, card_cosets]`. Establish `hn : (0 : ℝ) < (B.subgroupOf K).index` using `by exact_mod_cast Nat.pos_of_ne_zero h`.

Simplify using `only [avg, finsum_eq_sum_of_fintype]`. Establish `key` using `sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun c : Quotient (QuotientGroup.rightRel (B.subgroupOf K)) => u (j (c.out : Λ) * x))`. Rewrite `key` using `[hc]`. Use `set n : ℝ := ((B.subgroupOf K).index : ℝ) with hn_def`. Use `set s := ∑ c : Quotient (QuotientGroup.rightRel (B.subgroupOf K)), u (j (c.out : Λ) * x)`.

Use `set t := ∑ c : Quotient (QuotientGroup.rightRel (B.subgroupOf K)), u (j (c.out : Λ) * x) ^ 2`. Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts.
-/
theorem avg_sq_le (h : (B.subgroupOf K).index ≠ 0) (u : S → ℝ) (x : S) :
    avg j B K u x ^ 2 ≤ avg j B K (fun y => u y ^ 2) x := by
  haveI := finite_cosets (B := B) (K := K) h
  letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel (B.subgroupOf K)))
  have hc : (Finset.univ : Finset (Quotient (QuotientGroup.rightRel (B.subgroupOf K)))).card
      = (B.subgroupOf K).index := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, card_cosets]
  have hn : (0 : ℝ) < (B.subgroupOf K).index := by exact_mod_cast Nat.pos_of_ne_zero h
  simp only [avg, finsum_eq_sum_of_fintype]
  have key := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun c : Quotient (QuotientGroup.rightRel (B.subgroupOf K)) => u (j (c.out : Λ) * x))
  rw [hc] at key
  set n : ℝ := ((B.subgroupOf K).index : ℝ) with hn_def
  set s := ∑ c : Quotient (QuotientGroup.rightRel (B.subgroupOf K)), u (j (c.out : Λ) * x)
  set t := ∑ c : Quotient (QuotientGroup.rightRel (B.subgroupOf K)), u (j (c.out : Λ) * x) ^ 2
  calc (n⁻¹ * s) ^ 2 = n⁻¹ ^ 2 * s ^ 2 := by ring
    _ ≤ n⁻¹ ^ 2 * (n * t) := by gcongr
    _ = n⁻¹ * t := by
      field_simp

end PositivityTheory.KB.SpectralGap.PGap

end
