import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.AEConst

noncomputable section

open MeasureTheory

namespace PositivityTheory.KB.SpectralGap.PGap

variable {Λ S : Type} [Group Λ] [Group S] (j : Λ →* S)

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem linv_mono {E E' : Subgroup Λ} (h : E ≤ E') {u : S → ℝ} (hu : LInv j E' u) : LInv j E u :=
  fun γ hγ x => hu γ (h hγ) x

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.
-/
theorem linv_sub {E : Subgroup Λ} {u v : S → ℝ} (hu : LInv j E u) (hv : LInv j E v) :
    LInv j E (fun x => u x - v x) := by
  intro γ hγ x
  simp only [hu γ hγ x, hv γ hγ x]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.
-/
theorem linv_mul {E : Subgroup Λ} {u v : S → ℝ} (hu : LInv j E u) (hv : LInv j E v) :
    LInv j E (fun x => u x * v x) := by
  intro γ hγ x
  simp only [hu γ hγ x, hv γ hγ x]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.
-/
theorem linv_sq {E : Subgroup Λ} {u : S → ℝ} (hu : LInv j E u) : LInv j E (fun x => u x ^ 2) := by
  intro γ hγ x
  simp only [hu γ hγ x]

variable {B K : Subgroup Λ}

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem card_cosets :
    Nat.card (Quotient (QuotientGroup.rightRel (B.subgroupOf K))) = (B.subgroupOf K).index := by
  rw [Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel (B.subgroupOf K))]
  rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finite_cosets (h : (B.subgroupOf K).index ≠ 0) :
    Finite (Quotient (QuotientGroup.rightRel (B.subgroupOf K))) :=
  Nat.finite_of_card_ne_zero (by rw [card_cosets]; exact h)

/- English proof (translation)
Equip the data with the indicated structure. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem avg_sub (h : (B.subgroupOf K).index ≠ 0) (u v : S → ℝ) (x : S) :
    avg j B K (fun y => u y - v y) x = avg j B K u x - avg j B K v x := by
  haveI := finite_cosets (B := B) (K := K) h
  letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel (B.subgroupOf K)))
  simp only [avg, finsum_eq_sum_of_fintype, Finset.sum_sub_distrib, mul_sub]

/- English proof (translation)
Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Equip the data with the indicated structure. Simplify using the standard rewrite rules. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
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
Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Check the signs of the components of the expression. A detailed English derivation is pending.
-/
theorem avg_nonneg {u : S → ℝ} (hu : ∀ y, 0 ≤ u y) (x : S) : 0 ≤ avg j B K u x := by
  unfold avg
  apply mul_nonneg
  · positivity
  · exact finsum_nonneg fun c => hu _

/- English proof (translation)
Equip the data with the indicated structure. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Chain the equalities or inequalities of the calculation. Clear the denominators using the available nonvanishing facts. A detailed English derivation is pending.
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
