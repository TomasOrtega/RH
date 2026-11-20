import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.AEConst

noncomputable section

open MeasureTheory

namespace PositivityTheory.KB.SpectralGap.UnfoldA

open PositivityTheory.KB.SpectralGap

variable {Λ S : Type} [Group Λ] [Group S]

abbrev RQ (B K : Subgroup Λ) := Quotient (QuotientGroup.rightRel (B.subgroupOf K))

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem card_Q (B K : Subgroup Λ) : Nat.card (RQ B K) = (B.subgroupOf K).index := by
  rw [Subgroup.index_eq_card]
  exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel _)

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem finite_Q (B K : Subgroup Λ) (hi : (B.subgroupOf K).index ≠ 0) : Finite (RQ B K) := by
  have h : Nat.card (RQ B K) ≠ 0 := by rw [card_Q]; exact hi
  exact (Nat.card_ne_zero.mp h).2

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem avg_eq_sum (j : Λ →* S) (B K : Subgroup Λ) [Fintype (RQ B K)] (u : S → ℝ) (x : S) :
    avg j B K u x = ((B.subgroupOf K).index : ℝ)⁻¹ *
      ∑ c : RQ B K, u (j ((c.out : K) : Λ) * x) := by
  rw [avg, finsum_eq_sum_of_fintype]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mk_eq_iff {B K : Subgroup Λ} (a b : K) :
    Quotient.mk (QuotientGroup.rightRel (B.subgroupOf K)) a = Quotient.mk _ b ↔
      (b : Λ) * (a : Λ)⁻¹ ∈ B := by
  rw [Quotient.eq]
  exact QuotientGroup.rightRel_apply.trans (by rw [Subgroup.mem_subgroupOf]; simp)

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem out_mk {B K : Subgroup Λ} (k : K) :
    (((Quotient.mk (QuotientGroup.rightRel (B.subgroupOf K)) k).out : K) : Λ) * (k : Λ)⁻¹ ∈ B := by
  have h : Quotient.mk (QuotientGroup.rightRel (B.subgroupOf K))
      (Quotient.mk (QuotientGroup.rightRel (B.subgroupOf K)) k).out = Quotient.mk _ k :=
    Quotient.out_eq _
  rw [mk_eq_iff] at h
  simpa [mul_inv_rev] using B.inv_mem h

/- English proof (translation)
Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem linv_out {j : Λ →* S} {B K : Subgroup Λ} {u : S → ℝ} (hu : LInv j B u) (k : K) (x : S) :
    u (j (((Quotient.mk (QuotientGroup.rightRel (B.subgroupOf K)) k).out : K) : Λ) * x) =
      u (j (k : Λ) * x) := by
  have h := out_mk (B := B) k
  set o : Λ := (((Quotient.mk (QuotientGroup.rightRel (B.subgroupOf K)) k).out : K) : Λ)
  calc u (j o * x) = u (j (o * (k : Λ)⁻¹) * (j (k : Λ) * x)) := by
        rw [← mul_assoc, ← map_mul, inv_mul_cancel_right]
    _ = u (j (k : Λ) * x) := hu _ h _

/- English proof (translation)
Equip the data with the indicated structure. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Introduce a local definition for the expression.

Introduce a local definition for the expression. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem avg_linv (j : Λ →* S) (B K : Subgroup Λ) (hi : (B.subgroupOf K).index ≠ 0) (u : S → ℝ)
    (hu : LInv j B u) : LInv j K (avg j B K u) := by
  haveI := finite_Q B K hi
  letI := Fintype.ofFinite (RQ B K)
  intro γ hγ x
  rw [avg_eq_sum, avg_eq_sum]
  congr 1
  let g : K := ⟨γ, hγ⟩
  let e : RQ B K ≃ RQ B K := Quotient.congr (Equiv.mulRight g) (fun a b => by
    simp only [Equiv.coe_mulRight]
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply,
      show b * g * (a * g)⁻¹ = b * a⁻¹ by group])
  refine Fintype.sum_equiv e _ _ (fun c => ?_)
  have hc : e c = Quotient.mk _ (c.out * g) := by
    conv_lhs => rw [← Quotient.out_eq c]
    exact Quotient.congr_mk _ _ _
  rw [hc, linv_out hu, Subgroup.coe_mul, map_mul, mul_assoc]

/- English proof (translation)
Equip the data with the indicated structure. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem avg_of_linv (j : Λ →* S) (B K : Subgroup Λ) (hi : (B.subgroupOf K).index ≠ 0) (u : S → ℝ)
    (hu : LInv j K u) : avg j B K u = u := by
  haveI := finite_Q B K hi
  letI := Fintype.ofFinite (RQ B K)
  funext x
  rw [avg_eq_sum]
  have h : ∀ c : RQ B K, u (j ((c.out : K) : Λ) * x) = u x := fun c => hu _ (c.out : K).2 x
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card, card_Q]
  exact inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr hi) _

/- English proof (translation)
Equip the data with the indicated structure. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem avg_meas [MeasurableSpace S] [MeasurableMul S] (j : Λ →* S) (B K : Subgroup Λ)
    (hi : (B.subgroupOf K).index ≠ 0) (u : S → ℝ) (hu : Measurable u) :
    Measurable (avg j B K u) := by
  haveI := finite_Q B K hi
  letI := Fintype.ofFinite (RQ B K)
  have h : avg j B K u = fun x => ((B.subgroupOf K).index : ℝ)⁻¹ *
      ∑ c : RQ B K, u (j ((c.out : K) : Λ) * x) := funext (avg_eq_sum j B K u)
  rw [h]
  exact measurable_const.mul
    (Finset.measurable_sum _ fun c _ => hu.comp (measurable_const_mul _))

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Equip the data with the indicated structure. Equip the data with the indicated structure.

Equip the data with the indicated structure. Introduce a local definition for the expression. Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Substitute using the available equality. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify by unfolding definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem avg_tower (j : Λ →* S) (B E K : Subgroup Λ) (hBE : B ≤ E) (hEK : E ≤ K)
    (hi : (B.subgroupOf K).index ≠ 0) (u : S → ℝ) (hu : LInv j B u) :
    avg j E K (avg j B E u) = avg j B K u := by
  have hmul : (B.subgroupOf E).index * (E.subgroupOf K).index = (B.subgroupOf K).index :=
    Subgroup.relIndex_mul_relIndex B E K hBE hEK
  have hBEi : (B.subgroupOf E).index ≠ 0 := fun h => hi (by rw [← hmul, h, zero_mul])
  have hEKi : (E.subgroupOf K).index ≠ 0 := fun h => hi (by rw [← hmul, h, mul_zero])
  haveI := finite_Q B K hi
  haveI := finite_Q B E hBEi
  haveI := finite_Q E K hEKi
  letI := Fintype.ofFinite (RQ B K)
  letI := Fintype.ofFinite (RQ B E)
  letI := Fintype.ofFinite (RQ E K)
  let φ : RQ E K × RQ B E → RQ B K := fun p => Quotient.mk _
    (⟨((p.2.out : E) : Λ) * ((p.1.out : K) : Λ), K.mul_mem (hEK (p.2.out : E).2) (p.1.out : K).2⟩ : K)
  have hinj : Function.Injective φ := by
    rintro ⟨c, d⟩ ⟨c', d'⟩ h
    have h1 := (mk_eq_iff _ _).mp h
    simp only at h1
    have hc : c = c' := by
      rw [← Quotient.out_eq c, ← Quotient.out_eq c', mk_eq_iff]
      have : ((c'.out : K) : Λ) * ((c.out : K) : Λ)⁻¹ = ((d'.out : E) : Λ)⁻¹ *
          ((((d'.out : E) : Λ) * ((c'.out : K) : Λ)) * (((d.out : E) : Λ) * ((c.out : K) : Λ))⁻¹) *
          ((d.out : E) : Λ) := by group
      rw [this]
      exact E.mul_mem (E.mul_mem (E.inv_mem (d'.out : E).2) (hBE h1)) (d.out : E).2
    subst hc
    have hd : d = d' := by
      rw [← Quotient.out_eq d, ← Quotient.out_eq d', mk_eq_iff]
      have : ((d'.out : E) : Λ) * ((d.out : E) : Λ)⁻¹ =
          (((d'.out : E) : Λ) * ((c.out : K) : Λ)) * (((d.out : E) : Λ) * ((c.out : K) : Λ))⁻¹ := by
        group
      rw [this]; exact h1
    rw [hd]
  have hcard : Fintype.card (RQ E K × RQ B E) = Fintype.card (RQ B K) := by
    rw [Fintype.card_prod, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card, card_Q, card_Q, card_Q, ← hmul, mul_comm]
  have hbij : Function.Bijective φ := (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard⟩
  funext x
  rw [avg_eq_sum j E K, avg_eq_sum j B K]
  simp_rw [avg_eq_sum j B E u]
  have hs : ∑ q : RQ B K, u (j ((q.out : K) : Λ) * x) =
      ∑ c : RQ E K, ∑ d : RQ B E, u (j ((d.out : E) : Λ) * (j ((c.out : K) : Λ) * x)) := by
    rw [← Fintype.sum_prod_type']
    refine (Fintype.sum_bijective φ hbij _ _ (fun p => ?_)).symm
    simp only [φ]
    rw [linv_out hu]
    dsimp only
    rw [map_mul, mul_assoc]
  rw [hs, ← Finset.mul_sum, ← hmul, Nat.cast_mul]
  ring

end PositivityTheory.KB.SpectralGap.UnfoldA

end
