import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem complete_of_sq {R : Type} [CommRing R] (I : Ideal R) (h : I ^ 2 = ⊥) :
    IsAdicComplete I R := by
  have h0 : ∀ x : R, x ∈ (I ^ 2 • ⊤ : Submodule R R) → x = 0 := by
    intro x hx
    rw [Ideal.smul_eq_mul, Ideal.mul_top, h] at hx
    exact (Submodule.mem_bot R).mp hx
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have hx2 := hx 2
    rw [SModEq.sub_mem, sub_zero] at hx2
    exact h0 x hx2
  · intro f hf
    refine ⟨f 2, fun n => ?_⟩
    rcases le_or_gt 2 n with hn | hn
    · have hfn := hf hn
      rw [SModEq.sub_mem] at hfn
      have e : f 2 = f n := sub_eq_zero.mp (h0 _ hfn)
      rw [SModEq.sub_mem, e, sub_self]
      exact Submodule.zero_mem _
    · exact hf hn.le

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Alg.co_res :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], IsCO O (ResidueField O) ∧ IsCO O (DualNumber (ResidueField O)) := by
  intro O _ _
  constructor
  · refine IsCO.mk ?_ ?_ ?_
    · apply complete_of_sq
      rw [maximalIdeal_eq_bot, pow_two, Ideal.bot_mul]
    · show IsLocalHom (residue O)
      infer_instance
    · intro x
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x
      refine ⟨a, ?_⟩
      have h : x - algebraMap O (ResidueField O) a = 0 := sub_eq_zero.mpr ha.symm
      rw [h]
      exact zero_mem _
  · have hm : ∀ x : DualNumber (ResidueField O), x ∈ maximalIdeal _ ↔ x.fst = 0 := by
      intro x
      rw [mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero,
        not_not]
    have hfst : ∀ a : O, (algebraMap O (DualNumber (ResidueField O)) a).fst =
        algebraMap O (ResidueField O) a :=
      fun a => (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).commutes a
    refine IsCO.mk ?_ ?_ ?_
    · apply complete_of_sq
      rw [pow_two]
      refine le_bot_iff.mp (Ideal.mul_le.mpr fun r hr s hs => ?_)
      rw [hm] at hr hs
      refine Ideal.mem_bot.mpr (TrivSqZeroExt.ext ?_ ?_) <;> simp [hr, hs]
    · refine ⟨fun a ha => ?_⟩
      have h1 := ha.map (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O))
      rw [(TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).commutes] at h1
      exact isUnit_of_map_unit (residue O) a h1
    · intro x
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x.fst
      refine ⟨a, ?_⟩
      rw [hm, TrivSqZeroExt.fst_sub, hfst]
      exact sub_eq_zero.mpr ha.symm
