import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.MeasureEqRelIndexMul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.RelIndexUH
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.LeviSizesMeasurable

noncomputable section

attribute [to_additive measure_eq_addRelIndex_mul] PI.IwaMeasEx.MF.measure_eq_relIndex_mul
attribute [to_additive addHaar_map_eq_addRelIndex] PI.IwaMeasEx.MF.haar_map_eq_relIndex

namespace PI.IwaMeasEx.MFI

open MeasureTheory Measure NumberField
open scoped ENNReal NNReal TensorProduct
open Formalism.MainNotions.S Formalism.L2.S.S7.GLOne PI.IwaMeasEx.Nrm

section

variable (I : AutInst)

attribute [local instance] AfT.tAf Nrm.topRing Nrm.t2 Nrm.mAf Nrm.borel_mAf

/- English proof (translation)
The claim follows from `IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup (isCompact_IntAf I) ((isOpen_IntAf I).mem_nhds (zero_mem _))`.
-/
theorem locallyCompact_AEf : LocallyCompactSpace (AEf I) :=
  IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup (isCompact_IntAf I)
    ((isOpen_IntAf I).mem_nhds (zero_mem _))

attribute [local instance] locallyCompact_AEf

def mulU (u : (AEf I)ˣ) : AEf I ≃ₜ+ AEf I where
  toFun x := (u : AEf I) * x
  invFun x := ((u⁻¹ : (AEf I)ˣ) : AEf I) * x
  left_inv x := by simp only [← mul_assoc, Units.inv_mul, one_mul]
  right_inv x := by simp only [← mul_assoc, Units.mul_inv, one_mul]
  map_add' x y := mul_add _ _ _
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mulU_apply (u : (AEf I)ˣ) (x : AEf I) : mulU I u x = (u : AEf I) * x := rfl

/- English proof (translation)
Use `set φ := mulU I u`. Use `set O := oH I`. Use `set V : AddSubgroup (AEf I) := O.comap φ.toAddEquiv.toAddMonoidHom with hV`. Establish `hOV : O ≤ V` using `fun x hx => (IntAf I.F I.E).mul_mem hu hx`. Establish `hOo : IsOpen (O : Set (AEf I))` using `isOpen_IntAf I`.

Establish `hOc : IsCompact (O : Set (AEf I))` using `isCompact_IntAf I`. Establish `hcomap : (uH I (u : AEf I)).comap φ.toAddEquiv.toAddMonoidHom = O`. Use extensionality with `x`. Use `show (u : AEf I) * x ∈ uH I (u : AEf I) ↔ x ∈ IntAf I.F I.E`. Rewrite using `[mem_uH_iff, ← mul_assoc, Units.inv_mul, one_mul]`.

Establish `hmap : V.map φ.toAddEquiv.toAddMonoidHom = O` using `AddSubgroup.map_comap_eq_self_of_surjective φ.surjective O`. Establish `hidx : O.relIndex V = (uH I (u : AEf I)).relIndex O`. Combine the equalities or inequalities in the displayed calculation. Establish `hR` using `relIndex_uH I u hu`. Establish `hpos : 0 < nrmF I u` using `nrmF_pos I u`.

Establish `hW : O ⊓ V = O` using `inf_eq_left.2 hOV`. Establish `hne : O.relIndex V ≠ 0`. Introduce `h0`. Rewrite `h0` using `[hidx]`. Rewrite `hR` using `[h0, Nat.cast_zero]`.

Conclude with `(inv_ne_zero hpos.ne') hR.symm`. Establish `h1 : (O ⊓ V).relIndex O ≠ 0` using `by rw [hW, AddSubgroup.relIndex_self]; exact one_ne_zero`. Establish `h2 : (O ⊓ V).relIndex V ≠ 0` using `by rw [hW]; exact hne`. Establish `hs` using `PI.IwaMeasEx.MF.addHaar_map_eq_addRelIndex φ O hOo hOc h1 h2`. Rewrite using `[hs, hW, AddSubgroup.relIndex_self, hidx, hR]`.

Simplify using the standard rewrite rules.
-/
theorem addHaar_map_mulU (u : (AEf I)ˣ) (hu : (u : AEf I) ∈ IntAf I.F I.E) :
    (addHaar : Measure (AEf I)).map (mulU I u) = ENNReal.ofReal (nrmF I u)⁻¹ • addHaar := by
  set φ := mulU I u
  set O := oH I
  set V : AddSubgroup (AEf I) := O.comap φ.toAddEquiv.toAddMonoidHom with hV
  have hOV : O ≤ V := fun x hx => (IntAf I.F I.E).mul_mem hu hx
  have hOo : IsOpen (O : Set (AEf I)) := isOpen_IntAf I
  have hOc : IsCompact (O : Set (AEf I)) := isCompact_IntAf I
  have hcomap : (uH I (u : AEf I)).comap φ.toAddEquiv.toAddMonoidHom = O := by
    ext x
    show (u : AEf I) * x ∈ uH I (u : AEf I) ↔ x ∈ IntAf I.F I.E
    rw [mem_uH_iff, ← mul_assoc, Units.inv_mul, one_mul]
  have hmap : V.map φ.toAddEquiv.toAddMonoidHom = O :=
    AddSubgroup.map_comap_eq_self_of_surjective φ.surjective O
  have hidx : O.relIndex V = (uH I (u : AEf I)).relIndex O := by
    calc O.relIndex V = ((uH I (u : AEf I)).comap φ.toAddEquiv.toAddMonoidHom).relIndex V := by rw [hcomap]
      _ = (uH I (u : AEf I)).relIndex (V.map φ.toAddEquiv.toAddMonoidHom) :=
        AddSubgroup.relIndex_comap _ φ.toAddEquiv.toAddMonoidHom V
      _ = (uH I (u : AEf I)).relIndex O := by rw [hmap]
  have hR := relIndex_uH I u hu
  have hpos : 0 < nrmF I u := nrmF_pos I u
  have hW : O ⊓ V = O := inf_eq_left.2 hOV
  have hne : O.relIndex V ≠ 0 := by
    intro h0
    rw [hidx] at h0
    rw [h0, Nat.cast_zero] at hR
    exact (inv_ne_zero hpos.ne') hR.symm
  have h1 : (O ⊓ V).relIndex O ≠ 0 := by rw [hW, AddSubgroup.relIndex_self]; exact one_ne_zero
  have h2 : (O ⊓ V).relIndex V ≠ 0 := by rw [hW]; exact hne
  have hs := PI.IwaMeasEx.MF.addHaar_map_eq_addRelIndex φ O hOo hOc h1 h2
  rw [hs, hW, AddSubgroup.relIndex_self, hidx, hR]
  simp

/- English proof (translation)
Establish `hc` using `addEquivAddHaarChar_smul_map (addHaar : Measure (AEf I)) (mulU I u)`. Rewrite `hc` using `[addHaar_map_mulU I u hu, ENNReal.smul_def, smul_smul]`. Take `⟨K, hK, hK0⟩` from `exists_compact_mem_nhds (0 : AEf I)`. Establish `h1 : (addHaar : Measure (AEf I)) K ≠ 0` using `((addHaar : Measure (AEf I)).measure_pos_of_mem_nhds hK0).ne'`. Establish `h2 : (addHaar : Measure (AEf I)) K ≠ ⊤` using `hK.measure_lt_top.ne`.

Establish `h3` using `congrArg (fun ν : Measure (AEf I) => ν K) hc`. Simplify using `only [Measure.smul_apply, smul_eq_mul] at h3`. Establish `h5` using `congrArg ENNReal.toReal h3`. Rewrite `h5` using `[ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal']`. Establish `hm : 0 < ((addHaar : Measure (AEf I)) K).toReal` using `ENNReal.toReal_pos h1 h2`.

Establish `h6 : (addEquivAddHaarChar (mulU I u) : ℝ) * max (nrmF I u)⁻¹ 0 = 1` using `mul_right_cancel₀ hm.ne' (h5.trans (one_mul _).symm)`. Break down `le_or_gt (nrmF I u)⁻¹ 0 with h | h` into its components or cases. Rewrite `h6` using `[max_eq_right h, mul_zero]`. Conclude with `absurd h6 zero_ne_one`. Rewrite `h6` using `[max_eq_left h.le]`.

Establish `hn : nrmF I u ≠ 0`. Introduce `h0`. Rewrite `h` using `[h0, inv_zero]`. Conclude with `lt_irrefl _ h`. Clear denominators, using `at h6` for the nonvanishing conditions.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem char_mulU_of_int (u : (AEf I)ˣ) (hu : (u : AEf I) ∈ IntAf I.F I.E) :
    (addEquivAddHaarChar (mulU I u) : ℝ) = nrmF I u := by
  have hc := addEquivAddHaarChar_smul_map (addHaar : Measure (AEf I)) (mulU I u)
  rw [addHaar_map_mulU I u hu, ENNReal.smul_def, smul_smul] at hc
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : AEf I)
  have h1 : (addHaar : Measure (AEf I)) K ≠ 0 :=
    ((addHaar : Measure (AEf I)).measure_pos_of_mem_nhds hK0).ne'
  have h2 : (addHaar : Measure (AEf I)) K ≠ ⊤ := hK.measure_lt_top.ne
  have h3 := congrArg (fun ν : Measure (AEf I) => ν K) hc
  simp only [Measure.smul_apply, smul_eq_mul] at h3
  have h5 := congrArg ENNReal.toReal h3
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal'] at h5
  have hm : 0 < ((addHaar : Measure (AEf I)) K).toReal := ENNReal.toReal_pos h1 h2
  have h6 : (addEquivAddHaarChar (mulU I u) : ℝ) * max (nrmF I u)⁻¹ 0 = 1 :=
    mul_right_cancel₀ hm.ne' (h5.trans (one_mul _).symm)
  rcases le_or_gt (nrmF I u)⁻¹ 0 with h | h
  · rw [max_eq_right h, mul_zero] at h6
    exact absurd h6 zero_ne_one
  · rw [max_eq_left h.le] at h6
    have hn : nrmF I u ≠ 0 := by
      intro h0
      rw [h0, inv_zero] at h
      exact lt_irrefl _ h
    field_simp at h6
    linarith

/- English proof (translation)
Take `⟨N, hN, hNu, -⟩` from `exists_nat_two I u`. Use `set n : (AEf I)ˣ := (AfT.isUnit_natCast I N hN).unit with hn0`. Establish `hn : (n : AEf I) = N` using `IsUnit.unit_spec _`. Establish `hnI : (n : AEf I) ∈ IntAf I.F I.E` using `by rw [hn]; exact natCast_mem _ _`. Establish `hnuI : ((n * u : (AEf I)ˣ) : AEf I) ∈ IntAf I.F I.E` using `by rw [Units.val_mul, hn]; exact hNu`.

Establish `htr : mulU I (n * u) = (mulU I u).trans (mulU I n)`. Use `ContinuousAddEquiv.ext fun x => ?_` and prove the remaining obligations. Use `show ((n * u : (AEf I)ˣ) : AEf I) * x = (n : AEf I) * ((u : AEf I) * x)`. Rewrite using `[Units.val_mul, mul_assoc]`. Establish `e1` using `char_mulU_of_int I (n * u) hnuI`.

Rewrite `e1` using `[htr, addEquivAddHaarChar_trans, NNReal.coe_mul, char_mulU_of_int I n hnI, nrmF_mul]`. Conclude with `mul_left_cancel₀ (nrmF_pos I n).ne' ((mul_comm _ _).trans e1)`.
-/
theorem char_mulU (u : (AEf I)ˣ) : (addEquivAddHaarChar (mulU I u) : ℝ) = nrmF I u := by
  obtain ⟨N, hN, hNu, -⟩ := exists_nat_two I u
  set n : (AEf I)ˣ := (AfT.isUnit_natCast I N hN).unit with hn0
  have hn : (n : AEf I) = N := IsUnit.unit_spec _
  have hnI : (n : AEf I) ∈ IntAf I.F I.E := by rw [hn]; exact natCast_mem _ _
  have hnuI : ((n * u : (AEf I)ˣ) : AEf I) ∈ IntAf I.F I.E := by rw [Units.val_mul, hn]; exact hNu
  have htr : mulU I (n * u) = (mulU I u).trans (mulU I n) := by
    refine ContinuousAddEquiv.ext fun x => ?_
    show ((n * u : (AEf I)ˣ) : AEf I) * x = (n : AEf I) * ((u : AEf I) * x)
    rw [Units.val_mul, mul_assoc]
  have e1 := char_mulU_of_int I (n * u) hnuI
  rw [htr, addEquivAddHaarChar_trans, NNReal.coe_mul, char_mulU_of_int I n hnI, nrmF_mul] at e1
  exact mul_left_cancel₀ (nrmF_pos I n).ne' ((mul_comm _ _).trans e1)

/- English proof (translation)
Establish `hc` using `addEquivAddHaarChar_smul_map (addHaar : Measure (AEf I)) (mulU I u)`. Establish `hpos` using `addEquivAddHaarChar_pos (mulU I u)`. Establish `hn` using `char_mulU I u`. Establish `hm : (addHaar : Measure (AEf I)).map (mulU I u) = (addEquivAddHaarChar (mulU I u))⁻¹ • addHaar` using `by conv_rhs => rw [← hc]`. Rewrite using `[smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]`.

Rewrite using `[hm, ← hn, ← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal]`. Use `first`. Consider the case `rfl`. Consider the case `rw [ENNReal.smul_def]`.
-/
theorem addHaar_map_mulU' (u : (AEf I)ˣ) :
    (addHaar : Measure (AEf I)).map (mulU I u) = ENNReal.ofReal (nrmF I u)⁻¹ • addHaar := by
  have hc := addEquivAddHaarChar_smul_map (addHaar : Measure (AEf I)) (mulU I u)
  have hpos := addEquivAddHaarChar_pos (mulU I u)
  have hn := char_mulU I u
  have hm : (addHaar : Measure (AEf I)).map (mulU I u) = (addEquivAddHaarChar (mulU I u))⁻¹ • addHaar := by
    conv_rhs => rw [← hc]
    rw [smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
  rw [hm, ← hn, ← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal]
  first
  | rfl
  | rw [ENNReal.smul_def]

end

end PI.IwaMeasEx.MFI

end
