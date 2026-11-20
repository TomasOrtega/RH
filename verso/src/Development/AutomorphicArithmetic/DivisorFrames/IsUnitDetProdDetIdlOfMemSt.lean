import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemLevelOfThetaDatumNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetIdlVal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdemSumMulOfSubset
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Proceed by induction on `Z using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, ih fun i hi j hj hij => ho i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij]`. Establish `h0 : es a * ∑ w ∈ s, es w = 0`.

Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_eq_zero fun j hj => ho a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj) fun h => ha (h ▸ hj)`. Take the linear combination `(d - 1) ^ 2 * h0`.
-/
private theorem prod_orthogonal_idempotents {R ι : Type} [CommRing R] [DecidableEq ι] (d : R) (es : ι → R) (Z : Finset ι)
    (ho : ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j → es i * es j = 0) :
    ∏ w ∈ Z, (es w * d + (1 - es w)) = (∑ w ∈ Z, es w) * d + (1 - ∑ w ∈ Z, es w) := by
  induction Z using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ih fun i hi j hj hij => ho i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij]
    have h0 : es a * ∑ w ∈ s, es w = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun j hj =>
        ho a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj) fun h => ha (h ▸ hj)
    linear_combination (d - 1) ^ 2 * h0

/- English proof (translation)
Establish `h1 : f ((x⁻¹ : Aˣ) : A) * f (x : A) = 1` using `by rw [← map_mul, Units.inv_mul, map_one]`. Establish `h2 : f (x : A) * (1 - ε + ε * d') = 1`. Rewrite using `[hx]`. Take the linear combination `(1 - d - d' + d * d') * hε + ε * hd`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem inv_aux {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : Aˣ) (ε d d' : B)
    (hε : ε * ε = ε) (hd : d * d' = 1) (hx : f (x : A) = 1 - ε + ε * d) :
    f ((x⁻¹ : Aˣ) : A) = 1 - ε + ε * d' := by
  have h1 : f ((x⁻¹ : Aˣ) : A) * f (x : A) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have h2 : f (x : A) * (1 - ε + ε * d') = 1 := by
    rw [hx]; linear_combination (1 - d - d' + d * d') * hε + ε * hd
  calc f ((x⁻¹ : Aˣ) : A) = f ((x⁻¹ : Aˣ) : A) * (f (x : A) * (1 - ε + ε * d')) := by rw [h2, mul_one]
    _ = _ := by rw [← mul_assoc, h1, one_mul]

/- English proof (translation)
Rewrite using `[Units.val_mul, Units.val_mul, Matrix.det_units_conj']`.
-/
private theorem det_conj_eq {n : ℕ} {B : Type} [CommRing B] (β γ : GL (Fin n) B) :
    (β⁻¹ * γ * β : GL (Fin n) B).val.det = γ.val.det := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj']

/- English proof (translation)
Introduce `D S βS e Z hZ g hg`. Establish `hinf` using `GlobalTheory.PlaceDatum.infPart_idemSum hZ`. Establish `hint` using `StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem hZ`. Establish `hee : e * e = e` using `GlobalTheory.Tow.idemSum_mul_of_subset hZ hZ (Finset.Subset.refl Z)`. Take `⟨⟨es, hes, hsum⟩, -⟩` from `hZ`.

Establish `hid : ∀ w ∈ Z, GlobalTheory.RowVacScalar.idemAt w = es w` using `fun w hw => GlobalTheory.Tow.idemAt_unique (Classical.epsilon_spec (p := fun a : AE D => Formalism.L2.NTheta.IsIdemAt a w) ⟨es w, hes w hw⟩) (hes w hw)`. Establish `hval : ((∏ w ∈ Z, GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) S g : (AE D)ˣ) : AE D) = e * (Formalism.L2.Theta.mt S g).det + (1 - e)`. Rewrite using `[Units.coe_prod, hsum, ← prod_orthogonal_idempotents _ es Z fun i hi j hj hij => GlobalTheory.Tow.idemAt_orth (hes i hi) (hes j hj) hij]`. Use `Finset.prod_congr rfl fun w hw => ?_` and prove the remaining obligations. Rewrite using `[hid w hw, GlobalTheory.RowVacScalar.detIdl_val (hes w hw).1.1]`.

Establish `hdet : toEAf D (Formalism.L2.Theta.mt S g).det = (Lev.finE S g).val.det`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression. Establish `h2 : toEAf D ((∏ w ∈ Z, GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) S g : (AE D)ˣ) : AE D) = 1 - toEAf D e + toEAf D e * (βS⁻¹ * Lev.finE S g * βS : GL (Fin S.rank) (Lev.EAf D)).val.det`. Rewrite using `[hval, det_conj_eq, map_add, map_mul, map_sub, map_one, hdet, add_comm]`.

Use `⟨?_, h2, ?_⟩` and prove the remaining obligations. Rewrite using `[hval, map_add, map_mul, map_sub, map_one, hinf, zero_mul, zero_add, sub_zero]`. Take `⟨z, hz⟩` from `hg`. Establish `hz' : (βS⁻¹ * Lev.finE S g * βS : GL (Fin S.rank) (Lev.EAf D)) = Formalism.L2.DIV.intGL _ _ _ z`. Rewrite using `[← hz]`.

Use `show βS⁻¹ * (βS * Formalism.L2.DIV.intGL _ _ _ z * βS⁻¹) * βS = _`. Use `group`. Establish `hzd : (βS⁻¹ * Lev.finE S g * βS : GL (Fin S.rank) (Lev.EAf D)).val.det = (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype z.val.det`. Rewrite using `[hz', RingHom.map_det]`. Both sides reduce to the same expression.

Establish `hd : (βS⁻¹ * Lev.finE S g * βS : GL (Fin S.rank) (Lev.EAf D)).val.det * (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype (z⁻¹).val.det = 1`. Rewrite using `[hzd, ← map_mul, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, map_one]`. Rewrite using `[inv_aux (toEAf D) _ _ _ _ (by rw [← map_mul, hee]) hd h2]`. Conclude with `add_mem (sub_mem (one_mem _) hint) (mul_mem hint (z⁻¹).val.det.2)`.
-/
theorem UpperTheory.isUnitDet_prod_detIdl_of_mem_St :
    ∀ (D : D7) (S : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (e : AE D) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)),
      IsIdemSum e Z → ∀ g : GA D S, Lev.finE S g ∈ Formalism.L2.DIV.St βS →
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.IsUnitDet e (βS⁻¹ * Lev.finE S g * βS : GL (Fin S.rank) (Lev.EAf D)).val
        (∏ w ∈ Z, GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) S g) := by
  classical
  intro D S βS e Z hZ g hg
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum hZ
  have hint := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem hZ
  have hee : e * e = e := GlobalTheory.Tow.idemSum_mul_of_subset hZ hZ (Finset.Subset.refl Z)
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := hZ
  have hid : ∀ w ∈ Z, GlobalTheory.RowVacScalar.idemAt w = es w := fun w hw =>
    GlobalTheory.Tow.idemAt_unique
      (Classical.epsilon_spec (p := fun a : AE D => Formalism.L2.NTheta.IsIdemAt a w) ⟨es w, hes w hw⟩) (hes w hw)
  have hval : ((∏ w ∈ Z, GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) S g : (AE D)ˣ) : AE D)
      = e * (Formalism.L2.Theta.mt S g).det + (1 - e) := by
    rw [Units.coe_prod, hsum, ← prod_orthogonal_idempotents _ es Z fun i hi j hj hij => GlobalTheory.Tow.idemAt_orth (hes i hi) (hes j hj) hij]
    refine Finset.prod_congr rfl fun w hw => ?_
    rw [hid w hw, GlobalTheory.RowVacScalar.detIdl_val (hes w hw).1.1]
  have hdet : toEAf D (Formalism.L2.Theta.mt S g).det = (Lev.finE S g).val.det := by
    rw [RingHom.map_det]; rfl
  have h2 : toEAf D ((∏ w ∈ Z, GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) S g : (AE D)ˣ) : AE D)
      = 1 - toEAf D e + toEAf D e * (βS⁻¹ * Lev.finE S g * βS : GL (Fin S.rank) (Lev.EAf D)).val.det := by
    rw [hval, det_conj_eq, map_add, map_mul, map_sub, map_one, hdet, add_comm]
  refine ⟨?_, h2, ?_⟩
  · rw [hval, map_add, map_mul, map_sub, map_one, hinf, zero_mul, zero_add, sub_zero]
  · obtain ⟨z, hz⟩ := hg
    have hz' : (βS⁻¹ * Lev.finE S g * βS : GL (Fin S.rank) (Lev.EAf D)) = Formalism.L2.DIV.intGL _ _ _ z := by
      rw [← hz]
      show βS⁻¹ * (βS * Formalism.L2.DIV.intGL _ _ _ z * βS⁻¹) * βS = _
      group
    have hzd : (βS⁻¹ * Lev.finE S g * βS : GL (Fin S.rank) (Lev.EAf D)).val.det
        = (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype z.val.det := by
      rw [hz', RingHom.map_det]; rfl
    have hd : (βS⁻¹ * Lev.finE S g * βS : GL (Fin S.rank) (Lev.EAf D)).val.det *
        (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype (z⁻¹).val.det = 1 := by
      rw [hzd, ← map_mul, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, map_one]
    rw [inv_aux (toEAf D) _ _ _ _ (by rw [← map_mul, hee]) hd h2]
    exact add_mem (sub_mem (one_mem _) hint) (mul_mem hint (z⁻¹).val.det.2)
