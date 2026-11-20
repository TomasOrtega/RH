import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralActionUnitCharacterEigen

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

noncomputable section

namespace GlobalTheory.StdRead.CharMul

variable {D : D7}

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Use `Subring.sum_mem _ fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Units.smul_def]`. Conclude with `Subring.zsmul_mem _ (Subring.prod_mem _ fun i _ => h (σ i) i) _`.
-/
theorem det_int {n : ℕ} {N : Matrix (Fin n) (Fin n) (EAf D)} (h : IsIntM N) :
    N.det ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  rw [Matrix.det_apply]
  refine Subring.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  exact Subring.zsmul_mem _ (Subring.prod_mem _ fun i _ => h (σ i) i) _

/- English proof (translation)
Take the linear combination `(1 - a - b + a * b) * h`.
-/
theorem ring_mul {R : Type} [CommRing R] {ε : R} (h : ε * ε = ε) (a b : R) :
    (1 - ε + ε * a) * (1 - ε + ε * b) = 1 - ε + ε * (a * b) := by
  linear_combination (1 - a - b + a * b) * h

/- English proof (translation)
The claim follows from `Matrix.det_mul A B`.
-/
theorem det_mul' {R : Type} [CommRing R] {k : ℕ} (A B : Matrix (Fin k) (Fin k) R) :
    (HMul.hMul A B).det = A.det * B.det :=
  Matrix.det_mul A B

/- English proof (translation)
Rewrite using `[← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]`.
-/
theorem det_gl {R : Type} [CommRing R] {k : ℕ} (β : GL (Fin k) R) : β.val.det * (β⁻¹).val.det = 1 := by
  rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]

/- English proof (translation)
Take `⟨hx1, hx2, hx3⟩` from `hx`. Take `⟨hy1, hy2, hy3⟩` from `hy`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, map_mul, hx1, hy1, one_mul]`. Rewrite using `[Units.val_mul, map_mul, hx2, hy2, h]`.

Conclude with `ring_mul (by rw [← map_mul, he]) _ _`. Rewrite using `[mul_inv_rev, Units.val_mul, map_mul]`. Conclude with `Subring.mul_mem _ hy3 hx3`.
-/
theorem isUnitDet_mul {e : AE D} (he : e * e = e) {k : ℕ} {A B C : Matrix (Fin k) (Fin k) (EAf D)}
    (h : C.det = A.det * B.det) {x y : (AE D)ˣ} (hx : IsUnitDet e A x) (hy : IsUnitDet e B y) :
    IsUnitDet e C (x * y) := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  refine ⟨?_, ?_, ?_⟩
  · rw [Units.val_mul, map_mul, hx1, hy1, one_mul]
  · rw [Units.val_mul, map_mul, hx2, hy2, h]
    exact ring_mul (by rw [← map_mul, he]) _ _
  · rw [mul_inv_rev, Units.val_mul, map_mul]
    exact Subring.mul_mem _ hy3 hx3

/- English proof (translation)
Use `⟨((Algebra.TensorProduct.comm D.host.F (AF D.host.F) D.host.E).trans (Algebra.TensorProduct.prodRight D.host.F D.host.F D.host.E (Ainf D.host.F) (Af D.host.F))).toRingEquiv, fun z => ?_⟩` and prove the remaining obligations. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => exact ⟨rfl, rfl⟩`. Consider the case `add z z' h1 h2`.

Prove the components needed by the constructor for the conclusion. Simplify using `only [map_add, Prod.fst_add, h1.1, h2.1]`. Simplify using `only [map_add, Prod.snd_add, h1.2, h2.2]`.
-/
private lemma eq_lr_take_drop_of_map_fst_eq_replicate {D : D7} : ∃ Ψ : AE D ≃+* (TensorProduct D.host.F D.host.E (Ainf D.host.F)) × EAf D,
    ∀ z, infPart D z = Algebra.TensorProduct.comm D.host.F D.host.E (Ainf D.host.F) (Ψ z).1 ∧
      toEAf D z = (Ψ z).2 := by
  refine ⟨((Algebra.TensorProduct.comm D.host.F (AF D.host.F) D.host.E).trans
    (Algebra.TensorProduct.prodRight D.host.F D.host.F D.host.E (Ainf D.host.F) (Af D.host.F))).toRingEquiv,
    fun z => ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => exact ⟨rfl, rfl⟩
  | add z z' h1 h2 =>
    constructor
    · simp only [map_add, Prod.fst_add, h1.1, h2.1]
    · simp only [map_add, Prod.snd_add, h1.2, h2.2]

/- English proof (translation)
Take `⟨Ψ, hΨ⟩` from `eq_lr_take_drop_of_map_fst_eq_replicate (D := D)`. Apply `Ψ.injective` to reduce the goal to its premises. Use `Prod.ext ((Algebra.TensorProduct.comm D.host.F D.host.E (Ainf D.host.F)).injective ?_) ?_` and prove the remaining obligations. Rewrite using `[← (hΨ z).1, ← (hΨ z').1, hi]`. Rewrite using `[← (hΨ z).2, ← (hΨ z').2, ht]`.
-/
private lemma units_eq_of_res_eq_of_le_iSup {D : D7} {z z' : AE D} (hi : infPart D z = infPart D z') (ht : toEAf D z = toEAf D z') :
    z = z' := by
  obtain ⟨Ψ, hΨ⟩ := eq_lr_take_drop_of_map_fst_eq_replicate (D := D)
  apply Ψ.injective
  refine Prod.ext ((Algebra.TensorProduct.comm D.host.F D.host.E (Ainf D.host.F)).injective ?_) ?_
  · rw [← (hΨ z).1, ← (hΨ z').1, hi]
  · rw [← (hΨ z).2, ← (hΨ z').2, ht]

/- English proof (translation)
Take `⟨Ψ, hΨ⟩` from `eq_lr_take_drop_of_map_fst_eq_replicate (D := D)`. Establish `hwu : w * u = 1` using `by rw [mul_comm, huw]`. Use `⟨⟨Ψ.symm (1, u), Ψ.symm (1, w), ?_, ?_⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Apply `Ψ.injective` to reduce the goal to its premises. Simplify using `[huw]`.

Apply `Ψ.injective` to reduce the goal to its premises. Simplify using `[hwu]`. Use `show infPart D (Ψ.symm (1, u)) = 1`. Rewrite using `[(hΨ _).1, RingEquiv.apply_symm_apply, map_one]`. Use `show toEAf D (Ψ.symm (1, u)) = u`.

Rewrite using `[(hΨ _).2, RingEquiv.apply_symm_apply]`. Use `show toEAf D (Ψ.symm (1, w)) = w`. Rewrite using `[(hΨ _).2, RingEquiv.apply_symm_apply]`.
-/
private lemma exists_unit_infPart_one_toEAf_eq {D : D7} {u w : EAf D} (huw : u * w = 1) :
    ∃ x : (AE D)ˣ, infPart D (x : AE D) = 1 ∧ toEAf D (x : AE D) = u ∧ toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) = w := by
  obtain ⟨Ψ, hΨ⟩ := eq_lr_take_drop_of_map_fst_eq_replicate (D := D)
  have hwu : w * u = 1 := by rw [mul_comm, huw]
  refine ⟨⟨Ψ.symm (1, u), Ψ.symm (1, w), ?_, ?_⟩, ?_, ?_, ?_⟩
  · apply Ψ.injective
    simp [huw]
  · apply Ψ.injective
    simp [hwu]
  · show infPart D (Ψ.symm (1, u)) = 1
    rw [(hΨ _).1, RingEquiv.apply_symm_apply, map_one]
  · show toEAf D (Ψ.symm (1, u)) = u
    rw [(hΨ _).2, RingEquiv.apply_symm_apply]
  · show toEAf D (Ψ.symm (1, w)) = w
    rw [(hΨ _).2, RingEquiv.apply_symm_apply]

/- English proof (translation)
Establish `hε : toEAf D e * toEAf D e = toEAf D e` using `by rw [← map_mul, he]`. Take `⟨x, hx1, hx2, hx3⟩` from `exists_unit_infPart_one_toEAf_eq (u := 1 - toEAf D e + toEAf D e * A.det) (w := 1 - toEAf D e + toEAf D e * v) (by rw [ring_mul hε, h, mul_one, sub_add_cancel])`. Use `⟨x, hx1, hx2, ?_⟩` and prove the remaining obligations. Rewrite using `[hx3]`. Conclude with `Subring.add_mem _ (Subring.sub_mem _ (Subring.one_mem _) hE) (Subring.mul_mem _ hE hv)`.
-/
theorem exists_isUnitDet {e : AE D} (he : e * e = e) (hE : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) {k : ℕ}
    {A : Matrix (Fin k) (Fin k) (EAf D)} {v : EAf D} (hv : v ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h : A.det * v = 1) : ∃ x, IsUnitDet e A x := by
  have hε : toEAf D e * toEAf D e = toEAf D e := by rw [← map_mul, he]
  obtain ⟨x, hx1, hx2, hx3⟩ := exists_unit_infPart_one_toEAf_eq (u := 1 - toEAf D e + toEAf D e * A.det)
    (w := 1 - toEAf D e + toEAf D e * v) (by rw [ring_mul hε, h, mul_one, sub_add_cancel])
  refine ⟨x, hx1, hx2, ?_⟩
  rw [hx3]
  exact Subring.add_mem _ (Subring.sub_mem _ (Subring.one_mem _) hE) (Subring.mul_mem _ hE hv)

/- English proof (translation)
The claim follows from `Units.ext (units_eq_of_res_eq_of_le_iSup (hx.1.trans hx'.1.symm) (hx.2.1.trans hx'.2.1.symm))`.
-/
private lemma isUnitDet_unique' {D : D7} {e : AE D} {k : ℕ} {M : Matrix (Fin k) (Fin k) (EAf D)} {x x' : (AE D)ˣ}
    (hx : IsUnitDet e M x) (hx' : IsUnitDet e M x') : x = x' :=
  Units.ext (units_eq_of_res_eq_of_le_iSup (hx.1.trans hx'.1.symm) (hx.2.1.trans hx'.2.1.symm))

/- English proof (translation)
Establish `hex : ∃ x, IsUnitDet e M x` using `⟨x, hx⟩`. Unfold `unitChar`. Rewrite using `[dif_pos hex, isUnitDet_unique' hex.choose_spec hx]`.
-/
private lemma unitChar_eq_inv_of_isUnitDet {D : D7} (ν : (AE D)ˣ →* Circle) {e : AE D} {k : ℕ} {M : Matrix (Fin k) (Fin k) (EAf D)}
    {x : (AE D)ˣ} (hx : IsUnitDet e M x) : unitChar ν e M = (((ν x)⁻¹ : Circle) : ℂ) := by
  have hex : ∃ x, IsUnitDet e M x := ⟨x, hx⟩
  unfold unitChar
  rw [dif_pos hex, isUnitDet_unique' hex.choose_spec hx]

/- English proof (translation)
Introduce `D ν e he hE k N β hβ hβ'`. Take `⟨y, hy⟩` from `exists_isUnitDet he hE (det_int hβ') (det_gl β)`. Take `⟨y', hy'⟩` from `exists_isUnitDet he hE (det_int hβ) (by rw [mul_comm]; exact det_gl β)`. Distinguish the cases in `hN : ∃ x, IsUnitDet e N x`. Take `⟨x, hx⟩` from `hN`.

Rewrite using `[unitChar_eq_inv_of_isUnitDet ν (isUnitDet_mul he (det_mul' N β.val) hx hy), unitChar_eq_inv_of_isUnitDet ν hx, unitChar_eq_inv_of_isUnitDet ν hy, map_mul, mul_inv, Circle.coe_mul]`. Establish `hNβ : ¬ ∃ x, IsUnitDet e (HMul.hMul N β.val) x`. Introduce and unpack `⟨z, hz⟩`. Conclude with `hN ⟨_, isUnitDet_mul he (by rw [det_mul', mul_assoc, det_gl, mul_one]) hz hy'⟩`. Unfold `unitChar`.

Rewrite using `[dif_neg hN, dif_neg hNβ, zero_mul]`.
-/
theorem unitChar_mul : ∀ {D : D7} (ν : (AE D)ˣ →* Circle) (e : AE D), e * e = e → toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E →
  ∀ {k : ℕ} (N : Matrix (Fin k) (Fin k) (EAf D)) (β : GL (Fin k) (EAf D)), IsIntM β.val → IsIntM (β⁻¹).val →
  unitChar ν e (HMul.hMul N β.val) = unitChar ν e N * unitChar ν e β.val := by
  intro D ν e he hE k N β hβ hβ'
  obtain ⟨y, hy⟩ := exists_isUnitDet he hE (det_int hβ') (det_gl β)
  obtain ⟨y', hy'⟩ := exists_isUnitDet he hE (det_int hβ) (by rw [mul_comm]; exact det_gl β)
  by_cases hN : ∃ x, IsUnitDet e N x
  · obtain ⟨x, hx⟩ := hN
    rw [unitChar_eq_inv_of_isUnitDet ν (isUnitDet_mul he (det_mul' N β.val) hx hy), unitChar_eq_inv_of_isUnitDet ν hx, unitChar_eq_inv_of_isUnitDet ν hy,
      map_mul, mul_inv, Circle.coe_mul]
  · have hNβ : ¬ ∃ x, IsUnitDet e (HMul.hMul N β.val) x := by
      rintro ⟨z, hz⟩
      exact hN ⟨_, isUnitDet_mul he (by rw [det_mul', mul_assoc, det_gl, mul_one]) hz hy'⟩
    unfold unitChar
    rw [dif_neg hN, dif_neg hNβ, zero_mul]

end GlobalTheory.StdRead.CharMul

end
