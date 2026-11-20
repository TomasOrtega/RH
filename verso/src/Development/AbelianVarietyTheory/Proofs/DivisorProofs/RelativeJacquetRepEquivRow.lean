import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothColRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstCellFunctorEquiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeometricLemmaCellOneBlockSwapEquiv

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SmGL.RowOneCell Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SmGL.RowOneCell

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Rewrite using `[colRep, MonoidHom.comp_apply]`. Conclude with `CellFirstDet.extTensor_detRep_apply _ _ _ w`.
-/
theorem colRep_apply (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) (j : Bool) (g : Levi k fun i => Fin (sz u v i j))
    (w : ℂ ⊗[ℂ] ℂ) :
    colRep χ₁ χ₂ u v j g w =
      ((χ₁ (GeneralLinearGroup.det (g false)) * colChar v χ₂ j (GeneralLinearGroup.det (g true)) : ℂˣ) : ℂ) • w := by
  rw [colRep, MonoidHom.comp_apply]
  exact CellFirstDet.extTensor_detRep_apply _ _ _ w

def cellScal (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) (x : ∀ j, Levi k fun i => Fin (sz u v i j)) : ℂˣ :=
  ∏ j, χ₁ (GeneralLinearGroup.det (x j false)) * colChar v χ₂ j (GeneralLinearGroup.det (x j true))

/- English proof (translation)
Proceed by induction on `y using PiTensorProduct.induction_on with`. Consider the case `add a b ha hb => rw [map_add, ha, hb, smul_add]`. Consider the case `smul_tprod c f`. Rewrite using `[map_smul, smul_comm, piTensor_tprod, cellScal, Units.coe_prod, ← MultilinearMap.map_smul_univ]`. Use `congr 2`.

Use function extensionality and compare the values at `j`. Conclude with `colRep_apply χ₁ χ₂ u v j (x j) (f j)`.
-/
theorem piTensor_colRep_apply (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) (x : ∀ j, Levi k fun i => Fin (sz u v i j))
    (y : ⨂[ℂ] _ : Bool, ℂ ⊗[ℂ] ℂ) :
    piTensor (colRep χ₁ χ₂ u v) x y = (cellScal χ₁ χ₂ u v x : ℂ) • y := by
  induction y using PiTensorProduct.induction_on with
  | add a b ha hb => rw [map_add, ha, hb, smul_add]
  | smul_tprod c f =>
    rw [map_smul, smul_comm, piTensor_tprod, cellScal, Units.coe_prod, ← MultilinearMap.map_smul_univ]
    congr 2
    funext j
    exact colRep_apply χ₁ χ₂ u v j (x j) (f j)

/- English proof (translation)
The claim follows from `CellFirstDet.extTensor_detRep_apply χ₁ χ₂ _ w`.
-/
theorem rowRep_apply (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) (g : Levi k (Two (Fin u) (Fin (v + 1)))) (w : ℂ ⊗[ℂ] ℂ) :
    (extTensor (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)).comp
      (leviTwo k (Fin u) (Fin (v + 1))).symm.toMonoidHom g w =
      ((χ₁ (GeneralLinearGroup.det (g false)) * χ₂ (GeneralLinearGroup.det (g true)) : ℂˣ) : ℂ) • w :=
  CellFirstDet.extTensor_detRep_apply χ₁ χ₂ _ w

/- English proof (translation)
Use `Submodule.span_eq_bot.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨n, w, rfl⟩`. Establish `h : ∀ i, GeneralLinearGroup.det ((n : Levi k (Two (Fin u) (Fin (v + 1)))) i) = 1` using `fun i => det_eq_one_of_mem_unipRad k (n.2 i trivial)`. Rewrite using `[rowRep_apply, h, h]`. Simplify using the standard rewrite rules.
-/
theorem twKer_rowRep (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) :
    twKer ((extTensor (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)).comp
      (leviTwo k (Fin u) (Fin (v + 1))).symm.toMonoidHom) (relUnip k (rowPart u v)) 1 = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro _ ⟨n, w, rfl⟩
  have h : ∀ i, GeneralLinearGroup.det ((n : Levi k (Two (Fin u) (Fin (v + 1)))) i) = 1 := fun i =>
    det_eq_one_of_mem_unipRad k (n.2 i trivial)
  rw [rowRep_apply, h, h]
  simp

/- English proof (translation)
Take `⟨w, rfl⟩` from `Submodule.Quotient.mk_surjective _ z`. Rewrite using `[MonoidHom.comp_apply, relJac_mk, rowRep_apply, Submodule.Quotient.mk_smul, smul_smul, ← Units.val_mul]`. Use `congr 2`. Establish `hs : ∀ i j, swapBlocks k (fun i j => Fin (sz u v i j)) x i j = x j i` using `fun _ _ => rfl`. Establish `hdet : ∀ i, GeneralLinearGroup.det (relEmb k (rowPart u v) (swapBlocks k (fun i j => Fin (sz u v i j)) x) i) = GeneralLinearGroup.det (x true i) * GeneralLinearGroup.det (x false i)` using `fun i => by`.

Rewrite using `[relEmb_apply, det_leviEmb, Fintype.prod_bool]`. Both sides reduce to the same expression. Establish `h0 : GeneralLinearGroup.det (x false false) = 1` using `CellFirstDet.det_eq_one_of_card rfl _`. Establish `hr0 : deltaHalf k (fun j => Fin (sz u v false j)) (swapBlocks k (fun i j => Fin (sz u v i j)) x false) = 1` using `OneBlockCell.deltaHalf_eq_one_of_single (n := fun j => sz u v false j) true (fun j hj => by cases j; rfl; exact absurd rfl hj) _`. Establish `hm : modExp (fun j => Fin (sz u v true j)) false = v ∧ modExp (fun j => Fin (sz u v true j)) true = -1`.

Take `⟨h1, h2⟩` from `CellFirstDet.modExp_bool (fun j => Fin (sz u v true j))`. Conclude with `⟨h1.trans (by rw [Fintype.card_fin]; rfl), h2.trans (by rw [Fintype.card_fin]; rfl)⟩`. Rewrite using `[relDeltaHalf_apply, Fintype.prod_bool, hr0, deltaHalf_apply, Fintype.prod_bool, hm.1, hm.2, hdet, hdet, h0]`. Simplify using `only [cellScal, Fintype.prod_bool, h0, hs, colChar, cond_true, cond_false]`. Generalize the expression as in `GeneralLinearGroup.det (x false true) = A`.

Generalize the expression as in `GeneralLinearGroup.det (x true false) = B`. Generalize the expression as in `GeneralLinearGroup.det (x true true) = C`. Simplify using `only [MonoidHom.mul_apply, map_mul, mul_one, one_mul, map_one, Int.cast_neg, Int.cast_natCast, Int.cast_one, neg_div, absPow_neg, MonoidHom.inv_apply]`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Units.val_mul, Units.val_inv_eq_inv_val, _root_.mul_inv_rev, inv_inv, Units.val_one]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem rowJac_apply (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) (x : ∀ j, Levi k fun i => Fin (sz u v i j))
    (z : Jacquet ((extTensor (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)).comp
      (leviTwo k (Fin u) (Fin (v + 1))).symm.toMonoidHom) (relUnip k (rowPart u v))) :
    ((relJac (rowPart u v) ((extTensor (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)).comp
      (leviTwo k (Fin u) (Fin (v + 1))).symm.toMonoidHom)).comp
        (swapBlocks k fun i j => Fin (sz u v i j))) x z = (cellScal χ₁ χ₂ u v x : ℂ) • z := by
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [MonoidHom.comp_apply, relJac_mk, rowRep_apply, Submodule.Quotient.mk_smul, smul_smul, ← Units.val_mul]
  congr 2
  have hs : ∀ i j, swapBlocks k (fun i j => Fin (sz u v i j)) x i j = x j i := fun _ _ => rfl
  have hdet : ∀ i, GeneralLinearGroup.det
      (relEmb k (rowPart u v) (swapBlocks k (fun i j => Fin (sz u v i j)) x) i) =
        GeneralLinearGroup.det (x true i) * GeneralLinearGroup.det (x false i) := fun i => by
    rw [relEmb_apply, det_leviEmb, Fintype.prod_bool]
    rfl
  have h0 : GeneralLinearGroup.det (x false false) = 1 := CellFirstDet.det_eq_one_of_card rfl _
  have hr0 : deltaHalf k (fun j => Fin (sz u v false j))
      (swapBlocks k (fun i j => Fin (sz u v i j)) x false) = 1 :=
    OneBlockCell.deltaHalf_eq_one_of_single (n := fun j => sz u v false j) true
      (fun j hj => by cases j; rfl; exact absurd rfl hj) _
  have hm : modExp (fun j => Fin (sz u v true j)) false = v ∧
      modExp (fun j => Fin (sz u v true j)) true = -1 := by
    obtain ⟨h1, h2⟩ := CellFirstDet.modExp_bool (fun j => Fin (sz u v true j))
    exact ⟨h1.trans (by rw [Fintype.card_fin]; rfl), h2.trans (by rw [Fintype.card_fin]; rfl)⟩
  rw [relDeltaHalf_apply, Fintype.prod_bool, hr0, deltaHalf_apply, Fintype.prod_bool, hm.1, hm.2, hdet, hdet,
    h0]
  simp only [cellScal, Fintype.prod_bool, h0, hs, colChar, cond_true, cond_false]
  generalize GeneralLinearGroup.det (x false true) = A
  generalize GeneralLinearGroup.det (x true false) = B
  generalize GeneralLinearGroup.det (x true true) = C
  simp only [MonoidHom.mul_apply, map_mul, mul_one, one_mul, map_one, Int.cast_neg, Int.cast_natCast,
    Int.cast_one, neg_div, absPow_neg, MonoidHom.inv_apply]
  apply Units.ext
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, _root_.mul_inv_rev, inv_inv, Units.val_one]
  ring

def cellLineEquiv (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) :
    Jacquet ((extTensor (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)).comp
      (leviTwo k (Fin u) (Fin (v + 1))).symm.toMonoidHom) (relUnip k (rowPart u v)) ≃ₗ[ℂ]
        ⨂[ℂ] _ : Bool, ℂ ⊗[ℂ] ℂ :=
  (Submodule.quotEquivOfEqBot _ (twKer_rowRep χ₁ χ₂ u v)).trans
    ((TensorProduct.lid ℂ ℂ).trans ((PiTensorProduct.constantBaseRingEquiv Bool ℂ).toLinearEquiv.symm.trans
      (PiTensorProduct.congr fun _ => (TensorProduct.lid ℂ ℂ).symm)))

/- English proof (translation)
Introduce `k _ _ _ _ χ₁ χ₂ u v`. Use `⟨.mk (cellLineEquiv χ₁ χ₂ u v) fun x => LinearMap.ext fun z => ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[rowJac_apply, piTensor_colRep_apply, map_smul]`.
-/
theorem rowJac_swap_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ),
    Nonempty (Representation.Equiv ((relJac (rowPart u v) ((extTensor (detRep (Fin u) χ₁)
      (detRep (Fin (v + 1)) χ₂)).comp (leviTwo k (Fin u) (Fin (v + 1))).symm.toMonoidHom)).comp
        (swapBlocks k fun i j => Fin (sz u v i j))) (piTensor (colRep χ₁ χ₂ u v))) := by
  intro k _ _ _ _ χ₁ χ₂ u v
  refine ⟨.mk (cellLineEquiv χ₁ χ₂ u v) fun x => LinearMap.ext fun z => ?_⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [rowJac_apply, piTensor_colRep_apply, map_smul]

end GlobalTheory.SmGL.RowOneCell
