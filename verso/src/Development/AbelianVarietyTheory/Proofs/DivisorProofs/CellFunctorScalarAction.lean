import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
open GlobalTheory.PRep GlobalTheory.SmGL Matrix

noncomputable section

namespace GlobalTheory.CellLowerScalar

open GlobalTheory.SplitWeil

/- English proof (translation)
Use `ext`. Simplify using `[GeneralLinearGroup.scalar, Matrix.det_diagonal]`.
-/
theorem det_scalar_fin {k : Type} [Field k] (n : ℕ) (t : kˣ) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin n) t) = t ^ n := by
  ext
  simp [GeneralLinearGroup.scalar, Matrix.det_diagonal]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Use `show F.1.1 (x * z) = c • F.1.1 x`. Rewrite using `[hcen x]`.

Conclude with `(F.1.2 ⟨z, hz⟩ x).trans (hc _)`.
-/
theorem smInd_central' {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W]
    [Module ℂ W] (H : Subgroup G) (σ : Representation ℂ H W) (z : G) (hz : z ∈ H)
    (hcen : ∀ x, x * z = z * x) (c : ℂ) (hc : ∀ w, σ ⟨z, hz⟩ w = c • w) (F : smoothPart (ind H σ)) :
    smInd H σ z F = c • F := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  show F.1.1 (x * z) = c • F.1.1 x
  rw [hcen x]
  exact (F.1.2 ⟨z, hz⟩ x).trans (hc _)

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [map_add, hx, hy, smul_add]`. Consider the case `tmul x y`. Rewrite using `[MonoidHom.comp_apply, extTensor_tmul]`.

Simplify using `only [detRep, ofChar_apply, detChar_apply, Units.val_mul]`. Rewrite using `[← smul_eq_mul, ← smul_eq_mul, TensorProduct.smul_tmul_smul]`. Both sides reduce to the same expression.
-/
theorem detTensor_apply {k : Type} [Field k] {a b : Type} [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] (χ₁ χ₂ : kˣ →* ℂˣ) (l : Levi k (Two a b)) (x : TensorProduct ℂ ℂ ℂ) :
    ((extTensor (detRep a χ₁) (detRep b χ₂)).comp (leviTwo k a b).symm.toMonoidHom) l x =
      ((χ₁ (GeneralLinearGroup.det (l false)) * χ₂ (GeneralLinearGroup.det (l true)) : ℂˣ) : ℂ) • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy, smul_add]
  | tmul x y =>
    rw [MonoidHom.comp_apply, extTensor_tmul]
    simp only [detRep, ofChar_apply, detChar_apply, Units.val_mul]
    rw [← smul_eq_mul, ← smul_eq_mul, TensorProduct.smul_tmul_smul]
    rfl

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Simplify using `[modExp, Finset.sum_filter, Fintype.sum_bool]`.
-/
theorem modExp_bool_true (m : Bool → Type) [∀ a, Fintype (m a)] :
    modExp m true = -(Fintype.card (m false) : ℤ) := by
  simp [modExp, Finset.sum_filter, Fintype.sum_bool]

/- English proof (translation)
Rewrite using `[relDeltaHalf_apply, Fintype.prod_bool, deltaHalf_apply, deltaHalf_apply]`. Simplify using `only [Fintype.prod_bool, det_scalar_fin, cond_true, cond_false, one_pow, map_one, h01, pow_zero, mul_one, modExp_bool_true, Fintype.card_fin]`. Simplify using the standard rewrite rules.
-/
theorem relDeltaHalf_cols_scalar (n : Bool → Bool → ℕ) (h01 : n false true = 0) (ϖ : kˣ) :
    relDeltaHalf k (fun j i => Fin (n i j))
      (fun j i => GeneralLinearGroup.scalar (Fin (n i j)) (cond j ϖ 1)) = 1 := by
  rw [relDeltaHalf_apply, Fintype.prod_bool, deltaHalf_apply, deltaHalf_apply]
  simp only [Fintype.prod_bool, det_scalar_fin, cond_true, cond_false, one_pow, map_one, h01, pow_zero,
    mul_one, modExp_bool_true, Fintype.card_fin]
  simp

/- English proof (translation)
Rewrite using `[relDeltaHalf_apply, Fintype.prod_bool, deltaHalf_apply, deltaHalf_apply]`. Simplify using `only [Fintype.prod_bool, det_scalar_fin, cond_true, cond_false, one_pow, map_one, h01, h11, pow_zero, pow_one, mul_one, one_mul, modExp_bool_true, Fintype.card_fin]`. Use `push_cast`. Put the polynomial expressions in normal form.
-/
theorem relDeltaHalf_rows_scalar (n : Bool → Bool → ℕ) (h01 : n false true = 0) (h11 : n true true = 1)
    (ϖ : kˣ) :
    relDeltaHalf k (fun i j => Fin (n i j))
      (fun i j => GeneralLinearGroup.scalar (Fin (n i j)) (cond j ϖ 1)) =
        absPow k (-((n true false : ℕ) : ℂ) / 2) ϖ := by
  rw [relDeltaHalf_apply, Fintype.prod_bool, deltaHalf_apply, deltaHalf_apply]
  simp only [Fintype.prod_bool, det_scalar_fin, cond_true, cond_false, one_pow, map_one, h01, h11, pow_zero,
    pow_one, mul_one, one_mul, modExp_bool_true, Fintype.card_fin]
  push_cast
  ring_nf

/- English proof (translation)
Apply the tactic sequence `cases i <;> simp [relEmb_apply, det_leviEmb, Fintype.prod_bool, det_scalar_fin, h01, h11]`.
-/
theorem det_relEmb_scalar {M : Bool → Type} [∀ i, Fintype (M i)] [∀ i, DecidableEq (M i)]
    (n : Bool → Bool → ℕ) (h01 : n false true = 0) (h11 : n true true = 1)
    (f : ∀ i, (Σ j, Fin (n i j)) ≃ M i) (ϖ : kˣ) (i : Bool) :
    GeneralLinearGroup.det
        (relEmb k f (fun i j => GeneralLinearGroup.scalar (Fin (n i j)) (cond j ϖ 1)) i) = cond i ϖ 1 := by
  cases i <;> simp [relEmb_apply, det_leviEmb, Fintype.prod_bool, det_scalar_fin, h01, h11]

end

end GlobalTheory.CellLowerScalar

open GlobalTheory.CellLowerScalar in

/- English proof (translation)
Introduce `k _ _ _ _ χ₁ χ₂ u v b hb f g ϖ w`. Establish `r0` using `b.2.1 false`. Establish `r1` using `b.2.1 true`. Establish `c0` using `b.2.2 false`. Establish `c1` using `b.2.2 true`.

Simplify using `only [Fintype.sum_bool, Fintype.card_fin] at r0 r1 c0 c1`. Establish `h11 : b.1 true true = 1` using `by omega`. Establish `h10 : b.1 true false + 1 = v` using `by omega`. Set `z` to `leviTwo k (Fin (u + v)) (Fin 1) (1, GeneralLinearGroup.scalar (Fin 1) ϖ)`. Set `s : Bool → kˣ` to `fun j => cond j ϖ 1`.

Establish `hzs : ∀ j, z j = GeneralLinearGroup.scalar (Two (Fin (u + v)) (Fin 1) j) (s j)`. Introduce and unpack `(_ | _)`. Conclude with `(map_one _).symm`. Both sides reduce to the same expression. Establish `hz : z ∈ relParab k (c` using `fun j i => Fin (b.1 i j)) g := fun j _ => mem_parab.2 fun x y hxy => by`.

Establish `hne : x ≠ y` using `by rintro rfl; exact lt_irrefl _ hxy`. Rewrite using `[hzs j]`. Simplify using `[Matrix.GeneralLinearGroup.scalar, hne]`. Establish `hcen : ∀ x : Levi k (Two (Fin (u + v)) (Fin 1)), x * z = z * x` using `fun x => by`. Use function extensionality and compare the values at `j`.

Rewrite using `[Pi.mul_apply, Pi.mul_apply, hzs j]`. Use `ext1`. Simplify using `only [Units.val_mul, Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_coe]`. Conclude with `(Matrix.scalar_commute _ (fun r => Commute.all _ r) _).symm.eq`. Establish `hproj : relProj k (c` using `fun j i => Fin (b.1 i j)) g ⟨z, hz⟩ = fun j i => GeneralLinearGroup.scalar (Fin (b.1 i j)) (s j) := by`.

Use function extensionality and compare the values at `j i`. Use `Units.ext (Matrix.ext fun x y => ?_)` and prove the remaining obligations. Use `(leviProj_apply k (g j) ⟨z j, hz j trivial⟩ i x y).trans ?_` and prove the remaining obligations. Use `show ((z j : GL _ k) : Matrix _ _ k) (g j ⟨i, x⟩) (g j ⟨i, y⟩) = _`. Rewrite using `[hzs j]`.

Simplify using `[Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply]`. Use `smInd_central' _ _ z hz hcen _ (fun w' => ?_) w` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ w'`. Rewrite using `[MonoidHom.comp_apply, twist_apply, hproj, MonoidHom.comp_apply, relJac_mk, detTensor_apply]`. Establish `hsw : swapBlocks k (fun i j => Fin (b.1 i j)) (fun j i => GeneralLinearGroup.scalar (Fin (b.1 i j)) (s j)) = fun i j => GeneralLinearGroup.scalar (Fin (b.1 i j)) (s j)` using `rfl`.

Rewrite using `[hsw, relDeltaHalf_cols_scalar b.1 hb ϖ, relDeltaHalf_rows_scalar b.1 hb h11 ϖ, det_relEmb_scalar b.1 hb h11 f ϖ, det_relEmb_scalar b.1 hb h11 f ϖ]`. Establish `hv : ((b.1 true false : ℕ) : ℂ) = (v : ℂ) - 1`. Use `congrArg (Nat.cast (R := ℂ)) h10` as an intermediate fact. Move the coercions through the operations in `at this`. Take the linear combination `this`.

Rewrite using `[hv, neg_div, absPow_neg, MonoidHom.inv_apply, inv_inv]`. Simplify using `only [cond_true, cond_false, map_one, one_mul, Units.val_one, one_smul, Submodule.Quotient.mk_smul, smul_smul, MonoidHom.mul_apply, Units.val_mul]`. Rewrite using `[mul_comm]`.
-/
theorem GlobalTheory.cellFunctor_detTensor_scalar_lower : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ)
    (b : SizeMatrix (Two (Fin (u + 1)) (Fin v)) (Two (Fin (u + v)) (Fin 1))), b.1 false true = 0 →
    ∀ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin (u + 1)) (Fin v) i)
      (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Two (Fin (u + v)) (Fin 1) j) (ϖ : kˣ) w,
      cellFunctor f g ((extTensor (detRep (Fin (u + 1)) χ₁) (detRep (Fin v) χ₂)).comp
          (leviTwo k (Fin (u + 1)) (Fin v)).symm.toMonoidHom)
        (leviTwo k (Fin (u + v)) (Fin 1) (1, GeneralLinearGroup.scalar (Fin 1) ϖ)) w =
        (((χ₂ * absPow k (((v : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ) • w := by
  intro k _ _ _ _ χ₁ χ₂ u v b hb f g ϖ w
  have r0 := b.2.1 false
  have r1 := b.2.1 true
  have c0 := b.2.2 false
  have c1 := b.2.2 true
  simp only [Fintype.sum_bool, Fintype.card_fin] at r0 r1 c0 c1
  have h11 : b.1 true true = 1 := by omega
  have h10 : b.1 true false + 1 = v := by omega
  let z := leviTwo k (Fin (u + v)) (Fin 1) (1, GeneralLinearGroup.scalar (Fin 1) ϖ)
  let s : Bool → kˣ := fun j => cond j ϖ 1
  have hzs : ∀ j, z j = GeneralLinearGroup.scalar (Two (Fin (u + v)) (Fin 1) j) (s j) := by
    rintro (_ | _)
    · exact (map_one _).symm
    · rfl
  have hz : z ∈ relParab k (c := fun j i => Fin (b.1 i j)) g := fun j _ =>
    mem_parab.2 fun x y hxy => by
      have hne : x ≠ y := by rintro rfl; exact lt_irrefl _ hxy
      rw [hzs j]
      simp [Matrix.GeneralLinearGroup.scalar, hne]
  have hcen : ∀ x : Levi k (Two (Fin (u + v)) (Fin 1)), x * z = z * x := fun x => by
    funext j
    rw [Pi.mul_apply, Pi.mul_apply, hzs j]
    ext1
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_coe]
    exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).symm.eq
  have hproj : relProj k (c := fun j i => Fin (b.1 i j)) g ⟨z, hz⟩ =
      fun j i => GeneralLinearGroup.scalar (Fin (b.1 i j)) (s j) := by
    funext j i
    refine Units.ext (Matrix.ext fun x y => ?_)
    refine (leviProj_apply k (g j) ⟨z j, hz j trivial⟩ i x y).trans ?_
    show ((z j : GL _ k) : Matrix _ _ k) (g j ⟨i, x⟩) (g j ⟨i, y⟩) = _
    rw [hzs j]
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply]
  refine smInd_central' _ _ z hz hcen _ (fun w' => ?_) w
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ w'
  rw [MonoidHom.comp_apply, twist_apply, hproj, MonoidHom.comp_apply, relJac_mk, detTensor_apply]
  have hsw : swapBlocks k (fun i j => Fin (b.1 i j)) (fun j i => GeneralLinearGroup.scalar (Fin (b.1 i j)) (s j)) =
      fun i j => GeneralLinearGroup.scalar (Fin (b.1 i j)) (s j) := rfl
  rw [hsw, relDeltaHalf_cols_scalar b.1 hb ϖ, relDeltaHalf_rows_scalar b.1 hb h11 ϖ,
    det_relEmb_scalar b.1 hb h11 f ϖ, det_relEmb_scalar b.1 hb h11 f ϖ]
  have hv : ((b.1 true false : ℕ) : ℂ) = (v : ℂ) - 1 := by
    have := congrArg (Nat.cast (R := ℂ)) h10
    push_cast at this
    linear_combination this
  rw [hv, neg_div, absPow_neg, MonoidHom.inv_apply, inv_inv]
  simp only [cond_true, cond_false, map_one, one_mul, Units.val_one, one_smul, Submodule.Quotient.mk_smul,
    smul_smul, MonoidHom.mul_apply, Units.val_mul]
  rw [mul_comm]
