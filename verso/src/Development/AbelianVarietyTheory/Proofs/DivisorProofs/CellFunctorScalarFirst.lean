import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
open GlobalTheory.PRep GlobalTheory.SmGL Matrix

open scoped TensorProduct
noncomputable section
namespace GlobalTheory.SmGL.CellScalarFirst

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use `ext`. Simplify using `[GeneralLinearGroup.scalar]`.
-/
theorem det_scalar (n : ℕ) (z : kˣ) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin n) z) = z ^ n := by
  ext; simp [GeneralLinearGroup.scalar]

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [map_add, hx, hy, smul_add]`. Consider the case `tmul a b`. Rewrite using `[extTensor_tmul]`.

Simplify using `only [detRep, ofChar_apply, Units.val_mul]`. Rewrite using `[detChar_apply, detChar_apply, ← smul_eq_mul _ b, TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem extTensor_detRep_apply (u v : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ) (g1 : GL (Fin u) k)
    (g2 : GL (Fin (v + 1)) k) (y : ℂ ⊗[ℂ] ℂ) :
    extTensor (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂) (g1, g2) y =
      ((χ₁ (GeneralLinearGroup.det g1) * χ₂ (GeneralLinearGroup.det g2) : ℂˣ) : ℂ) • y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy, smul_add]
  | tmul a b =>
    rw [extTensor_tmul]
    simp only [detRep, ofChar_apply, Units.val_mul]
    rw [detChar_apply, detChar_apply, ← smul_eq_mul _ b, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', smul_eq_mul]
    congr 1
    ring

/- English proof (translation)
The claim follows from `F.2 h x`.
-/
theorem indSpace_law {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (H : Subgroup G)
    (σ : Representation ℂ H W) (F : indSpace H σ) (h : H) (x : G) : F.1 (h * x) = σ h (F.1 x) :=
  F.2 h x

end GlobalTheory.SmGL.CellScalarFirst

open GlobalTheory.SmGL.CellScalarFirst in
/- English proof (translation)
Introduce `k _ _ _ _ χ₁ χ₂ u v B hB f g ϖ w`. Establish `hrow : B.1 false false + B.1 false true = u`. Establish `h` using `B.2.1 false`. Simplify using `[Fintype.sum_bool] at h`. Use linear arithmetic over natural numbers and integers.

Establish `hcol : B.1 false false + B.1 true false = 1`. Establish `h` using `B.2.2 false`. Simplify using `[Fintype.sum_bool] at h`. Use linear arithmetic over natural numbers and integers. Establish `h10 : B.1 true false = 0` using `by omega`.

Establish `hz : leviTwo k (Fin 1) (Fin (u + v)) (GeneralLinearGroup.scalar (Fin 1) ϖ, 1) ∈ relParab k g`. Use `(Subgroup.mem_pi _).2 fun j _ => ?_` and prove the remaining obligations. Consider the cases of `j`. Use `mem_parab.2 fun i j h => ?_` and prove the remaining obligations. Take `rfl : i = j` from `Subsingleton.elim _ _`.

Conclude with `absurd h (lt_irrefl _)`. Conclude with `one_mem _`. Establish `hcomm : ∀ x : Levi k (Two (Fin 1) (Fin (u + v))), x * leviTwo k (Fin 1) (Fin (u + v)) (GeneralLinearGroup.scalar (Fin 1) ϖ, 1) = leviTwo k (Fin 1) (Fin (u + v)) (GeneralLinearGroup.scalar (Fin 1) ϖ, 1) * x`. Introduce `x`. Use function extensionality and compare the values at `j`.

Consider the cases of `j`. Use extensionality with `a b show ((x false * GeneralLinearGroup.scalar (Fin 1) ϖ : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k) a b = ((GeneralLinearGroup.scalar (Fin 1) ϖ * x false : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k) a b`. Establish `ha : a = 0` using `Subsingleton.elim _ _`. Establish `hb : b = 0` using `Subsingleton.elim _ _`. Substitute `ha hb` using the available equality.

Simplify using `[GeneralLinearGroup.scalar, Matrix.mul_apply, mul_comm]`. Use `show x true * 1 = 1 * x true`. Rewrite using `[mul_one, one_mul]`. Establish `hp1 : ∀ i, relProj k g (⟨_, hz⟩ : relParab k g) true i = 1`. Introduce `i`.

Use extensionality with `a b`. Rewrite using `[show (relProj k g (⟨_, hz⟩ : relParab k g) true i : Matrix _ _ k) a b = ((1 : GL (Fin (u + v)) k) : Matrix _ _ k) (g true ⟨i, a⟩) (g true ⟨i, b⟩) from rfl]`. Establish `hinj : g true ⟨i, a⟩ = g true ⟨i, b⟩ ↔ a = b` using `((g true).injective.comp sigma_mk_injective).eq_iff`. Simplify using `only [Units.val_one, Matrix.one_apply, hinj]`. Establish `hp0 : ∀ i, relProj k g (⟨_, hz⟩ : relParab k g) false i = GeneralLinearGroup.scalar _ ϖ`.

Introduce `i`. Use extensionality with `a b`. Rewrite using `[show (relProj k g (⟨_, hz⟩ : relParab k g) false i : Matrix _ _ k) a b = ((GeneralLinearGroup.scalar (Fin 1) ϖ : GL (Fin 1) k) : Matrix _ _ k) (g false ⟨i, a⟩) (g false ⟨i, b⟩) from rfl]`. Establish `h' : (⟨i, a⟩ : Σ j, Fin (B.1 j false)) = ⟨i, b⟩` using `(g false).injective (Subsingleton.elim _ _)`. Establish `hab : a = b` using `eq_of_heq (Sigma.mk.inj_iff.1 h').2`.

Substitute `hab` using the available equality. Simplify using `[GeneralLinearGroup.scalar]`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`.

Establish `e1 : w.1.1 (x * leviTwo k (Fin 1) (Fin (u + v)) (GeneralLinearGroup.scalar (Fin 1) ϖ, 1)) = (((χ₁ * absPow k ((1 - (u : ℂ)) / 2)) ϖ : ℂˣ) : ℂ) • w.1.1 x`. Use `(congrArg w.1.1 (hcomm x)).trans ?_` and prove the remaining obligations. Use `(indSpace_law _ _ w.1 ⟨_, hz⟩ x).trans ?_` and prove the remaining obligations. Generalize the expression as in `w.1.1 x = y`. Rewrite using `[MonoidHom.comp_apply, twist_apply]`.

Generalize the expression as in `relProj k g (⟨_, hz⟩ : relParab k g) = p at hp0 hp1 ⊢`. Establish `hft : (B.1 false true : ℂ) = (u : ℂ) - 1`. Establish `h' : (u : ℂ) = (B.1 false true : ℂ) + 1`. Establish `: B.1 false true + 1 = u` using `by omega`. Conclude with `this.symm` after adjusting the coercions.

Rewrite using `[h']`. Expand and normalize the polynomial expressions, which then agree. Establish `hδ' : relDeltaHalf k (fun j i => Fin (B.1 i j)) p = 1`. Rewrite using `[relDeltaHalf_apply, Fintype.prod_bool]`. Establish `ht : p true = 1` using `funext hp1`.

Rewrite using `[ht, map_one, one_mul, deltaHalf_apply, Fintype.prod_bool]`. Simplify using `only [hp0, det_scalar, h10, pow_zero, map_one, one_mul]`. Simplify using `[modExp, Finset.sum_filter, h10]`. Establish `hq00 : swapBlocks k (fun i j => Fin (B.1 i j)) p false false = GeneralLinearGroup.scalar _ ϖ` using `hp0 false`. Establish `hq01 : swapBlocks k (fun i j => Fin (B.1 i j)) p false true = 1` using `hp1 false`.

Establish `hq10 : swapBlocks k (fun i j => Fin (B.1 i j)) p true false = GeneralLinearGroup.scalar _ ϖ` using `hp0 true`. Establish `hq11 : swapBlocks k (fun i j => Fin (B.1 i j)) p true true = 1` using `hp1 true`. Establish `hδ : relDeltaHalf k (fun i j => Fin (B.1 i j)) (swapBlocks k (fun i j => Fin (B.1 i j)) p) = absPow k (((u : ℂ) - 1) / 2) ϖ`. Rewrite using `[relDeltaHalf_apply, Fintype.prod_bool, deltaHalf_apply, deltaHalf_apply, Fintype.prod_bool, Fintype.prod_bool, hq00, hq01, hq10, hq11]`. Simplify using `only [det_scalar, h10, hB, pow_zero, pow_one, map_one, one_mul, mul_one]`.

Establish `hlt : ¬ (true < false)` using `by decide`. Simplify using `[modExp, Finset.sum_filter, hft, hlt]`. Establish `hρ : ∀ y', ((extTensor (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)).comp (leviTwo k (Fin u) (Fin (v + 1))).symm.toMonoidHom) (relEmb k f (swapBlocks k (fun i j => Fin (B.1 i j)) p)) y' = ((χ₁ ϖ : ℂˣ) : ℂ) • y'`. Introduce `y'`. Rewrite using `[MonoidHom.comp_apply]`.

Use `(extTensor_detRep_apply u v χ₁ χ₂ (relEmb k f (swapBlocks k (fun i j => Fin (B.1 i j)) p) false) (relEmb k f (swapBlocks k (fun i j => Fin (B.1 i j)) p) true) y').trans ?_` and prove the remaining obligations. Rewrite using `[relEmb_apply, relEmb_apply, det_leviEmb, det_leviEmb, Fintype.prod_bool, Fintype.prod_bool, hq00, hq01, hq10, hq11]`. Simplify using `[det_scalar, h10, hB]`. Rewrite using `[hδ', Units.val_one, one_smul, MonoidHom.comp_apply]`. Take `⟨v', rfl⟩` from `Submodule.Quotient.mk_surjective _ y`.

Rewrite using `[relJac_mk, hρ, hδ, Submodule.Quotient.mk_smul, smul_smul]`. Use `congr 1`. Rewrite using `[MonoidHom.mul_apply, show (1 - (u : ℂ)) / 2 = -(((u : ℂ) - 1) / 2) by ring, absPow_neg, MonoidHom.inv_apply, Units.val_mul, mul_comm]`. Conclude with `e1`.
-/
theorem GlobalTheory.SmGL.cellFunctor_scalar_first : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ)
    (B : SizeMatrix (Two (Fin u) (Fin (v + 1))) (Two (Fin 1) (Fin (u + v)))), B.1 false false = 1 →
    ∀ (f : ∀ i, (Σ j, Fin (B.1 i j)) ≃ Two (Fin u) (Fin (v + 1)) i)
      (g : ∀ j, (Σ i, Fin (B.1 i j)) ≃ Two (Fin 1) (Fin (u + v)) j) (ϖ : kˣ)
      (w : smoothPart (ind (relParab k g) ((twist ((relJac f ((extTensor (detRep (Fin u) χ₁)
        (detRep (Fin (v + 1)) χ₂)).comp (leviTwo k (Fin u) (Fin (v + 1))).symm.toMonoidHom)).comp
          (swapBlocks k fun i j => Fin (B.1 i j))) (relDeltaHalf k fun j i => Fin (B.1 i j))).comp (relProj k g)))),
      cellFunctor f g ((extTensor (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)).comp
        (leviTwo k (Fin u) (Fin (v + 1))).symm.toMonoidHom)
          (leviTwo k (Fin 1) (Fin (u + v)) (GeneralLinearGroup.scalar (Fin 1) ϖ, 1)) w =
        (((χ₁ * absPow k ((1 - (u : ℂ)) / 2)) ϖ : ℂˣ) : ℂ) • w := by
  intro k _ _ _ _ χ₁ χ₂ u v B hB f g ϖ w

  have hrow : B.1 false false + B.1 false true = u := by
    have h := B.2.1 false
    simp [Fintype.sum_bool] at h
    omega
  have hcol : B.1 false false + B.1 true false = 1 := by
    have h := B.2.2 false
    simp [Fintype.sum_bool] at h
    omega
  have h10 : B.1 true false = 0 := by omega
  have hz : leviTwo k (Fin 1) (Fin (u + v)) (GeneralLinearGroup.scalar (Fin 1) ϖ, 1) ∈ relParab k g := by
    refine (Subgroup.mem_pi _).2 fun j _ => ?_
    cases j
    · refine mem_parab.2 fun i j h => ?_
      obtain rfl : i = j := Subsingleton.elim _ _
      exact absurd h (lt_irrefl _)
    · exact one_mem _
  have hcomm : ∀ x : Levi k (Two (Fin 1) (Fin (u + v))), x * leviTwo k (Fin 1) (Fin (u + v)) (GeneralLinearGroup.scalar (Fin 1) ϖ, 1) =
      leviTwo k (Fin 1) (Fin (u + v)) (GeneralLinearGroup.scalar (Fin 1) ϖ, 1) * x := by
    intro x
    funext j
    cases j
    · ext a b
      show ((x false * GeneralLinearGroup.scalar (Fin 1) ϖ : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k) a b =
        ((GeneralLinearGroup.scalar (Fin 1) ϖ * x false : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k) a b
      have ha : a = 0 := Subsingleton.elim _ _
      have hb : b = 0 := Subsingleton.elim _ _
      subst ha hb
      simp [GeneralLinearGroup.scalar, Matrix.mul_apply, mul_comm]
    · show x true * 1 = 1 * x true
      rw [mul_one, one_mul]
  have hp1 : ∀ i, relProj k g (⟨_, hz⟩ : relParab k g) true i = 1 := by
    intro i
    ext a b
    rw [show (relProj k g (⟨_, hz⟩ : relParab k g) true i : Matrix _ _ k) a b =
      ((1 : GL (Fin (u + v)) k) : Matrix _ _ k) (g true ⟨i, a⟩) (g true ⟨i, b⟩) from rfl]
    have hinj : g true ⟨i, a⟩ = g true ⟨i, b⟩ ↔ a = b :=
      ((g true).injective.comp sigma_mk_injective).eq_iff
    simp only [Units.val_one, Matrix.one_apply, hinj]
  have hp0 : ∀ i, relProj k g (⟨_, hz⟩ : relParab k g) false i = GeneralLinearGroup.scalar _ ϖ := by
    intro i
    ext a b
    rw [show (relProj k g (⟨_, hz⟩ : relParab k g) false i : Matrix _ _ k) a b =
      ((GeneralLinearGroup.scalar (Fin 1) ϖ : GL (Fin 1) k) : Matrix _ _ k) (g false ⟨i, a⟩) (g false ⟨i, b⟩) from rfl]
    have h' : (⟨i, a⟩ : Σ j, Fin (B.1 j false)) = ⟨i, b⟩ := (g false).injective (Subsingleton.elim _ _)
    have hab : a = b := eq_of_heq (Sigma.mk.inj_iff.1 h').2
    subst hab
    simp [GeneralLinearGroup.scalar]
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have e1 : w.1.1 (x * leviTwo k (Fin 1) (Fin (u + v)) (GeneralLinearGroup.scalar (Fin 1) ϖ, 1)) =
      (((χ₁ * absPow k ((1 - (u : ℂ)) / 2)) ϖ : ℂˣ) : ℂ) • w.1.1 x := by
    refine (congrArg w.1.1 (hcomm x)).trans ?_
    refine (indSpace_law _ _ w.1 ⟨_, hz⟩ x).trans ?_
    generalize w.1.1 x = y
    rw [MonoidHom.comp_apply, twist_apply]
    generalize relProj k g (⟨_, hz⟩ : relParab k g) = p at hp0 hp1 ⊢
    have hft : (B.1 false true : ℂ) = (u : ℂ) - 1 := by
      have h' : (u : ℂ) = (B.1 false true : ℂ) + 1 := by
        have : B.1 false true + 1 = u := by omega
        exact_mod_cast this.symm
      rw [h']; ring
    have hδ' : relDeltaHalf k (fun j i => Fin (B.1 i j)) p = 1 := by
      rw [relDeltaHalf_apply, Fintype.prod_bool]
      have ht : p true = 1 := funext hp1
      rw [ht, map_one, one_mul, deltaHalf_apply, Fintype.prod_bool]
      simp only [hp0, det_scalar, h10, pow_zero, map_one, one_mul]
      simp [modExp, Finset.sum_filter, h10]
    have hq00 : swapBlocks k (fun i j => Fin (B.1 i j)) p false false = GeneralLinearGroup.scalar _ ϖ :=
      hp0 false
    have hq01 : swapBlocks k (fun i j => Fin (B.1 i j)) p false true = 1 := hp1 false
    have hq10 : swapBlocks k (fun i j => Fin (B.1 i j)) p true false = GeneralLinearGroup.scalar _ ϖ :=
      hp0 true
    have hq11 : swapBlocks k (fun i j => Fin (B.1 i j)) p true true = 1 := hp1 true
    have hδ : relDeltaHalf k (fun i j => Fin (B.1 i j)) (swapBlocks k (fun i j => Fin (B.1 i j)) p) =
        absPow k (((u : ℂ) - 1) / 2) ϖ := by
      rw [relDeltaHalf_apply, Fintype.prod_bool, deltaHalf_apply, deltaHalf_apply, Fintype.prod_bool,
        Fintype.prod_bool, hq00, hq01, hq10, hq11]
      simp only [det_scalar, h10, hB, pow_zero, pow_one, map_one, one_mul, mul_one]
      have hlt : ¬ (true < false) := by decide
      simp [modExp, Finset.sum_filter, hft, hlt]
    have hρ : ∀ y', ((extTensor (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)).comp
        (leviTwo k (Fin u) (Fin (v + 1))).symm.toMonoidHom)
          (relEmb k f (swapBlocks k (fun i j => Fin (B.1 i j)) p)) y' = ((χ₁ ϖ : ℂˣ) : ℂ) • y' := by
      intro y'
      rw [MonoidHom.comp_apply]
      refine (extTensor_detRep_apply u v χ₁ χ₂ (relEmb k f (swapBlocks k (fun i j => Fin (B.1 i j)) p) false)
        (relEmb k f (swapBlocks k (fun i j => Fin (B.1 i j)) p) true) y').trans ?_
      rw [relEmb_apply, relEmb_apply, det_leviEmb, det_leviEmb, Fintype.prod_bool, Fintype.prod_bool,
        hq00, hq01, hq10, hq11]
      simp [det_scalar, h10, hB]
    rw [hδ', Units.val_one, one_smul, MonoidHom.comp_apply]
    obtain ⟨v', rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [relJac_mk, hρ, hδ, Submodule.Quotient.mk_smul, smul_smul]
    congr 1
    rw [MonoidHom.mul_apply, show (1 - (u : ℂ)) / 2 = -(((u : ℂ) - 1) / 2) by ring, absPow_neg,
      MonoidHom.inv_apply, Units.val_mul, mul_comm]
  exact e1
