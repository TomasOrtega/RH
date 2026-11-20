import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.CuspWeights
import GroundTheory.AutomorphicForms.GL2Classical.EigenformTranslatesIrreducible

open NumberField Matrix CongruenceSubgroup ModularForm Complex
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

set_option linter.unusedSectionVars false

def IsGKFStable (W : Submodule ℂ (cuspForms ℚ 2)) : Prop :=
  (∀ X, ∀ v ∈ W, (gkModuleCusp ℚ 2).ρ X v ∈ W) ∧ (∀ x, ∀ v ∈ W, (gkModuleCusp ℚ 2).σ x v ∈ W) ∧
    ∀ g, ∀ v ∈ W, finRepCusp ℚ 2 g v ∈ W

def gkfSpan (φ : cuspForms ℚ 2) : Submodule ℂ (cuspForms ℚ 2) :=
  sInf {W | IsGKFStable W ∧ φ ∈ W}

/- English proof (translation)
The claim follows from `Submodule.mem_sInf.2 fun _ hW => hW.2`.
-/
theorem mem_gkfSpan_self (φ : cuspForms ℚ 2) : φ ∈ gkfSpan φ :=
  Submodule.mem_sInf.2 fun _ hW => hW.2

/- English proof (translation)
The claim follows from `sInf_le ⟨hW, hφ⟩`.
-/
theorem gkfSpan_le {φ : cuspForms ℚ 2} {W : Submodule ℂ (cuspForms ℚ 2)} (hW : IsGKFStable W) (hφ : φ ∈ W) :
    gkfSpan φ ≤ W :=
  sInf_le ⟨hW, hφ⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun X v hv => Submodule.mem_sInf.2 fun W hW => hW.1.1 X v (Submodule.mem_sInf.1 hv W hW), fun x v hv => Submodule.mem_sInf.2 fun W hW => hW.1.2.1 x v (Submodule.mem_sInf.1 hv W hW), fun g v hv => Submodule.mem_sInf.2 fun W hW => hW.1.2.2 g v (Submodule.mem_sInf.1 hv W hW)⟩`.
-/
theorem isGKFStable_gkfSpan (φ : cuspForms ℚ 2) : IsGKFStable (gkfSpan φ) :=
  ⟨fun X v hv => Submodule.mem_sInf.2 fun W hW => hW.1.1 X v (Submodule.mem_sInf.1 hv W hW),
    fun x v hv => Submodule.mem_sInf.2 fun W hW => hW.1.2.1 x v (Submodule.mem_sInf.1 hv W hW),
    fun g v hv => Submodule.mem_sInf.2 fun W hW => hW.1.2.2 g v (Submodule.mem_sInf.1 hv W hW)⟩

/- English proof (translation)
The claim follows from `add_mem (hW.1 _ v hv) (Submodule.smul_mem _ _ (hW.1 _ v hv))`.
-/
theorem IsGKFStable.cuspOp_mem {W : Submodule ℂ (cuspForms ℚ 2)} (hW : IsGKFStable W) (B : Matrix (Fin 2) (Fin 2) ℂ)
    {v : cuspForms ℚ 2} (hv : v ∈ W) : cuspOp B v ∈ W :=
  add_mem (hW.1 _ v hv) (Submodule.smul_mem _ _ (hW.1 _ v hv))

def IsRot (x : archCompact ℚ 2) : Prop :=
  ∃ (w : ℂ) (hw : w ≠ 0), ‖w‖ = 1 ∧ kMat x = kGL w hw

def IsRefl (x : archCompact ℚ 2) : Prop :=
  ∃ (w : ℂ) (hw : w ≠ 0), ‖w‖ = 1 ∧ kMat x = toReal epsilon * kGL w hw

/- English proof (translation)
Take `⟨w, hw, h1, h | h⟩` from `exists_kGL_of_mem_archCompact x`. Conclude with `Or.inl ⟨w, hw, h1, h⟩`. Conclude with `Or.inr ⟨w, hw, h1, h⟩`.
-/
theorem isRot_or_isRefl (x : archCompact ℚ 2) : IsRot x ∨ IsRefl x := by
  obtain ⟨w, hw, h1, h | h⟩ := exists_kGL_of_mem_archCompact x
  · exact Or.inl ⟨w, hw, h1, h⟩
  · exact Or.inr ⟨w, hw, h1, h⟩

/- English proof (translation)
Take `⟨w, hw, -, h⟩` from `hx`. Rewrite using `[h]`. Conclude with `det_kGL_pos w hw`.
-/
theorem IsRot.det_pos {x : archCompact ℚ 2} (hx : IsRot x) : 0 < (kMat x).det.val := by
  obtain ⟨w, hw, -, h⟩ := hx
  rw [h]
  exact det_kGL_pos w hw

/- English proof (translation)
Take `⟨w, hw, -, h⟩` from `hx`. Rewrite using `[h, map_mul, Units.val_mul, det_toReal_epsilon]`. Use `det_kGL_pos w hw` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem IsRefl.det_neg {x : archCompact ℚ 2} (hx : IsRefl x) : (kMat x).det.val < 0 := by
  obtain ⟨w, hw, -, h⟩ := hx
  rw [h, map_mul, Units.val_mul, det_toReal_epsilon]
  have := det_kGL_pos w hw
  linarith

/- English proof (translation)
The claim follows from `archToReal_mul _ _`.
-/
theorem kMat_mul (x y : archCompact ℚ 2) : kMat (x * y) = kMat x * kMat y :=
  archToReal_mul _ _

/- English proof (translation)
The claim follows from `(isRot_or_isRefl x).resolve_right fun hr => absurd hr.det_neg (not_lt.2 h.le)`.
-/
theorem isRot_of_det_pos {x : archCompact ℚ 2} (h : 0 < (kMat x).det.val) : IsRot x :=
  (isRot_or_isRefl x).resolve_right fun hr => absurd hr.det_neg (not_lt.2 h.le)

/- English proof (translation)
The claim follows from `(isRot_or_isRefl x).resolve_left fun hr => absurd hr.det_pos (not_lt.2 h.le)`.
-/
theorem isRefl_of_det_neg {x : archCompact ℚ 2} (h : (kMat x).det.val < 0) : IsRefl x :=
  (isRot_or_isRefl x).resolve_left fun hr => absurd hr.det_pos (not_lt.2 h.le)

/- English proof (translation)
Apply `isRefl_of_det_neg` to reduce the goal to its premises. Rewrite using `[kMat_mul, map_mul, Units.val_mul]`. Conclude with `mul_neg_of_pos_of_neg hx.det_pos hy.det_neg`.
-/
theorem IsRefl.mul_isRot {x y : archCompact ℚ 2} (hx : IsRot x) (hy : IsRefl y) : IsRefl (x * y) := by
  apply isRefl_of_det_neg
  rw [kMat_mul, map_mul, Units.val_mul]
  exact mul_neg_of_pos_of_neg hx.det_pos hy.det_neg

/- English proof (translation)
Apply `isRot_of_det_pos` to reduce the goal to its premises. Rewrite using `[kMat_mul, map_mul, Units.val_mul]`. Conclude with `mul_pos_of_neg_of_neg hx.det_neg hy.det_neg`.
-/
theorem IsRefl.mul_isRefl {x y : archCompact ℚ 2} (hx : IsRefl x) (hy : IsRefl y) : IsRot (x * y) := by
  apply isRot_of_det_pos
  rw [kMat_mul, map_mul, Units.val_mul]
  exact mul_pos_of_neg_of_neg hx.det_neg hy.det_neg

abbrev Rop : Module.End ℂ (cuspForms ℚ 2) := cuspOp raiseMat

abbrev Lop : Module.End ℂ (cuspForms ℚ 2) := cuspOp lowerMat

abbrev Jop : Module.End ℂ (cuspForms ℚ 2) := cuspOp rotMat

abbrev Zop : Module.End ℂ (cuspForms ℚ 2) := cuspOp 1

/- English proof (translation)
Use `cuspOp_smul 0 0` as an intermediate fact. Rewrite `this` using `[zero_smul, zero_smul]`. Then use the resulting hypothesis.
-/
theorem cuspOp_zero : cuspOp 0 = 0 := by
  have := cuspOp_smul 0 0
  rwa [zero_smul, zero_smul] at this

/- English proof (translation)
Rewrite using `[← cuspOp_lie, rot_raise, cuspOp_smul]`.
-/
theorem Jop_Rop : Jop * Rop - Rop * Jop = (2 * I) • Rop := by
  rw [← cuspOp_lie, rot_raise, cuspOp_smul]

/- English proof (translation)
Rewrite using `[← cuspOp_lie, lower_raise, cuspOp_smul]`.
-/
theorem Lop_Rop : Lop * Rop - Rop * Lop = (4 * I) • Jop := by
  rw [← cuspOp_lie, lower_raise, cuspOp_smul]

/- English proof (translation)
Use `congrArg (fun F : Module.End ℂ (cuspForms ℚ 2) => F ψ) (cuspOp_lie rotMat lowerMat)` as an intermediate fact. Rewrite `this` using `[rot_lower, cuspOp_smul]`. Simplify using `using this.symm`.
-/
theorem Jop_Lop_apply (ψ : cuspForms ℚ 2) : Jop (Lop ψ) - Lop (Jop ψ) = -((2 * I) • Lop ψ) := by
  have := congrArg (fun F : Module.End ℂ (cuspForms ℚ 2) => F ψ) (cuspOp_lie rotMat lowerMat)
  rw [rot_lower, cuspOp_smul] at this
  simpa using this.symm

/- English proof (translation)
Use `congrArg (fun F : Module.End ℂ (cuspForms ℚ 2) => F ψ) Lop_Rop` as an intermediate fact. Simplify using `using this`.
-/
theorem Lop_Rop_apply (ψ : cuspForms ℚ 2) : Lop (Rop ψ) - Rop (Lop ψ) = (4 * I) • Jop ψ := by
  have := congrArg (fun F : Module.End ℂ (cuspForms ℚ 2) => F ψ) Lop_Rop
  simpa using this

/- English proof (translation)
Use extensionality with `ψ : 1`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply, map_neg, LinearMap.smul_apply]`. Rewrite using `[show -(Jop (Lop ψ)) - -(Lop (Jop ψ)) = -(Jop (Lop ψ) - Lop (Jop ψ)) by abel, Jop_Lop_apply, neg_neg]`.
-/
theorem negJop_Lop : -Jop * Lop - Lop * -Jop = (2 * I) • Lop := by
  ext ψ : 1
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply, map_neg, LinearMap.smul_apply]
  rw [show -(Jop (Lop ψ)) - -(Lop (Jop ψ)) = -(Jop (Lop ψ) - Lop (Jop ψ)) by abel, Jop_Lop_apply, neg_neg]

/- English proof (translation)
Use extensionality with `ψ : 1`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply, LinearMap.smul_apply]`. Rewrite using `[show Rop (Lop ψ) - Lop (Rop ψ) = -(Lop (Rop ψ) - Rop (Lop ψ)) by abel, Lop_Rop_apply, smul_neg]`.
-/
theorem Rop_Lop : Rop * Lop - Lop * Rop = (4 * I) • -Jop := by
  ext ψ : 1
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply, LinearMap.smul_apply]
  rw [show Rop (Lop ψ) - Lop (Rop ψ) = -(Lop (Rop ψ) - Rop (Lop ψ)) by abel, Lop_Rop_apply, smul_neg]

/- English proof (translation)
Use `cuspOp_lie 1 B` as an intermediate fact. Rewrite `this` using `[Matrix.one_mul, Matrix.mul_one, sub_self, cuspOp_zero]`. Conclude with `sub_eq_zero.1 this.symm`.
-/
theorem Zop_commute (B : Matrix (Fin 2) (Fin 2) ℂ) : Commute Zop (cuspOp B) := by
  have := cuspOp_lie 1 B
  rw [Matrix.one_mul, Matrix.mul_one, sub_self, cuspOp_zero] at this
  exact sub_eq_zero.1 this.symm

abbrev σc (x : archCompact ℚ 2) : Module.End ℂ (cuspForms ℚ 2) := archCompactRepCusp ℚ 2 x

/- English proof (translation)
Rewrite using `[archCompactRepCusp_cuspOp x (B' := (starRingEnd ℂ w / w) • raiseMat) (by rw [kMatC_of_plus hK]; exact plus_raiseMat w hw), cuspOp_smul, LinearMap.smul_apply]`.
-/
theorem σc_Rop_rot {x : archCompact ℚ 2} {w : ℂ} {hw : w ≠ 0} (hK : kMat x = kGL w hw) (ψ : cuspForms ℚ 2) :
    σc x (Rop ψ) = (starRingEnd ℂ w / w) • Rop (σc x ψ) := by
  rw [archCompactRepCusp_cuspOp x (B' := (starRingEnd ℂ w / w) • raiseMat)
    (by rw [kMatC_of_plus hK]; exact plus_raiseMat w hw), cuspOp_smul, LinearMap.smul_apply]

/- English proof (translation)
Rewrite using `[archCompactRepCusp_cuspOp x (B' := (w / starRingEnd ℂ w) • lowerMat) (by rw [kMatC_of_plus hK]; exact plus_lowerMat w hw), cuspOp_smul, LinearMap.smul_apply]`.
-/
theorem σc_Lop_rot {x : archCompact ℚ 2} {w : ℂ} {hw : w ≠ 0} (hK : kMat x = kGL w hw) (ψ : cuspForms ℚ 2) :
    σc x (Lop ψ) = (w / starRingEnd ℂ w) • Lop (σc x ψ) := by
  rw [archCompactRepCusp_cuspOp x (B' := (w / starRingEnd ℂ w) • lowerMat)
    (by rw [kMatC_of_plus hK]; exact plus_lowerMat w hw), cuspOp_smul, LinearMap.smul_apply]

/- English proof (translation)
Rewrite using `[archCompactRepCusp_cuspOp x (B' := (-(starRingEnd ℂ w / w)) • lowerMat) (by rw [kMatC_of_minus hK]; exact minus_raiseMat w hw), cuspOp_smul, LinearMap.smul_apply]`.
-/
theorem σc_Rop_refl {x : archCompact ℚ 2} {w : ℂ} {hw : w ≠ 0} (hK : kMat x = toReal epsilon * kGL w hw)
    (ψ : cuspForms ℚ 2) : σc x (Rop ψ) = (-(starRingEnd ℂ w / w)) • Lop (σc x ψ) := by
  rw [archCompactRepCusp_cuspOp x (B' := (-(starRingEnd ℂ w / w)) • lowerMat)
    (by rw [kMatC_of_minus hK]; exact minus_raiseMat w hw), cuspOp_smul, LinearMap.smul_apply]

/- English proof (translation)
Rewrite using `[archCompactRepCusp_cuspOp x (B' := (-(w / starRingEnd ℂ w)) • raiseMat) (by rw [kMatC_of_minus hK]; exact minus_lowerMat w hw), cuspOp_smul, LinearMap.smul_apply]`.
-/
theorem σc_Lop_refl {x : archCompact ℚ 2} {w : ℂ} {hw : w ≠ 0} (hK : kMat x = toReal epsilon * kGL w hw)
    (ψ : cuspForms ℚ 2) : σc x (Lop ψ) = (-(w / starRingEnd ℂ w)) • Rop (σc x ψ) := by
  rw [archCompactRepCusp_cuspOp x (B' := (-(w / starRingEnd ℂ w)) • raiseMat)
    (by rw [kMatC_of_minus hK]; exact minus_lowerMat w hw), cuspOp_smul, LinearMap.smul_apply]

/- English proof (translation)
Rewrite using `[archCompactRepCusp_cuspOp x (B' := (-1 : ℂ) • rotMat) (by rw [kMatC_of_minus hK]; exact minus_rotMat w hw), cuspOp_smul, LinearMap.smul_apply]`.
-/
theorem σc_Jop_refl {x : archCompact ℚ 2} {w : ℂ} {hw : w ≠ 0} (hK : kMat x = toReal epsilon * kGL w hw)
    (ψ : cuspForms ℚ 2) : σc x (Jop ψ) = (-1 : ℂ) • Jop (σc x ψ) := by
  rw [archCompactRepCusp_cuspOp x (B' := (-1 : ℂ) • rotMat)
    (by rw [kMatC_of_minus hK]; exact minus_rotMat w hw), cuspOp_smul, LinearMap.smul_apply]

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih`. Rewrite using `[pow_succ' B j, Module.End.mul_apply, h, ih, map_smul, smul_smul, pow_succ' B' j, Module.End.mul_apply, pow_succ' c j]`.
-/
theorem σc_pow {x : archCompact ℚ 2} {B B' : Module.End ℂ (cuspForms ℚ 2)} {c : ℂ}
    (h : ∀ ψ, σc x (B ψ) = c • B' (σc x ψ)) (j : ℕ) (ψ : cuspForms ℚ 2) :
    σc x ((B ^ j) ψ) = c ^ j • (B' ^ j) (σc x ψ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ' B j, Module.End.mul_apply, h, ih, map_smul, smul_smul, pow_succ' B' j, Module.End.mul_apply,
      pow_succ' c j]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [raiseMat, lowerMat, rotMat] <;> ring_nf <;> simp only [I_sq] <;> ring`.
-/
theorem matrix_eq_combo (B : Matrix (Fin 2) (Fin 2) ℂ) :
    B = (((B 0 1 + B 1 0) / 2 + I * (B 0 0 - B 1 1) / 2) / 2) • raiseMat +
      (((B 0 1 + B 1 0) / 2 - I * (B 0 0 - B 1 1) / 2) / 2) • lowerMat +
      ((B 0 1 - B 1 0) / 2) • rotMat + ((B 0 0 + B 1 1) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [raiseMat, lowerMat, rotMat] <;> ring_nf <;> simp only [I_sq] <;> ring

/- English proof (translation)
Use `conv_lhs => rw [matrix_eq_combo B]`. Simplify using `only [cuspOp_add, cuspOp_smul]`.
-/
theorem cuspOp_eq_combo (B : Matrix (Fin 2) (Fin 2) ℂ) :
    cuspOp B = (((B 0 1 + B 1 0) / 2 + I * (B 0 0 - B 1 1) / 2) / 2) • Rop +
      (((B 0 1 + B 1 0) / 2 - I * (B 0 0 - B 1 1) / 2) / 2) • Lop +
      ((B 0 1 - B 1 0) / 2) • Jop + ((B 0 0 + B 1 1) / 2) • Zop := by
  conv_lhs => rw [matrix_eq_combo B]
  simp only [cuspOp_add, cuspOp_smul]

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih => rw [pow_succ', Module.End.mul_apply, ih, cuspOp_finRepCusp, Module.End.mul_apply]`.
-/
theorem cuspOp_pow_finRepCusp (B : Matrix (Fin 2) (Fin 2) ℂ) (j : ℕ) (g : FiniteAdelicGL ℚ 2)
    (ψ : cuspForms ℚ 2) : (cuspOp B ^ j) (finRepCusp ℚ 2 g ψ) = finRepCusp ℚ 2 g ((cuspOp B ^ j) ψ) := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', Module.End.mul_apply, ih, cuspOp_finRepCusp, Module.End.mul_apply]

/- English proof (translation)
The claim follows from `gkModuleCusp_σ_finRepCusp x g ψ`.
-/
theorem σc_finRepCusp (x : archCompact ℚ 2) (g : FiniteAdelicGL ℚ 2) (ψ : cuspForms ℚ 2) :
    σc x (finRepCusp ℚ 2 g ψ) = finRepCusp ℚ 2 g (σc x ψ) :=
  gkModuleCusp_σ_finRepCusp x g ψ

/- English proof (translation)
Rewrite using `[σc, σc, σc, map_mul, Module.End.mul_apply]`.
-/
theorem σc_mul_apply (x y : archCompact ℚ 2) (ψ : cuspForms ℚ 2) : σc x (σc y ψ) = σc (x * y) ψ := by
  rw [σc, σc, σc, map_mul, Module.End.mul_apply]

section Span

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)

/- English proof (translation)
Rewrite using `[cuspOp_translateSpanCusp f holCoeff_lowerMat ht, weightChar_lowerMat, zero_smul]`.
-/
theorem Lop_T {t : cuspForms ℚ 2} (ht : t ∈ translateSpanCusp f) : Lop t = 0 := by
  rw [cuspOp_translateSpanCusp f holCoeff_lowerMat ht, weightChar_lowerMat, zero_smul]

/- English proof (translation)
Rewrite using `[cuspOp_translateSpanCusp f holCoeff_rotMat ht, weightChar_rotMat]`.
-/
theorem Jop_T {t : cuspForms ℚ 2} (ht : t ∈ translateSpanCusp f) : Jop t = (I * k) • t := by
  rw [cuspOp_translateSpanCusp f holCoeff_rotMat ht, weightChar_rotMat]

/- English proof (translation)
Rewrite using `[cuspOp_translateSpanCusp f holCoeff_one ht, weightChar_one, zero_smul]`.
-/
theorem Zop_T {t : cuspForms ℚ 2} (ht : t ∈ translateSpanCusp f) : Zop t = 0 := by
  rw [cuspOp_translateSpanCusp f holCoeff_one ht, weightChar_one, zero_smul]

def reflSpan : Submodule ℂ (cuspForms ℚ 2) :=
  Submodule.span ℂ {v | ∃ x, IsRefl x ∧ ∃ t ∈ translateSpanCusp f, v = σc x t}

/- English proof (translation)
Proceed by induction on `hs using Submodule.span_induction with`. Consider the case `mem v hv`. Take `⟨x, hx, t, ht, rfl⟩` from `hv`. Conclude with `hgen x hx t ht`. Consider the case `zero => exact h0`.

Consider the case `add a b _ _ ha hb => exact hadd a b ha hb`. Consider the case `smul c a _ ha => exact hsmul c a ha`.
-/
theorem reflSpan_induction {P : cuspForms ℚ 2 → Prop} (h0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b))
    (hsmul : ∀ (c : ℂ) a, P a → P (c • a))
    (hgen : ∀ x, IsRefl x → ∀ t ∈ translateSpanCusp f, P (σc x t)) {s : cuspForms ℚ 2} (hs : s ∈ reflSpan f) :
    P s := by
  induction hs using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨x, hx, t, ht, rfl⟩ := hv
    exact hgen x hx t ht
  | zero => exact h0
  | add a b _ _ ha hb => exact hadd a b ha hb
  | smul c a _ ha => exact hsmul c a ha

/- English proof (translation)
Use `reflSpan_induction f (P := fun s => Rop s = 0) (map_zero _) (fun a b ha hb => by rw [map_add, ha, hb, add_zero]) (fun c a ha => by rw [map_smul, ha, smul_zero]) (fun x hx t ht => ?_) hs` and prove the remaining obligations. Take `⟨w, hw, -, hK⟩` from `hx`. Establish `h` using `σc_Lop_refl hK t`. Rewrite `h` using `[Lop_T f ht, map_zero]`. Establish `hc : (-(w / starRingEnd ℂ w)) ≠ 0` using `neg_ne_zero.2 (div_ne_zero hw (conj_ne_zero' hw))`.

Conclude with `(smul_eq_zero.1 h.symm).resolve_left hc`.
-/
theorem Rop_reflSpan {s : cuspForms ℚ 2} (hs : s ∈ reflSpan f) : Rop s = 0 := by
  refine reflSpan_induction f (P := fun s => Rop s = 0) (map_zero _) (fun a b ha hb => by rw [map_add, ha, hb, add_zero])
    (fun c a ha => by rw [map_smul, ha, smul_zero]) (fun x hx t ht => ?_) hs
  obtain ⟨w, hw, -, hK⟩ := hx
  have h := σc_Lop_refl hK t
  rw [Lop_T f ht, map_zero] at h
  have hc : (-(w / starRingEnd ℂ w)) ≠ 0 := neg_ne_zero.2 (div_ne_zero hw (conj_ne_zero' hw))
  exact (smul_eq_zero.1 h.symm).resolve_left hc

/- English proof (translation)
Use `reflSpan_induction f (P := fun s => (-Jop) s = (I * k) • s) (by simp) (fun a b ha hb => by rw [map_add, ha, hb, smul_add]) (fun c a ha => by rw [map_smul, ha, smul_comm]) (fun x hx t ht => ?_) hs` and prove the remaining obligations. Take `⟨w, hw, -, hK⟩` from `hx`. Establish `h` using `σc_Jop_refl hK t`. Rewrite `h` using `[Jop_T f ht, map_smul]`. Rewrite using `[LinearMap.neg_apply, h]`.

Conclude with `(neg_one_smul ℂ _).symm`.
-/
theorem negJop_reflSpan {s : cuspForms ℚ 2} (hs : s ∈ reflSpan f) : (-Jop) s = (I * k) • s := by
  refine reflSpan_induction f (P := fun s => (-Jop) s = (I * k) • s) (by simp) (fun a b ha hb => by rw [map_add, ha, hb, smul_add])
    (fun c a ha => by rw [map_smul, ha, smul_comm]) (fun x hx t ht => ?_) hs
  obtain ⟨w, hw, -, hK⟩ := hx
  have h := σc_Jop_refl hK t
  rw [Jop_T f ht, map_smul] at h
  rw [LinearMap.neg_apply, h]
  exact (neg_one_smul ℂ _).symm

/- English proof (translation)
Use `reflSpan_induction f (P := fun s => Zop s = 0) (map_zero _) (fun a b ha hb => by rw [map_add, ha, hb, add_zero]) (fun c a ha => by rw [map_smul, ha, smul_zero]) (fun x _ t ht => ?_) hs` and prove the remaining obligations. Rewrite using `[← archCompactRepCusp_cuspOp_one, Zop_T f ht, map_zero]`.
-/
theorem Zop_reflSpan {s : cuspForms ℚ 2} (hs : s ∈ reflSpan f) : Zop s = 0 := by
  refine reflSpan_induction f (P := fun s => Zop s = 0) (map_zero _) (fun a b ha hb => by rw [map_add, ha, hb, add_zero])
    (fun c a ha => by rw [map_smul, ha, smul_zero]) (fun x _ t ht => ?_) hs
  rw [← archCompactRepCusp_cuspOp_one, Zop_T f ht, map_zero]

def weightPiece : ℕ ⊕ ℕ → Submodule ℂ (cuspForms ℚ 2)
  | Sum.inl j => (translateSpanCusp f).map (Rop ^ j)
  | Sum.inr j => (reflSpan f).map (Lop ^ j)

def weightSpan : Submodule ℂ (cuspForms ℚ 2) := ⨆ i, weightPiece f i

variable (k) in

def weightEig : ℕ ⊕ ℕ → ℂ
  | Sum.inl j => I * k + 2 * I * j
  | Sum.inr j => -(I * k + 2 * I * j)

/- English proof (translation)
Break down `i with j | j` into its components or cases. Take `⟨t, ht, rfl⟩` from `hv`. Conclude with `J_pow_apply Jop_Rop (Jop_T f ht) j`. Take `⟨s, hs, rfl⟩` from `hv`. Use `J_pow_apply negJop_Lop (negJop_reflSpan f hs) j` as an intermediate fact.

Rewrite `this` using `[LinearMap.neg_apply, neg_eq_iff_eq_neg, ← _root_.neg_smul]`. Conclude with `this`.
-/
theorem Jop_weightPiece {i : ℕ ⊕ ℕ} {v : cuspForms ℚ 2} (hv : v ∈ weightPiece f i) :
    Jop v = weightEig k i • v := by
  rcases i with j | j
  · obtain ⟨t, ht, rfl⟩ := hv
    exact J_pow_apply Jop_Rop (Jop_T f ht) j
  · obtain ⟨s, hs, rfl⟩ := hv
    have := J_pow_apply negJop_Lop (negJop_reflSpan f hs) j
    rw [LinearMap.neg_apply, neg_eq_iff_eq_neg, ← _root_.neg_smul] at this
    exact this

/- English proof (translation)
Establish `hk' : (0 : ℝ) < k` using `by exact_mod_cast hk`. Apply the tactic sequence `rintro (j | j) (j' | j') h <;> simp only [weightEig, Complex.ext_iff] at h <;>`. Simplify using `at h`. Conclude with `congrArg Sum.inl h`. Establish `: (0 : ℝ) ≤ j` using `Nat.cast_nonneg j`.

Establish `: (0 : ℝ) ≤ j'` using `Nat.cast_nonneg j'`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: (0 : ℝ) ≤ j` using `Nat.cast_nonneg j`. Establish `: (0 : ℝ) ≤ j'` using `Nat.cast_nonneg j'`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `congrArg Sum.inr h`.
-/
theorem weightEig_injective (hk : 0 < k) : Function.Injective (weightEig k) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rintro (j | j) (j' | j') h <;> simp only [weightEig, Complex.ext_iff] at h <;>
    simp at h
  · exact congrArg Sum.inl h
  · have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have : (0 : ℝ) ≤ j' := Nat.cast_nonneg j'
    linarith
  · have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have : (0 : ℝ) ≤ j' := Nat.cast_nonneg j'
    linarith
  · exact congrArg Sum.inr h

end Span

section Stable

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)

/- English proof (translation)
The claim follows from `(le_iSup (weightPiece f) i) hv`.
-/
theorem mem_weightSpan_of_mem {i : ℕ ⊕ ℕ} {v : cuspForms ℚ 2} (hv : v ∈ weightPiece f i) : v ∈ weightSpan f :=
  (le_iSup (weightPiece f) i) hv

/- English proof (translation)
Introduce `v hv`. Establish `: weightSpan f ≤ (weightSpan f).comap op` using `iSup_le fun i w hw => h i w hw`. Conclude with `this hv`.
-/
theorem weightSpan_map_mem (op : Module.End ℂ (cuspForms ℚ 2))
    (h : ∀ i, ∀ v ∈ weightPiece f i, op v ∈ weightSpan f) : ∀ v ∈ weightSpan f, op v ∈ weightSpan f := by
  intro v hv
  have : weightSpan f ≤ (weightSpan f).comap op := iSup_le fun i w hw => h i w hw
  exact this hv

/- English proof (translation)
The claim follows from `mem_weightSpan_of_mem f (i := Sum.inl j) ⟨t, ht, rfl⟩`.
-/
theorem Rop_pow_mem (j : ℕ) {t : cuspForms ℚ 2} (ht : t ∈ translateSpanCusp f) : (Rop ^ j) t ∈ weightSpan f :=
  mem_weightSpan_of_mem f (i := Sum.inl j) ⟨t, ht, rfl⟩

/- English proof (translation)
The claim follows from `mem_weightSpan_of_mem f (i := Sum.inr j) ⟨s, hs, rfl⟩`.
-/
theorem Lop_pow_mem (j : ℕ) {s : cuspForms ℚ 2} (hs : s ∈ reflSpan f) : (Lop ^ j) s ∈ weightSpan f :=
  mem_weightSpan_of_mem f (i := Sum.inr j) ⟨s, hs, rfl⟩

/- English proof (translation)
Use `weightSpan_map_mem f Rop fun i v hv => ?_` and prove the remaining obligations. Break down `i with j | j` into its components or cases. Take `⟨t, ht, rfl⟩` from `hv`. Rewrite using `[← Module.End.mul_apply, ← pow_succ']`. Conclude with `Rop_pow_mem f _ ht`.

Take `⟨s, hs, rfl⟩` from `hv`. Consider the cases of `j with`. Consider the case `zero`. Rewrite using `[pow_zero, Module.End.one_apply, Rop_reflSpan f hs]`. Conclude with `zero_mem _`.

Consider the case `succ m`. Rewrite using `[L_pow_succ_apply negJop_Lop Rop_Lop (negJop_reflSpan f hs) (Rop_reflSpan f hs) m]`. Conclude with `Submodule.smul_mem _ _ (Lop_pow_mem f m hs)`.
-/
theorem Rop_weightSpan : ∀ v ∈ weightSpan f, Rop v ∈ weightSpan f := by
  refine weightSpan_map_mem f Rop fun i v hv => ?_
  rcases i with j | j
  · obtain ⟨t, ht, rfl⟩ := hv
    rw [← Module.End.mul_apply, ← pow_succ']
    exact Rop_pow_mem f _ ht
  · obtain ⟨s, hs, rfl⟩ := hv
    cases j with
    | zero =>
      rw [pow_zero, Module.End.one_apply, Rop_reflSpan f hs]
      exact zero_mem _
    | succ m =>
      rw [L_pow_succ_apply negJop_Lop Rop_Lop (negJop_reflSpan f hs) (Rop_reflSpan f hs) m]
      exact Submodule.smul_mem _ _ (Lop_pow_mem f m hs)

/- English proof (translation)
Use `weightSpan_map_mem f Lop fun i v hv => ?_` and prove the remaining obligations. Break down `i with j | j` into its components or cases. Take `⟨t, ht, rfl⟩` from `hv`. Consider the cases of `j with`. Consider the case `zero`.

Rewrite using `[pow_zero, Module.End.one_apply, Lop_T f ht]`. Conclude with `zero_mem _`. Consider the case `succ m`. Rewrite using `[L_pow_succ_apply Jop_Rop Lop_Rop (Jop_T f ht) (Lop_T f ht) m]`. Conclude with `Submodule.smul_mem _ _ (Rop_pow_mem f m ht)`.

Take `⟨s, hs, rfl⟩` from `hv`. Rewrite using `[← Module.End.mul_apply, ← pow_succ']`. Conclude with `Lop_pow_mem f _ hs`.
-/
theorem Lop_weightSpan : ∀ v ∈ weightSpan f, Lop v ∈ weightSpan f := by
  refine weightSpan_map_mem f Lop fun i v hv => ?_
  rcases i with j | j
  · obtain ⟨t, ht, rfl⟩ := hv
    cases j with
    | zero =>
      rw [pow_zero, Module.End.one_apply, Lop_T f ht]
      exact zero_mem _
    | succ m =>
      rw [L_pow_succ_apply Jop_Rop Lop_Rop (Jop_T f ht) (Lop_T f ht) m]
      exact Submodule.smul_mem _ _ (Rop_pow_mem f m ht)
  · obtain ⟨s, hs, rfl⟩ := hv
    rw [← Module.End.mul_apply, ← pow_succ']
    exact Lop_pow_mem f _ hs

/- English proof (translation)
Use `weightSpan_map_mem f Jop fun i v hv => ?_` and prove the remaining obligations. Rewrite using `[Jop_weightPiece f hv]`. Conclude with `Submodule.smul_mem _ _ (mem_weightSpan_of_mem f hv)`.
-/
theorem Jop_weightSpan : ∀ v ∈ weightSpan f, Jop v ∈ weightSpan f := by
  refine weightSpan_map_mem f Jop fun i v hv => ?_
  rw [Jop_weightPiece f hv]
  exact Submodule.smul_mem _ _ (mem_weightSpan_of_mem f hv)

/- English proof (translation)
Use `weightSpan_map_mem f Zop fun i v hv => ?_` and prove the remaining obligations. Break down `i with j | j` into its components or cases. Take `⟨t, ht, rfl⟩` from `hv`. Establish `hc` using `((Zop_commute raiseMat).pow_right j).eq`. Rewrite using `[← Module.End.mul_apply, hc, Module.End.mul_apply, Zop_T f ht, map_zero]`.

Conclude with `zero_mem _`. Take `⟨s, hs, rfl⟩` from `hv`. Establish `hc` using `((Zop_commute lowerMat).pow_right j).eq`. Rewrite using `[← Module.End.mul_apply, hc, Module.End.mul_apply, Zop_reflSpan f hs, map_zero]`. Conclude with `zero_mem _`.
-/
theorem Zop_weightSpan : ∀ v ∈ weightSpan f, Zop v ∈ weightSpan f := by
  refine weightSpan_map_mem f Zop fun i v hv => ?_
  rcases i with j | j
  · obtain ⟨t, ht, rfl⟩ := hv
    have hc := ((Zop_commute raiseMat).pow_right j).eq
    rw [← Module.End.mul_apply, hc, Module.End.mul_apply, Zop_T f ht, map_zero]
    exact zero_mem _
  · obtain ⟨s, hs, rfl⟩ := hv
    have hc := ((Zop_commute lowerMat).pow_right j).eq
    rw [← Module.End.mul_apply, hc, Module.End.mul_apply, Zop_reflSpan f hs, map_zero]
    exact zero_mem _

/- English proof (translation)
Introduce `v hv`. Rewrite using `[cuspOp_eq_combo]`. Simplify using `only [LinearMap.add_apply, LinearMap.smul_apply]`. Apply the tactic sequence `refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_ <;> refine Submodule.smul_mem _ _ ?_`. Conclude with `Rop_weightSpan f v hv`.

Conclude with `Lop_weightSpan f v hv`. Conclude with `Jop_weightSpan f v hv`. Conclude with `Zop_weightSpan f v hv`.
-/
theorem cuspOp_weightSpan (B : Matrix (Fin 2) (Fin 2) ℂ) :
    ∀ v ∈ weightSpan f, cuspOp B v ∈ weightSpan f := by
  intro v hv
  rw [cuspOp_eq_combo]
  simp only [LinearMap.add_apply, LinearMap.smul_apply]
  refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_ <;> refine Submodule.smul_mem _ _ ?_
  · exact Rop_weightSpan f v hv
  · exact Lop_weightSpan f v hv
  · exact Jop_weightSpan f v hv
  · exact Zop_weightSpan f v hv

/- English proof (translation)
Use `weightSpan_map_mem f (σc x) fun i v hv => ?_` and prove the remaining obligations. Break down `i with j | j` into its components or cases. Take `⟨t, ht, rfl⟩` from `hv`. Break down `isRot_or_isRefl x with ⟨w, hw, h1, hK⟩ | ⟨w, hw, h1, hK⟩` into its components or cases. Rewrite using `[σc_pow (σc_Rop_rot hK) j t, archCompactRepCusp_translateSpanCusp f x hw h1 hK ht, map_smul]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Rop_pow_mem f j ht))`. Rewrite using `[σc_pow (σc_Rop_refl hK) j t]`. Conclude with `Submodule.smul_mem _ _ (Lop_pow_mem f j (Submodule.subset_span ⟨x, ⟨w, hw, h1, hK⟩, t, ht, rfl⟩))`. Take `⟨s, hs, rfl⟩` from `hv`. Use `reflSpan_induction f (P := fun s => σc x ((Lop ^ j) s) ∈ weightSpan f) (by rw [map_zero, map_zero]; exact zero_mem _) (fun a b ha hb => by rw [map_add, map_add]; exact add_mem ha hb) (fun c a ha => by rw [map_smul, map_smul]; exact Submodule.smul_mem _ _ ha) (fun y hy t ht => ?_) …` and prove the remaining obligations.

Break down `isRot_or_isRefl x with ⟨w, hw, h1, hK⟩ | ⟨w, hw, h1, hK⟩` into its components or cases. Rewrite using `[σc_pow (σc_Lop_rot hK) j, σc_mul_apply]`. Establish `hxy : IsRefl (x * y)` using `IsRefl.mul_isRot ⟨w, hw, h1, hK⟩ hy`. Conclude with `Submodule.smul_mem _ _ (Lop_pow_mem f j (Submodule.subset_span ⟨x * y, hxy, t, ht, rfl⟩))`. Rewrite using `[σc_pow (σc_Lop_refl hK) j, σc_mul_apply]`.

Take `⟨w', hw', h1', hK'⟩` from `IsRefl.mul_isRefl ⟨w, hw, h1, hK⟩ hy`. Rewrite using `[archCompactRepCusp_translateSpanCusp f (x * y) hw' h1' hK' ht, map_smul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Rop_pow_mem f j ht))`.
-/
theorem σc_weightSpan (x : archCompact ℚ 2) : ∀ v ∈ weightSpan f, σc x v ∈ weightSpan f := by
  refine weightSpan_map_mem f (σc x) fun i v hv => ?_
  rcases i with j | j
  · obtain ⟨t, ht, rfl⟩ := hv
    rcases isRot_or_isRefl x with ⟨w, hw, h1, hK⟩ | ⟨w, hw, h1, hK⟩
    · rw [σc_pow (σc_Rop_rot hK) j t, archCompactRepCusp_translateSpanCusp f x hw h1 hK ht, map_smul]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Rop_pow_mem f j ht))
    · rw [σc_pow (σc_Rop_refl hK) j t]
      exact Submodule.smul_mem _ _ (Lop_pow_mem f j (Submodule.subset_span ⟨x, ⟨w, hw, h1, hK⟩, t, ht, rfl⟩))
  · obtain ⟨s, hs, rfl⟩ := hv
    refine reflSpan_induction f (P := fun s => σc x ((Lop ^ j) s) ∈ weightSpan f)
      (by rw [map_zero, map_zero]; exact zero_mem _)
      (fun a b ha hb => by rw [map_add, map_add]; exact add_mem ha hb)
      (fun c a ha => by rw [map_smul, map_smul]; exact Submodule.smul_mem _ _ ha) (fun y hy t ht => ?_) hs
    rcases isRot_or_isRefl x with ⟨w, hw, h1, hK⟩ | ⟨w, hw, h1, hK⟩
    · rw [σc_pow (σc_Lop_rot hK) j, σc_mul_apply]
      have hxy : IsRefl (x * y) := IsRefl.mul_isRot ⟨w, hw, h1, hK⟩ hy
      exact Submodule.smul_mem _ _ (Lop_pow_mem f j (Submodule.subset_span ⟨x * y, hxy, t, ht, rfl⟩))
    · rw [σc_pow (σc_Lop_refl hK) j, σc_mul_apply]
      obtain ⟨w', hw', h1', hK'⟩ := IsRefl.mul_isRefl ⟨w, hw, h1, hK⟩ hy
      rw [archCompactRepCusp_translateSpanCusp f (x * y) hw' h1' hK' ht, map_smul]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Rop_pow_mem f j ht))

/- English proof (translation)
Use `reflSpan_induction f (P := fun s => finRepCusp ℚ 2 g s ∈ reflSpan f) (by rw [map_zero]; exact zero_mem _) (fun a b ha hb => by rw [map_add]; exact add_mem ha hb) (fun c a ha => by rw [map_smul]; exact Submodule.smul_mem _ _ ha) (fun y hy t ht => ?_) hs` and prove the remaining obligations. Rewrite using `[← σc_finRepCusp]`. Conclude with `Submodule.subset_span ⟨y, hy, _, finRepCusp_mem_translateSpanCusp f g ht, rfl⟩`.
-/
theorem finRepCusp_reflSpan (g : FiniteAdelicGL ℚ 2) {s : cuspForms ℚ 2} (hs : s ∈ reflSpan f) :
    finRepCusp ℚ 2 g s ∈ reflSpan f := by
  refine reflSpan_induction f (P := fun s => finRepCusp ℚ 2 g s ∈ reflSpan f)
    (by rw [map_zero]; exact zero_mem _) (fun a b ha hb => by rw [map_add]; exact add_mem ha hb)
    (fun c a ha => by rw [map_smul]; exact Submodule.smul_mem _ _ ha) (fun y hy t ht => ?_) hs
  rw [← σc_finRepCusp]
  exact Submodule.subset_span ⟨y, hy, _, finRepCusp_mem_translateSpanCusp f g ht, rfl⟩

/- English proof (translation)
Use `weightSpan_map_mem f (finRepCusp ℚ 2 g) fun i v hv => ?_` and prove the remaining obligations. Break down `i with j | j` into its components or cases. Take `⟨t, ht, rfl⟩` from `hv`. Rewrite using `[← cuspOp_pow_finRepCusp]`. Conclude with `Rop_pow_mem f j (finRepCusp_mem_translateSpanCusp f g ht)`.

Take `⟨s, hs, rfl⟩` from `hv`. Rewrite using `[← cuspOp_pow_finRepCusp]`. Conclude with `Lop_pow_mem f j (finRepCusp_reflSpan f g hs)`.
-/
theorem finRepCusp_weightSpan (g : FiniteAdelicGL ℚ 2) :
    ∀ v ∈ weightSpan f, finRepCusp ℚ 2 g v ∈ weightSpan f := by
  refine weightSpan_map_mem f (finRepCusp ℚ 2 g) fun i v hv => ?_
  rcases i with j | j
  · obtain ⟨t, ht, rfl⟩ := hv
    rw [← cuspOp_pow_finRepCusp]
    exact Rop_pow_mem f j (finRepCusp_mem_translateSpanCusp f g ht)
  · obtain ⟨s, hs, rfl⟩ := hv
    rw [← cuspOp_pow_finRepCusp]
    exact Lop_pow_mem f j (finRepCusp_reflSpan f g hs)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun X v hv => by rw [gkModuleCusp_ρ_eq_cuspOp]; exact cuspOp_weightSpan f _ v hv, fun x v hv => σc_weightSpan f x v hv, fun g v hv => finRepCusp_weightSpan f g v hv⟩`.
-/
theorem isGKFStable_weightSpan : IsGKFStable (weightSpan f) :=
  ⟨fun X v hv => by rw [gkModuleCusp_ρ_eq_cuspOp]; exact cuspOp_weightSpan f _ v hv,
    fun x v hv => σc_weightSpan f x v hv, fun g v hv => finRepCusp_weightSpan f g v hv⟩

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨1, by show finRepCusp ℚ 2 1 (liftCusp f) = _; rw [map_one, Module.End.one_apply]⟩`.
-/
theorem liftCusp_mem_translateSpanCusp : liftCusp f ∈ translateSpanCusp f :=
  Submodule.subset_span ⟨1, by show finRepCusp ℚ 2 1 (liftCusp f) = _; rw [map_one, Module.End.one_apply]⟩

/- English proof (translation)
Use `Rop_pow_mem f 0 (liftCusp_mem_translateSpanCusp f)` as an intermediate fact. Rewrite `this` using `[pow_zero, Module.End.one_apply]`. Then use the resulting hypothesis.
-/
theorem liftCusp_mem_weightSpan : liftCusp f ∈ weightSpan f := by
  have := Rop_pow_mem f 0 (liftCusp_mem_translateSpanCusp f)
  rwa [pow_zero, Module.End.one_apply] at this

/- English proof (translation)
The claim follows from `gkfSpan_le (isGKFStable_weightSpan f) (liftCusp_mem_weightSpan f)`.
-/
theorem gkfSpan_le_weightSpan : gkfSpan (liftCusp f) ≤ weightSpan f :=
  gkfSpan_le (isGKFStable_weightSpan f) (liftCusp_mem_weightSpan f)

end Stable

section Extract

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)

/- English proof (translation)
Rewrite using `[σc_mul_apply, inv_mul_cancel, σc, map_one, Module.End.one_apply]`.
-/
theorem σc_inv_apply (y : archCompact ℚ 2) (ψ : cuspForms ℚ 2) : σc y⁻¹ (σc y ψ) = ψ := by
  rw [σc_mul_apply, inv_mul_cancel, σc, map_one, Module.End.one_apply]

/- English proof (translation)
Use `reflSpan_induction f (P := fun s => σc y s ∈ translateSpanCusp f) (by rw [map_zero]; exact zero_mem _) (fun a b ha hb => by rw [map_add]; exact add_mem ha hb) (fun c a ha => by rw [map_smul]; exact Submodule.smul_mem _ _ ha) (fun x hx t ht => ?_) hs` and prove the remaining obligations. Rewrite using `[σc_mul_apply]`. Take `⟨w, hw, h1, hK⟩` from `IsRefl.mul_isRefl hy hx`. Rewrite using `[archCompactRepCusp_translateSpanCusp f (y * x) hw h1 hK ht]`. Conclude with `Submodule.smul_mem _ _ ht`.
-/
theorem σc_refl_reflSpan {y : archCompact ℚ 2} (hy : IsRefl y) {s : cuspForms ℚ 2} (hs : s ∈ reflSpan f) :
    σc y s ∈ translateSpanCusp f := by
  refine reflSpan_induction f (P := fun s => σc y s ∈ translateSpanCusp f)
    (by rw [map_zero]; exact zero_mem _) (fun a b ha hb => by rw [map_add]; exact add_mem ha hb)
    (fun c a ha => by rw [map_smul]; exact Submodule.smul_mem _ _ ha) (fun x hx t ht => ?_) hs
  rw [σc_mul_apply]
  obtain ⟨w, hw, h1, hK⟩ := IsRefl.mul_isRefl hy hx
  rw [archCompactRepCusp_translateSpanCusp f (y * x) hw h1 hK ht]
  exact Submodule.smul_mem _ _ ht

/- English proof (translation)
Assume the negation of the conclusion as `h`. Establish `h' : ∀ y, ¬ IsRefl y` using `fun y hy => h ⟨y, hy⟩`. Establish `hbot : reflSpan f = ⊥`. Rewrite using `[reflSpan, Submodule.span_eq_bot]`. Introduce and unpack `v ⟨x, hx, -⟩`.

Conclude with `absurd hx (h' x)`. Rewrite `hs` using `[hbot]`. Conclude with `hs0 ((Submodule.mem_bot ℂ).1 hs)`.
-/
theorem exists_isRefl_of_mem_reflSpan {s : cuspForms ℚ 2} (hs : s ∈ reflSpan f) (hs0 : s ≠ 0) :
    ∃ y, IsRefl y := by
  by_contra h
  have h' : ∀ y, ¬ IsRefl y := fun y hy => h ⟨y, hy⟩
  have hbot : reflSpan f = ⊥ := by
    rw [reflSpan, Submodule.span_eq_bot]
    rintro v ⟨x, hx, -⟩
    exact absurd hx (h' x)
  rw [hbot] at hs
  exact hs0 ((Submodule.mem_bot ℂ).1 hs)

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simpa using hv`. Consider the case `succ j ih => rw [pow_succ', Module.End.mul_apply]`. Conclude with `hW.cuspOp_mem B ih`.
-/
theorem IsGKFStable.cuspOp_pow_mem {W : Submodule ℂ (cuspForms ℚ 2)} (hW : IsGKFStable W)
    (B : Matrix (Fin 2) (Fin 2) ℂ) (j : ℕ) {v : cuspForms ℚ 2} (hv : v ∈ W) :
    (GL2Classical.cuspOp B ^ j) v ∈ W := by
  induction j with
  | zero => simpa using hv
  | succ j ih => rw [pow_succ', Module.End.mul_apply]; exact hW.cuspOp_mem B ih

/- English proof (translation)
Take `⟨w, hwW, hw0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hW0`. Take `⟨F, hF, hsum⟩` from `(Submodule.mem_iSup_iff_exists_finsupp (weightPiece f) w).1 (hWV hwW)`. Establish `hJW : ∀ v ∈ W, Jop v ∈ W` using `fun v hv => hW.cuspOp_mem rotMat hv`. Establish `hcomp` using `mem_of_sum_mem_of_eigen hJW F.support F (weightEig k) (fun i _ => Jop_weightPiece f (hF i)) ((weightEig_injective hk).injOn) (by rw [← hsum] at hwW; exact hwW)`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : F.support.Nonempty := by`.

Rewrite using `[Finset.nonempty_iff_ne_empty]`. Introduce `he`. Apply `hw0` to reduce the goal to its premises. Rewrite using `[← hsum, Finsupp.sum, he, Finset.sum_empty]`. Establish `hFiW` using `hcomp i hi`.

Establish `hFi0 : F i ≠ 0` using `Finsupp.mem_support_iff.1 hi`. Break down `i with j | j` into its components or cases. Establish `hFj : F (Sum.inl j) ∈ (translateSpanCusp f).map (Rop ^ j)` using `hF (Sum.inl j)`. Take `⟨t, ht, hte⟩` from `hFj`. Rewrite `hFiW`, `hFi0` using `[← hte]`.

Establish `h1` using `L_pow_R_pow_apply Jop_Rop Lop_Rop (Jop_T f ht) (Lop_T f ht) j`. Establish `hc` using `prod_ne_zero_of_pos hk j`. Establish `ht0 : t ≠ 0` using `fun h => hFi0 (by rw [h, map_zero])`. Use `⟨t, ht, ht0, ?_⟩` and prove the remaining obligations. Establish `h2` using `hW.cuspOp_pow_mem lowerMat j hFiW`.

Rewrite `h2` using `[h1]`. Establish `h3` using `Submodule.smul_mem W (∏ m ∈ Finset.range j, (4 * I * (m + 1) * (I * k + I * m)))⁻¹ h2`. Rewrite `h3` using `[smul_smul, inv_mul_cancel₀ hc, one_smul]`. Then use the resulting hypothesis. Establish `hFj : F (Sum.inr j) ∈ (reflSpan f).map (Lop ^ j)` using `hF (Sum.inr j)`. Take `⟨s, hs, hse⟩` from `hFj`.

Rewrite `hFiW`, `hFi0` using `[← hse]`. Establish `h1` using `L_pow_R_pow_apply negJop_Lop Rop_Lop (negJop_reflSpan f hs) (Rop_reflSpan f hs) j`. Establish `hc` using `prod_ne_zero_of_pos hk j`. Establish `hs0 : s ≠ 0` using `fun h => hFi0 (by rw [h, map_zero])`. Establish `h2` using `hW.cuspOp_pow_mem raiseMat j hFiW`.

Rewrite `h2` using `[h1]`. Establish `h3` using `Submodule.smul_mem W (∏ m ∈ Finset.range j, (4 * I * (m + 1) * (I * k + I * m)))⁻¹ h2`. Rewrite `h3` using `[smul_smul, inv_mul_cancel₀ hc, one_smul]`. Take `⟨y, hy⟩` from `exists_isRefl_of_mem_reflSpan f hs hs0`. Use `⟨σc y s, σc_refl_reflSpan f hy hs, fun h => hs0 ?_, hW.2.1 y s h3⟩` and prove the remaining obligations.

Rewrite using `[← σc_inv_apply y s, h, map_zero]`.
-/
theorem exists_ne_zero_mem_translateSpanCusp (hk : 0 < k) {W : Submodule ℂ (cuspForms ℚ 2)}
    (hW : IsGKFStable W) (hWV : W ≤ weightSpan f) (hW0 : W ≠ ⊥) :
    ∃ t ∈ translateSpanCusp f, t ≠ 0 ∧ t ∈ W := by
  classical
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨F, hF, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp (weightPiece f) w).1 (hWV hwW)
  have hJW : ∀ v ∈ W, Jop v ∈ W := fun v hv => hW.cuspOp_mem rotMat hv
  have hcomp := mem_of_sum_mem_of_eigen hJW F.support F (weightEig k)
    (fun i _ => Jop_weightPiece f (hF i)) ((weightEig_injective hk).injOn)
    (by rw [← hsum] at hwW; exact hwW)
  obtain ⟨i, hi⟩ : F.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    apply hw0
    rw [← hsum, Finsupp.sum, he, Finset.sum_empty]
  have hFiW := hcomp i hi
  have hFi0 : F i ≠ 0 := Finsupp.mem_support_iff.1 hi
  rcases i with j | j
  · have hFj : F (Sum.inl j) ∈ (translateSpanCusp f).map (Rop ^ j) := hF (Sum.inl j)
    obtain ⟨t, ht, hte⟩ := hFj
    rw [← hte] at hFiW hFi0
    have h1 := L_pow_R_pow_apply Jop_Rop Lop_Rop (Jop_T f ht) (Lop_T f ht) j
    have hc := prod_ne_zero_of_pos hk j
    have ht0 : t ≠ 0 := fun h => hFi0 (by rw [h, map_zero])
    refine ⟨t, ht, ht0, ?_⟩
    have h2 := hW.cuspOp_pow_mem lowerMat j hFiW
    rw [h1] at h2
    have h3 := Submodule.smul_mem W (∏ m ∈ Finset.range j, (4 * I * (m + 1) * (I * k + I * m)))⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h3
  · have hFj : F (Sum.inr j) ∈ (reflSpan f).map (Lop ^ j) := hF (Sum.inr j)
    obtain ⟨s, hs, hse⟩ := hFj
    rw [← hse] at hFiW hFi0
    have h1 := L_pow_R_pow_apply negJop_Lop Rop_Lop (negJop_reflSpan f hs) (Rop_reflSpan f hs) j
    have hc := prod_ne_zero_of_pos hk j
    have hs0 : s ≠ 0 := fun h => hFi0 (by rw [h, map_zero])
    have h2 := hW.cuspOp_pow_mem raiseMat j hFiW
    rw [h1] at h2
    have h3 := Submodule.smul_mem W (∏ m ∈ Finset.range j, (4 * I * (m + 1) * (I * k + I * m)))⁻¹ h2
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at h3
    obtain ⟨y, hy⟩ := exists_isRefl_of_mem_reflSpan f hs hs0
    refine ⟨σc y s, σc_refl_reflSpan f hy hs, fun h => hs0 ?_, hW.2.1 y s h3⟩
    rw [← σc_inv_apply y s, h, map_zero]

end Extract

end GL2Classical

end

end GroundTheory.Automorphic
