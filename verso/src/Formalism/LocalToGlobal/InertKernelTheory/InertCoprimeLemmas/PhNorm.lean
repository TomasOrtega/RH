import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.EndInt
import Formalism.LocalToGlobal.InertKernelTheory.DefsBeW
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalC
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HasCMByStable
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.SecondCoeffConsistency
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OneLetterGaussSharpTranslateHolds

open PowerSeries

noncomputable section

namespace Formalism.L2.KerInert.PN

open Formalism.L2.KerInert.VC

section Field

variable {K : Type} [Field K] [CharZero K] (W : WeierstrassCurve K) (C : WeierstrassCurve.VariableChange K)

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Formalism.L2.Th1.A.g₂, WeierstrassCurve.variableChange_c₄]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Formalism.L2.Th1.A.g₃, WeierstrassCurve.variableChange_c₆]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem g_change' : Formalism.L2.Th1.A.g₂ (C • W) = ((C.u⁻¹ : Kˣ) : K) ^ 4 * Formalism.L2.Th1.A.g₂ W ∧
    Formalism.L2.Th1.A.g₃ (C • W) = ((C.u⁻¹ : Kˣ) : K) ^ 6 * Formalism.L2.Th1.A.g₃ W := by
  refine ⟨?_, ?_⟩
  · simp only [Formalism.L2.Th1.A.g₂, WeierstrassCurve.variableChange_c₄]
    ring
  · simp only [Formalism.L2.Th1.A.g₃, WeierstrassCurve.variableChange_c₆]
    ring

/- English proof (translation)
Rewrite using `[Formalism.L2.KerInert.Sigma.wpReg_eq, Formalism.L2.KerInert.Sigma.wpReg_eq, (g_change' W C).1, (g_change' W C).2]`. Conclude with `(Formalism.L2.Th1.F.seriesScale K _ _ _).2.2.2.1`.
-/
theorem wpReg_change : Formalism.L2.Th1.A.wpReg (C • W) =
    PowerSeries.C (((C.u⁻¹ : Kˣ) : K) ^ 2) * PowerSeries.rescale ((C.u⁻¹ : Kˣ) : K) (Formalism.L2.Th1.A.wpReg W) := by
  rw [Formalism.L2.KerInert.Sigma.wpReg_eq, Formalism.L2.KerInert.Sigma.wpReg_eq, (g_change' W C).1, (g_change' W C).2]
  exact (Formalism.L2.Th1.F.seriesScale K _ _ _).2.2.2.1

/- English proof (translation)
Use extensionality with `n`. Break down `n with _ | m` into its components or cases. Simplify using `[Formalism.L2.Th1.B.prim]`. Simplify using `only [Formalism.L2.Th1.B.prim, PowerSeries.coeff_rescale, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]`. Rewrite using `[pow_succ]`.

Clear the denominators using the available nonvanishing facts.
-/
private lemma prim_rescale (a : K) (ha : a ≠ 0) (f : K⟦X⟧) :
    Formalism.L2.Th1.B.prim (PowerSeries.rescale a f) =
      PowerSeries.C a⁻¹ * PowerSeries.rescale a (Formalism.L2.Th1.B.prim f) := by
  ext n
  rcases n with _ | m
  · simp [Formalism.L2.Th1.B.prim]
  · simp only [Formalism.L2.Th1.B.prim, PowerSeries.coeff_rescale, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_mk, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    rw [pow_succ]
    field_simp

/- English proof (translation)
Use extensionality with `n`. Break down `n with _ | m` into its components or cases. Simplify using `[Formalism.L2.Th1.B.prim]`. Simplify using `only [Formalism.L2.Th1.B.prim, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, Nat.succ_ne_zero, if_false]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma prim_C_mul' (c : K) (f : K⟦X⟧) :
    Formalism.L2.Th1.B.prim (PowerSeries.C c * f) = PowerSeries.C c * Formalism.L2.Th1.B.prim f := by
  ext n
  rcases n with _ | m
  · simp [Formalism.L2.Th1.B.prim]
  · simp only [Formalism.L2.Th1.B.prim, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, Nat.succ_ne_zero,
      if_false]
    ring

/- English proof (translation)
Unfold `Formalism.L2.Th1.B.fExp`. Establish `hf'` using `PowerSeries.HasSubst.of_constantCoeff_zero' hf`. Establish `hX : PowerSeries.HasSubst ((a • PowerSeries.X : K⟦X⟧))` using `PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)`. Rewrite using `[PowerSeries.rescale_eq_subst a (PowerSeries.subst f (PowerSeries.exp K)), PowerSeries.subst_comp_subst_apply hf' hX, ← PowerSeries.rescale_eq_subst]`.
-/
private lemma fExp_rescale (a : K) (f : K⟦X⟧) (hf : PowerSeries.constantCoeff f = 0) :
    Formalism.L2.Th1.B.fExp (PowerSeries.rescale a f) = PowerSeries.rescale a (Formalism.L2.Th1.B.fExp f) := by
  unfold Formalism.L2.Th1.B.fExp
  have hf' := PowerSeries.HasSubst.of_constantCoeff_zero' hf
  have hX : PowerSeries.HasSubst ((a • PowerSeries.X : K⟦X⟧)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  rw [PowerSeries.rescale_eq_subst a (PowerSeries.subst f (PowerSeries.exp K)),
    PowerSeries.subst_comp_subst_apply hf' hX, ← PowerSeries.rescale_eq_subst]

/- English proof (translation)
Establish `hl : ((C.u⁻¹ : Kˣ) : K) ≠ 0` using `Units.ne_zero _`. Establish `hul : ((C.u : Kˣ) : K) * ((C.u⁻¹ : Kˣ) : K) = 1`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `hRC : ∀ c : K, PowerSeries.rescale ((C.u⁻¹ : Kˣ) : K) (PowerSeries.C c) = PowerSeries.C c`. Introduce `c`.

Use extensionality with `n`. Rewrite using `[PowerSeries.coeff_rescale, PowerSeries.coeff_C]`. Apply the tactic sequence `split_ifs with h <;> simp [h]`. Unfold `Formalism.L2.Th1.B.sgW Formalism.L2.Th1.B.sgStar Formalism.L2.Th1.B.sigma Formalism.L2.Th1.B.sigS`. Rewrite using `[wpReg_change W C]`.

Establish `hpp : Formalism.L2.Th1.B.prim (Formalism.L2.Th1.B.prim (PowerSeries.C (((C.u⁻¹ : Kˣ) : K) ^ 2) * PowerSeries.rescale ((C.u⁻¹ : Kˣ) : K) (Formalism.L2.Th1.A.wpReg W))) = PowerSeries.rescale ((C.u⁻¹ : Kˣ) : K) (Formalism.L2.Th1.B.prim (Formalism.L2.Th1.B.prim (Formalism.L2.Th1.A.wp …`. Rewrite using `[prim_C_mul', prim_rescale _ hl, ← mul_assoc, ← map_mul, prim_C_mul', prim_rescale _ hl, ← mul_assoc, ← map_mul]`. Establish `h1 : ((C.u⁻¹ : Kˣ) : K) ^ 2 * ((C.u⁻¹ : Kˣ) : K)⁻¹ * ((C.u⁻¹ : Kˣ) : K)⁻¹ = 1`. Clear the denominators using the available nonvanishing facts. Rewrite using `[h1, map_one, one_mul]`.

Establish `hT : -(PowerSeries.C (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2 / 2) * PowerSeries.X ^ 2 : K⟦X⟧) = PowerSeries.rescale ((C.u⁻¹ : Kˣ) : K) (-(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2))`. Rewrite using `[map_neg, map_mul, map_pow, PowerSeries.rescale_X, hRC, mul_pow, ← map_pow, ← mul_assoc, ← map_mul, show ((C.u⁻¹ : Kˣ) : K) ^ 2 * s2 / 2 = s2 / 2 * ((C.u⁻¹ : Kˣ) : K) ^ 2 by ring]`. Establish `hS0 : PowerSeries.constantCoeff (-Formalism.L2.Th1.B.prim (Formalism.L2.Th1.B.prim (Formalism.L2.Th1.A.wpReg W))) = 0`. Rewrite using `[map_neg, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Simplify using `[Formalism.L2.Th1.B.prim]`.

Establish `hT0 : PowerSeries.constantCoeff (-(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2 : K⟦X⟧)) = 0`. Simplify using the standard rewrite rules. Rewrite using `[hpp, hT, ← map_neg, fExp_rescale _ _ hS0, fExp_rescale _ _ hT0, map_mul, map_mul, PowerSeries.rescale_X]`. Simplify using `only [← mul_assoc, ← map_mul, hul, map_one, one_mul]`.
-/
theorem sgW_change (s2 : K) : Formalism.L2.Th1.B.sgW (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2) =
    PowerSeries.C ((C.u : Kˣ) : K) * PowerSeries.rescale ((C.u⁻¹ : Kˣ) : K) (Formalism.L2.Th1.B.sgW W s2) := by
  have hl : ((C.u⁻¹ : Kˣ) : K) ≠ 0 := Units.ne_zero _
  have hul : ((C.u : Kˣ) : K) * ((C.u⁻¹ : Kˣ) : K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hRC : ∀ c : K, PowerSeries.rescale ((C.u⁻¹ : Kˣ) : K) (PowerSeries.C c) = PowerSeries.C c := by
    intro c
    ext n
    rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
    split_ifs with h <;> simp [h]
  unfold Formalism.L2.Th1.B.sgW Formalism.L2.Th1.B.sgStar Formalism.L2.Th1.B.sigma Formalism.L2.Th1.B.sigS
  rw [wpReg_change W C]
  have hpp : Formalism.L2.Th1.B.prim (Formalism.L2.Th1.B.prim (PowerSeries.C (((C.u⁻¹ : Kˣ) : K) ^ 2) *
      PowerSeries.rescale ((C.u⁻¹ : Kˣ) : K) (Formalism.L2.Th1.A.wpReg W))) =
      PowerSeries.rescale ((C.u⁻¹ : Kˣ) : K)
        (Formalism.L2.Th1.B.prim (Formalism.L2.Th1.B.prim (Formalism.L2.Th1.A.wpReg W))) := by
    rw [prim_C_mul', prim_rescale _ hl, ← mul_assoc, ← map_mul, prim_C_mul',
      prim_rescale _ hl, ← mul_assoc, ← map_mul]
    have h1 : ((C.u⁻¹ : Kˣ) : K) ^ 2 * ((C.u⁻¹ : Kˣ) : K)⁻¹ * ((C.u⁻¹ : Kˣ) : K)⁻¹ = 1 := by
      field_simp
    rw [h1, map_one, one_mul]
  have hT : -(PowerSeries.C (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2 / 2) * PowerSeries.X ^ 2 : K⟦X⟧) =
      PowerSeries.rescale ((C.u⁻¹ : Kˣ) : K) (-(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2)) := by
    rw [map_neg, map_mul, map_pow, PowerSeries.rescale_X, hRC, mul_pow, ← map_pow, ← mul_assoc,
      ← map_mul, show ((C.u⁻¹ : Kˣ) : K) ^ 2 * s2 / 2 = s2 / 2 * ((C.u⁻¹ : Kˣ) : K) ^ 2 by ring]
  have hS0 : PowerSeries.constantCoeff (-Formalism.L2.Th1.B.prim (Formalism.L2.Th1.B.prim (Formalism.L2.Th1.A.wpReg W))) = 0 := by
    rw [map_neg, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [Formalism.L2.Th1.B.prim]
  have hT0 : PowerSeries.constantCoeff (-(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2 : K⟦X⟧)) = 0 := by
    simp
  rw [hpp, hT, ← map_neg, fExp_rescale _ _ hS0, fExp_rescale _ _ hT0, map_mul, map_mul,
    PowerSeries.rescale_X]
  simp only [← mul_assoc, ← map_mul, hul, map_one, one_mul]

/- English proof (translation)
Establish `hg'` using `PowerSeries.HasSubst.of_constantCoeff_zero' hg`. Establish `hX : PowerSeries.HasSubst ((a • PowerSeries.X : K⟦X⟧))` using `PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)`. Rewrite using `[PowerSeries.rescale_eq_subst, PowerSeries.subst_comp_subst_apply hX hg']`. Use `congr 1`. Rewrite using `[← PowerSeries.coe_substAlgHom hg', map_smul, PowerSeries.coe_substAlgHom, PowerSeries.subst_X hg', PowerSeries.smul_eq_C_mul]`.
-/
theorem subst_rescale' (a : K) (f : PowerSeries K) {g : PowerSeries K} (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.subst g (PowerSeries.rescale a f) = PowerSeries.subst (PowerSeries.C a * g) f := by
  have hg' := PowerSeries.HasSubst.of_constantCoeff_zero' hg
  have hX : PowerSeries.HasSubst ((a • PowerSeries.X : K⟦X⟧)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  rw [PowerSeries.rescale_eq_subst, PowerSeries.subst_comp_subst_apply hX hg']
  congr 1
  rw [← PowerSeries.coe_substAlgHom hg', map_smul, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X hg', PowerSeries.smul_eq_C_mul]

/- English proof (translation)
Establish `h` using `HasSubst.of_constantCoeff_zero' ha`. Rewrite using `[← PowerSeries.coe_substAlgHom h, map_neg]`.
-/
theorem subst_neg' {f a : K⟦X⟧} (ha : constantCoeff a = 0) : (-f).subst a = -(f.subst a) := by
  have h := HasSubst.of_constantCoeff_zero' ha
  rw [← PowerSeries.coe_substAlgHom h, map_neg]

/- English proof (translation)
Establish `h` using `HasSubst.of_constantCoeff_zero' ha`. Rewrite using `[← PowerSeries.coe_substAlgHom h, map_sub]`.
-/
theorem subst_sub' {f g a : K⟦X⟧} (ha : constantCoeff a = 0) : (f - g).subst a = f.subst a - g.subst a := by
  have h := HasSubst.of_constantCoeff_zero' ha
  rw [← PowerSeries.coe_substAlgHom h, map_sub]

/- English proof (translation)
Establish `h` using `HasSubst.of_constantCoeff_zero' ha`. Rewrite using `[← PowerSeries.coe_substAlgHom h, map_smul]`.
-/
theorem subst_smul' {f a : K⟦X⟧} (ha : constantCoeff a = 0) (c : K) : (c • f).subst a = c • (f.subst a) := by
  have h := HasSubst.of_constantCoeff_zero' ha
  rw [← PowerSeries.coe_substAlgHom h, map_smul]

/- English proof (translation)
The claim follows from `(Formalism.L2.Th1.B.expLogSubst K Unit Unit (fun _ => a) (fun _ => ha)).1 f hf`.
-/
private lemma subst_fExp' {a f : K⟦X⟧} (ha : PowerSeries.constantCoeff a = 0)
    (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.subst a (Formalism.L2.Th1.B.fExp f) = Formalism.L2.Th1.B.fExp (PowerSeries.subst a f) :=
  (Formalism.L2.Th1.B.expLogSubst K Unit Unit (fun _ => a) (fun _ => ha)).1 f hf

/- English proof (translation)
Establish `hφ0 : PowerSeries.constantCoeff (phi W C) = 0`. Rewrite using `[Formalism.L2.KerInert.VC.phi_eq]`. Simplify using the standard rewrite rules. Establish `hφ` using `PowerSeries.HasSubst.of_constantCoeff_zero' hφ0`. Establish `hℓ0 : PowerSeries.constantCoeff (Formalism.L2.Th1.A.logSer W) = 0` using `Formalism.L2.Th1.A.ZSer.log_cc (W := W)`.

Establish `hℓ0' : PowerSeries.constantCoeff (Formalism.L2.Th1.A.logSer (C • W)) = 0` using `Formalism.L2.Th1.A.ZSer.log_cc (W := C • W)`. Establish `hℓ'` using `PowerSeries.HasSubst.of_constantCoeff_zero' hℓ0'`. Establish `hcs` using `Formalism.L2.Th1.B.curveSigma K W s2`. Establish `hcs'` using `Formalism.L2.Th1.B.curveSigma K (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2)`. Establish `hnP0 : PowerSeries.constantCoeff (-Formalism.L2.Th1.B.phW (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2)) = 0`.

Rewrite using `[map_neg, hcs'.1, neg_zero]`. Establish `hul : ((C.u⁻¹ : Kˣ) : K) * ((C.u : Kˣ) : K) = 1`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`. Establish `hcu0 : PowerSeries.constantCoeff (PowerSeries.C ((C.u : Kˣ) : K) * Formalism.L2.Th1.A.logSer W) = 0`. Simplify using `[hℓ0]`.

Establish `step1 : phi W C * Formalism.L2.Th1.B.fExp (-((Formalism.L2.Th1.B.phW (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2)).subst (phi W C))) = PowerSeries.subst (phi W C) (X * Formalism.L2.Th1.B.fExp (-Formalism.L2.Th1.B.phW (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2)))`. Rewrite using `[← PowerSeries.coe_substAlgHom hφ, map_mul, PowerSeries.coe_substAlgHom hφ, PowerSeries.subst_X hφ, subst_fExp' hφ0 hnP0, subst_neg' hφ0]`. Establish `hsm : PowerSeries.C ((C.u : Kˣ) : K) * PowerSeries.rescale ((C.u⁻¹ : Kˣ) : K) (Formalism.L2.Th1.B.sgW W s2) = ((C.u : Kˣ) : K) • PowerSeries.rescale ((C.u⁻¹ : Kˣ) : K) (Formalism.L2.Th1.B.sgW W s2)` using `(PowerSeries.smul_eq_C_mul _ _).symm`. Rewrite using `[step1, ← hcs'.2.1, PowerSeries.subst_comp_subst_apply hℓ' hφ, Formalism.L2.KerInert.VC.log_phi, sgW_change, hsm, subst_smul' hcu0, subst_rescale' _ _ hcu0, ← mul_assoc (PowerSeries.C _) (PowerSeries.C _) (Formalism.L2.Th1.A.logSer W), ← map_mul PowerSeries.C, hul, map_one, one_m …`. Conclude with `PowerSeries.smul_eq_C_mul _ _`.
-/
theorem exp_rel (s2 : K) :
    phi W C * Formalism.L2.Th1.B.fExp (-((Formalism.L2.Th1.B.phW (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2)).subst (phi W C))) =
      PowerSeries.C ((C.u : Kˣ) : K) * (X * Formalism.L2.Th1.B.fExp (-(Formalism.L2.Th1.B.phW W s2))) := by
  have hφ0 : PowerSeries.constantCoeff (phi W C) = 0 := by
    rw [Formalism.L2.KerInert.VC.phi_eq]; simp
  have hφ := PowerSeries.HasSubst.of_constantCoeff_zero' hφ0
  have hℓ0 : PowerSeries.constantCoeff (Formalism.L2.Th1.A.logSer W) = 0 := Formalism.L2.Th1.A.ZSer.log_cc (W := W)
  have hℓ0' : PowerSeries.constantCoeff (Formalism.L2.Th1.A.logSer (C • W)) = 0 :=
    Formalism.L2.Th1.A.ZSer.log_cc (W := C • W)
  have hℓ' := PowerSeries.HasSubst.of_constantCoeff_zero' hℓ0'
  have hcs := Formalism.L2.Th1.B.curveSigma K W s2
  have hcs' := Formalism.L2.Th1.B.curveSigma K (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2)
  have hnP0 : PowerSeries.constantCoeff
      (-Formalism.L2.Th1.B.phW (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2)) = 0 := by
    rw [map_neg, hcs'.1, neg_zero]
  have hul : ((C.u⁻¹ : Kˣ) : K) * ((C.u : Kˣ) : K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcu0 : PowerSeries.constantCoeff (PowerSeries.C ((C.u : Kˣ) : K) * Formalism.L2.Th1.A.logSer W) = 0 := by
    simp [hℓ0]
  have step1 : phi W C * Formalism.L2.Th1.B.fExp
      (-((Formalism.L2.Th1.B.phW (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2)).subst (phi W C))) =
      PowerSeries.subst (phi W C)
        (X * Formalism.L2.Th1.B.fExp (-Formalism.L2.Th1.B.phW (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2))) := by
    rw [← PowerSeries.coe_substAlgHom hφ, map_mul, PowerSeries.coe_substAlgHom hφ,
      PowerSeries.subst_X hφ, subst_fExp' hφ0 hnP0, subst_neg' hφ0]
  have hsm : PowerSeries.C ((C.u : Kˣ) : K) *
      PowerSeries.rescale ((C.u⁻¹ : Kˣ) : K) (Formalism.L2.Th1.B.sgW W s2) =
      ((C.u : Kˣ) : K) • PowerSeries.rescale ((C.u⁻¹ : Kˣ) : K) (Formalism.L2.Th1.B.sgW W s2) :=
    (PowerSeries.smul_eq_C_mul _ _).symm
  rw [step1, ← hcs'.2.1, PowerSeries.subst_comp_subst_apply hℓ' hφ, Formalism.L2.KerInert.VC.log_phi,
    sgW_change, hsm, subst_smul' hcu0, subst_rescale' _ _ hcu0,
    ← mul_assoc (PowerSeries.C _) (PowerSeries.C _) (Formalism.L2.Th1.A.logSer W), ← map_mul PowerSeries.C,
    hul, map_one, one_mul, hcs.2.1]
  exact PowerSeries.smul_eq_C_mul _ _

end Field

section Cong

open Formalism.L2.Th1.C Formalism.L2.Th1.C.Pts

variable {K : Type} [Field K] [CharZero K] {R' : Subring K}

/- English proof (translation)
Take `⟨h0, hadd, hneg⟩` from `Formalism.L2.Th1.C.lGSubgroup K R' Unit`. Establish `key : ∀ n : ℕ, LG R' ((((n : ℤ) : K) • f : K⟦X⟧) : MvPowerSeries Unit K)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simpa using h0`.

Consider the case `succ n ih`. Establish `h1` using `hadd _ _ ih hf`. Establish `e : ((((n + 1 : ℕ) : ℤ) : K) • f : K⟦X⟧) = (((n : ℤ) : K) • f : K⟦X⟧) + f`. Use `push_cast`. Rewrite using `[add_smul, one_smul]`.

Rewrite using `[e]`. Conclude with `h1`. Break down `Int.eq_nat_or_neg N with ⟨n, rfl | rfl⟩` into its components or cases. Conclude with `key n`. Establish `h1` using `hneg _ (key n)`.

Establish `e : (((-(n : ℤ) : ℤ) : K) • f : K⟦X⟧) = -((((n : ℤ) : K) • f : K⟦X⟧))`. Use `push_cast`. Rewrite using `[neg_smul]`. Rewrite using `[e]`. Conclude with `h1`.
-/
theorem lg_intsmul (N : ℤ) {f : K⟦X⟧} (hf : LG R' (f : MvPowerSeries Unit K)) :
    LG R' (((N : K) • f : K⟦X⟧) : MvPowerSeries Unit K) := by
  obtain ⟨h0, hadd, hneg⟩ := Formalism.L2.Th1.C.lGSubgroup K R' Unit
  have key : ∀ n : ℕ, LG R' ((((n : ℤ) : K) • f : K⟦X⟧) : MvPowerSeries Unit K) := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      have h1 := hadd _ _ ih hf
      have e : ((((n + 1 : ℕ) : ℤ) : K) • f : K⟦X⟧) = (((n : ℤ) : K) • f : K⟦X⟧) + f := by
        push_cast
        rw [add_smul, one_smul]
      rw [e]
      exact h1
  rcases Int.eq_nat_or_neg N with ⟨n, rfl | rfl⟩
  · exact key n
  · have h1 := hneg _ (key n)
    have e : (((-(n : ℤ) : ℤ) : K) • f : K⟦X⟧) = -((((n : ℤ) : K) • f : K⟦X⟧)) := by
      push_cast
      rw [neg_smul]
    rw [e]
    exact h1

/- English proof (translation)
Establish `h` using `Formalism.L2.KerInert.VC.intPS_phi W hW C hu hr hs ht`. Rewrite `h` using `[Formalism.L2.KerInert.VC.phi_eq]`. Introduce `n`. Establish `h1` using `h (n + 1)`. Rewrite `h1` using `[PowerSeries.coeff_succ_X_mul]`. Then use the resulting hypothesis.
-/
theorem integral_phi1_variable_change (W : WeierstrassCurve K) (hW : CoeffIn R' W) (C : WeierstrassCurve.VariableChange K)
    (hu : ((C.u : Kˣ) : K) ∈ R') (hr : C.r ∈ R') (hs : C.s ∈ R') (ht : C.t ∈ R') :
    IntPS R' (PowerSeries.C ((C.u : Kˣ) : K) * (1 - PowerSeries.C C.r * X ^ 2 * Formalism.L2.Th1.A.wU W) * vv W C) := by
  have h := Formalism.L2.KerInert.VC.intPS_phi W hW C hu hr hs ht
  rw [Formalism.L2.KerInert.VC.phi_eq] at h
  intro n
  have h1 := h (n + 1)
  rwa [PowerSeries.coeff_succ_X_mul] at h1

/- English proof (translation)
Establish `hφ0 : PowerSeries.constantCoeff (phi W C) = 0`. Rewrite using `[Formalism.L2.KerInert.VC.phi_eq]`. Simplify using the standard rewrite rules. Establish `hφ` using `PowerSeries.HasSubst.of_constantCoeff_zero' hφ0`. Establish `hcs` using `Formalism.L2.Th1.B.curveSigma K W s2`.

Establish `hcs'` using `Formalism.L2.Th1.B.curveSigma K (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2)`. Establish `key` using `exp_rel W C s2`. Take `⟨A, hA⟩ : ∃ A : K⟦X⟧, A = PowerSeries.subst (phi W C) (Formalism.L2.Th1.B.phW (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2))` from `⟨_, rfl⟩`. Take `⟨B, hB⟩ : ∃ B : K⟦X⟧, B = Formalism.L2.Th1.B.phW W s2` from `⟨_, rfl⟩`. Rewrite using `[← hA, ← hB]`.

Rewrite `key` using `[← hA, ← hB]`. Take `⟨Q, hQ⟩` from `PowerSeries.X_dvd_iff.mpr hcs'.1`. Establish `hA0 : PowerSeries.constantCoeff A = 0`. Rewrite using `[hA, hQ, ← PowerSeries.coe_substAlgHom hφ, map_mul, PowerSeries.coe_substAlgHom hφ, PowerSeries.subst_X hφ, map_mul, hφ0, zero_mul]`. Establish `hB0 : PowerSeries.constantCoeff B = 0` using `by rw [hB]; exact hcs.1`.

Establish `hnA0 : PowerSeries.constantCoeff (-A) = 0` using `by rw [map_neg, hA0, neg_zero]`. Establish `hnB0 : PowerSeries.constantCoeff (-B) = 0` using `by rw [map_neg, hB0, neg_zero]`. Establish `hER` using `Formalism.L2.Th1.B.expLogRules K Unit`. Establish `hfe0 : Formalism.L2.Th1.B.fExp (0 : K⟦X⟧) = 1`. Establish `h1` using `hER.1 (0 : K⟦X⟧) 0 (map_zero _) (map_zero _)`.

Rewrite `h1` using `[add_zero]`. Establish `hu0 : IsUnit (Formalism.L2.Th1.B.fExp (0 : K⟦X⟧))`. Rewrite using `[MvPowerSeries.isUnit_iff_constantCoeff, (hER.2.1 0 (map_zero _)).1]`. Conclude with `isUnit_one`. Conclude with `hu0.mul_left_cancel (by rw [mul_one]; exact h1.symm)`.

Establish `hAA : Formalism.L2.Th1.B.fExp A * Formalism.L2.Th1.B.fExp (-A) = 1`. Rewrite using `[← hER.1 A (-A) hA0 hnA0, add_neg_cancel, hfe0]`. Establish `hAB : Formalism.L2.Th1.B.fExp (A - B) = Formalism.L2.Th1.B.fExp A * Formalism.L2.Th1.B.fExp (-B)`. Rewrite using `[sub_eq_add_neg, hER.1 A (-B) hA0 hnB0]`. Take `⟨V, hV⟩ : ∃ V : K⟦X⟧, V = PowerSeries.C ((C.u : Kˣ) : K) * (1 - PowerSeries.C C.r * X ^ 2 * Formalism.L2.Th1.A.wU W) * vv W C` from `⟨_, rfl⟩`.

Establish `hφV : phi W C = X * V` using `by rw [Formalism.L2.KerInert.VC.phi_eq, hV]`. Rewrite `key` using `[hφV]`. Establish `key2 : V * Formalism.L2.Th1.B.fExp (-A) = PowerSeries.C ((C.u : Kˣ) : K) * Formalism.L2.Th1.B.fExp (-B)`. Apply `mul_left_cancel₀ (PowerSeries.X_ne_zero (R := K))` to reduce the goal to its premises. Rewrite using `[← mul_assoc, key]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hul : ((C.u⁻¹ : Kˣ) : K) * ((C.u : Kˣ) : K) = 1`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`. Establish `hE : Formalism.L2.Th1.B.fExp (A - B) = PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * V`. Rewrite using `[hAB]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, ← map_mul, hul, map_one, one_mul, mul_comm]`. Use `_ = PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * (V * Formalism.L2.Th1.B.fExp (-A)) * Formalism.L2.Th1.B.fExp A := by`. Rewrite using `[key2]`. Use `_ = PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * V * (Formalism.L2.Th1.B.fExp A * Formalism.L2.Th1.B.fExp (-A)) := by`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * V := by rw [hAA, mul_one]`. Establish `hVi : Formalism.L2.Th1.C.IntPS R' V` using `by rw [hV]; exact integral_phi1_variable_change W hW C hu hr hs ht`. Use `show Formalism.L2.Th1.C.LG R' ((A : MvPowerSeries Unit K) - B)`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Use `show PowerSeries.constantCoeff (A - B) = 0`. Rewrite using `[map_sub, hA0, hB0, sub_zero]`. Use `show Formalism.L2.Th1.C.IntMv R' (Formalism.L2.Th1.B.fExp (A - B))`. Rewrite using `[hE]`. Introduce `n`.

Rewrite using `[Finsupp.unique_single n]`. Use `show PowerSeries.coeff (n default) (PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * V) ∈ R'`. Rewrite using `[PowerSeries.coeff_C_mul]`. Conclude with `R'.mul_mem hu' (hVi (n default))`.
-/
theorem cong_phi (W : WeierstrassCurve K) (hW : CoeffIn R' W) (C : WeierstrassCurve.VariableChange K)
    (hu : ((C.u : Kˣ) : K) ∈ R') (hu' : ((C.u⁻¹ : Kˣ) : K) ∈ R') (hr : C.r ∈ R') (hs : C.s ∈ R') (ht : C.t ∈ R')
    (s2 : K) :
    Cong R' ((PowerSeries.subst (phi W C) (Formalism.L2.Th1.B.phW (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2)) : K⟦X⟧) :
      MvPowerSeries Unit K) ((Formalism.L2.Th1.B.phW W s2 : K⟦X⟧) : MvPowerSeries Unit K) := by
  have hφ0 : PowerSeries.constantCoeff (phi W C) = 0 := by
    rw [Formalism.L2.KerInert.VC.phi_eq]; simp
  have hφ := PowerSeries.HasSubst.of_constantCoeff_zero' hφ0
  have hcs := Formalism.L2.Th1.B.curveSigma K W s2
  have hcs' := Formalism.L2.Th1.B.curveSigma K (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2)
  have key := exp_rel W C s2
  obtain ⟨A, hA⟩ : ∃ A : K⟦X⟧, A = PowerSeries.subst (phi W C)
      (Formalism.L2.Th1.B.phW (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2)) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : K⟦X⟧, B = Formalism.L2.Th1.B.phW W s2 := ⟨_, rfl⟩
  rw [← hA, ← hB]
  rw [← hA, ← hB] at key
  obtain ⟨Q, hQ⟩ := PowerSeries.X_dvd_iff.mpr hcs'.1
  have hA0 : PowerSeries.constantCoeff A = 0 := by
    rw [hA, hQ, ← PowerSeries.coe_substAlgHom hφ, map_mul, PowerSeries.coe_substAlgHom hφ,
      PowerSeries.subst_X hφ, map_mul, hφ0, zero_mul]
  have hB0 : PowerSeries.constantCoeff B = 0 := by rw [hB]; exact hcs.1
  have hnA0 : PowerSeries.constantCoeff (-A) = 0 := by rw [map_neg, hA0, neg_zero]
  have hnB0 : PowerSeries.constantCoeff (-B) = 0 := by rw [map_neg, hB0, neg_zero]
  have hER := Formalism.L2.Th1.B.expLogRules K Unit
  have hfe0 : Formalism.L2.Th1.B.fExp (0 : K⟦X⟧) = 1 := by
    have h1 := hER.1 (0 : K⟦X⟧) 0 (map_zero _) (map_zero _)
    rw [add_zero] at h1
    have hu0 : IsUnit (Formalism.L2.Th1.B.fExp (0 : K⟦X⟧)) := by
      rw [MvPowerSeries.isUnit_iff_constantCoeff, (hER.2.1 0 (map_zero _)).1]
      exact isUnit_one
    exact hu0.mul_left_cancel (by rw [mul_one]; exact h1.symm)
  have hAA : Formalism.L2.Th1.B.fExp A * Formalism.L2.Th1.B.fExp (-A) = 1 := by
    rw [← hER.1 A (-A) hA0 hnA0, add_neg_cancel, hfe0]
  have hAB : Formalism.L2.Th1.B.fExp (A - B) = Formalism.L2.Th1.B.fExp A * Formalism.L2.Th1.B.fExp (-B) := by
    rw [sub_eq_add_neg, hER.1 A (-B) hA0 hnB0]
  obtain ⟨V, hV⟩ : ∃ V : K⟦X⟧, V = PowerSeries.C ((C.u : Kˣ) : K) *
      (1 - PowerSeries.C C.r * X ^ 2 * Formalism.L2.Th1.A.wU W) * vv W C := ⟨_, rfl⟩
  have hφV : phi W C = X * V := by rw [Formalism.L2.KerInert.VC.phi_eq, hV]
  rw [hφV] at key
  have key2 : V * Formalism.L2.Th1.B.fExp (-A) = PowerSeries.C ((C.u : Kˣ) : K) * Formalism.L2.Th1.B.fExp (-B) := by
    apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R := K))
    rw [← mul_assoc, key]
    ring
  have hul : ((C.u⁻¹ : Kˣ) : K) * ((C.u : Kˣ) : K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hE : Formalism.L2.Th1.B.fExp (A - B) = PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * V := by
    rw [hAB]
    calc Formalism.L2.Th1.B.fExp A * Formalism.L2.Th1.B.fExp (-B)
        = PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * (PowerSeries.C ((C.u : Kˣ) : K) * Formalism.L2.Th1.B.fExp (-B)) *
          Formalism.L2.Th1.B.fExp A := by
          rw [← mul_assoc, ← map_mul, hul, map_one, one_mul, mul_comm]
      _ = PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * (V * Formalism.L2.Th1.B.fExp (-A)) * Formalism.L2.Th1.B.fExp A := by
          rw [key2]
      _ = PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * V * (Formalism.L2.Th1.B.fExp A * Formalism.L2.Th1.B.fExp (-A)) := by
          ring
      _ = PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * V := by rw [hAA, mul_one]
  have hVi : Formalism.L2.Th1.C.IntPS R' V := by rw [hV]; exact integral_phi1_variable_change W hW C hu hr hs ht
  show Formalism.L2.Th1.C.LG R' ((A : MvPowerSeries Unit K) - B)
  refine ⟨?_, ?_⟩
  · show PowerSeries.constantCoeff (A - B) = 0
    rw [map_sub, hA0, hB0, sub_zero]
  · show Formalism.L2.Th1.C.IntMv R' (Formalism.L2.Th1.B.fExp (A - B))
    rw [hE]
    intro n
    rw [Finsupp.unique_single n]
    show PowerSeries.coeff (n default) (PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * V) ∈ R'
    rw [PowerSeries.coeff_C_mul]
    exact R'.mul_mem hu' (hVi (n default))

end Cong

section Transfer

open Formalism.L2.Th1.C Formalism.L2.Th1.C.Pts Formalism.L2.Th1.C.Calc

variable {K : Type} [Field K] [CharZero K] {R' : Subring K}

/- English proof (translation)
Rewrite using `[← one_smul K (X : K⟦X⟧), ← PowerSeries.rescale_eq_subst, PowerSeries.rescale_one, RingHom.id_apply]`.
-/
private lemma powerSeries_subst_X (f : K⟦X⟧) : PowerSeries.subst (X : K⟦X⟧) f = f := by
  rw [← one_smul K (X : K⟦X⟧), ← PowerSeries.rescale_eq_subst, PowerSeries.rescale_one, RingHom.id_apply]

/- English proof (translation)
Introduce `n`. Rewrite using `[Finsupp.unique_single n]`. Conclude with `h (n default)`.
-/
private lemma intMv_coe_of_intPS {f : K⟦X⟧} (h : IntPS R' f) : IntMv R' (f : MvPowerSeries Unit K) := by
  intro n
  rw [Finsupp.unique_single n]
  exact h (n default)

/- English proof (translation)
Unfold `Formalism.L2.Th1.A.compInv`. Use `split_ifs with h`. Conclude with `h.choose_spec.1`. Simplify using the standard rewrite rules.
-/
private lemma constantCoeff_compInv (f : K⟦X⟧) : PowerSeries.constantCoeff (Formalism.L2.Th1.A.compInv f) = 0 := by
  unfold Formalism.L2.Th1.A.compInv
  split_ifs with h
  · exact h.choose_spec.1
  · simp

/- English proof (translation)
Take `⟨Q, hQ⟩` from `PowerSeries.X_dvd_iff.mpr hf`. Establish `hs` using `PowerSeries.HasSubst.of_constantCoeff_zero' ha`. Rewrite using `[hQ, ← PowerSeries.coe_substAlgHom hs, map_mul, PowerSeries.coe_substAlgHom hs, PowerSeries.subst_X hs, map_mul, ha, zero_mul]`.
-/
private lemma constantCoeff_subst_eq_zero_inert_coprime {a f : K⟦X⟧} (ha : PowerSeries.constantCoeff a = 0)
    (hf : PowerSeries.constantCoeff f = 0) : PowerSeries.constantCoeff (PowerSeries.subst a f) = 0 := by
  obtain ⟨Q, hQ⟩ := PowerSeries.X_dvd_iff.mpr hf
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' ha
  rw [hQ, ← PowerSeries.coe_substAlgHom hs, map_mul, PowerSeries.coe_substAlgHom hs, PowerSeries.subst_X hs,
    map_mul, ha, zero_mul]

/- English proof (translation)
Establish `hφ0 : PowerSeries.constantCoeff (phi W C) = 0`. Rewrite using `[Formalism.L2.KerInert.VC.phi_eq]`. Simplify using the standard rewrite rules. Establish `hφ` using `PowerSeries.HasSubst.of_constantCoeff_zero' hφ0`. Establish `h1 : PowerSeries.coeff 1 (phi W C) = ((C.u : Kˣ) : K)`.

Rewrite using `[Formalism.L2.KerInert.VC.phi_eq, show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Simplify using `[Formalism.L2.KerInert.VC.vv, PowerSeries.constantCoeff_invOfUnit]`. Establish `huu : ((C.u : Kˣ) : K) * ((C.u⁻¹ : Kˣ) : K) = 1`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `spec` using `Formalism.L2.Th1.A.compInvSpec K (phi W C) hφ0 (by rw [h1]; exact (C.u).isUnit)`.

Establish `hψ0 : PowerSeries.constantCoeff (Formalism.L2.Th1.A.compInv (phi W C)) = 0` using `spec.1`. Establish `hψ` using `PowerSeries.HasSubst.of_constantCoeff_zero' hψ0`. Establish `hψI : IntPS R' (Formalism.L2.Th1.A.compInv (phi W C))` using `Formalism.L2.KerInert.VC.intPS_compInv (R' := R') (hf := Formalism.L2.KerInert.VC.intPS_phi W hW C hu hr hs ht) (h0 := hφ0) (hui := hu') (h1 := h1) (huu := huu)`. Establish `hψpt : IsPt R' ((Formalism.L2.Th1.A.compInv (phi W C) : K⟦X⟧) : MvPowerSeries Unit K)` using `⟨hψ0, intMv_coe_of_intPS hψI⟩`. Establish `hℓ0 : PowerSeries.constantCoeff (Formalism.L2.Th1.A.logSer W) = 0` using `Formalism.L2.Th1.A.ZSer.log_cc (W := W)`.

Establish `hm0 : PowerSeries.constantCoeff (mulBy (Formalism.L2.Th1.A.logSer W) (Formalism.L2.Th1.A.expSer W) c) = 0`. Unfold `mulBy`. Conclude with `constantCoeff_subst_eq_zero_inert_coprime (by simp [hℓ0]) (constantCoeff_compInv _)`. Establish `hm` using `PowerSeries.HasSubst.of_constantCoeff_zero' hm0`. Establish `hmψ0 : PowerSeries.constantCoeff (PowerSeries.subst (Formalism.L2.Th1.A.compInv (phi W C)) (mulBy (Formalism.L2.Th1.A.logSer W) (Formalism.L2.Th1.A.expSer W) c)) = 0` using `constantCoeff_subst_eq_zero_inert_coprime hψ0 hm0`.

Establish `hmψ` using `PowerSeries.HasSubst.of_constantCoeff_zero' hmψ0`. Establish `hmψpt : IsPt R' ((PowerSeries.subst (Formalism.L2.Th1.A.compInv (phi W C)) (mulBy (Formalism.L2.Th1.A.logSer W) (Formalism.L2.Th1.A.expSer W) c) : K⟦X⟧) : MvPowerSeries Unit K)` using `⟨hmψ0, Formalism.L2.Th1.C.intSubst K R' _ hE Unit _ hψpt⟩`. Establish `hD` using `cong_phi W hW C hu hu' hr hs ht s2`. Take `⟨D, hDdef⟩ : ∃ D : K⟦X⟧, D = PowerSeries.subst (phi W C) (Formalism.L2.Th1.B.phW (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2)) - Formalism.L2.Th1.B.phW W s2` from `⟨_, rfl⟩`. Establish `hDLG : LG R' (D : MvPowerSeries Unit K)` using `by rw [hDdef]; exact hD`.

Establish `e1 : PowerSeries.subst (phi W C) (Formalism.L2.Th1.B.phW (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2)) = Formalism.L2.Th1.B.phW W s2 + D` using `by rw [hDdef]; ring`. Establish `e2 : Formalism.L2.Th1.B.phW (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2) = PowerSeries.subst (Formalism.L2.Th1.A.compInv (phi W C)) (Formalism.L2.Th1.B.phW W s2 + D)`. Rewrite using `[← e1, PowerSeries.subst_comp_subst_apply hφ hψ, spec.2.1, powerSeries_subst_X]`. Establish `hadd : ∀ (a f g : K⟦X⟧), PowerSeries.HasSubst a → PowerSeries.subst a (f + g) = PowerSeries.subst a f + PowerSeries.subst a g`. Introduce `a f g ha`.

Rewrite using `[← PowerSeries.coe_substAlgHom ha, map_add]`. Establish `hL1` using `Formalism.L2.Th1.C.lGSubst K R' _ h Unit _ hψpt`. Establish `hL2` using `Formalism.L2.Th1.C.lGSubst K R' _ hDLG Unit _ hmψpt`. Establish `hL3` using `lg_intsmul N (Formalism.L2.Th1.C.lGSubst K R' _ hDLG Unit _ hψpt)`. Unfold `PhNormAt Cong`.

Rewrite using `[Formalism.L2.KerInert.VC.mulBy_eq, ← PowerSeries.subst_comp_subst_apply hφ hmψ, e1, hadd _ _ _ hmψ, ← PowerSeries.subst_comp_subst_apply hm hψ]`. Rewrite using `[e2]`. Rewrite using `[hadd _ _ _ hψ, hN]`. Establish `e3 : PowerSeries.subst (Formalism.L2.Th1.A.compInv (phi W C)) (PowerSeries.subst (mulBy (Formalism.L2.Th1.A.logSer W) (Formalism.L2.Th1.A.expSer W) c) (Formalism.L2.Th1.B.phW W s2) - (N : K) • Formalism.L2.Th1.B.phW W s2) = PowerSeries.subst (Formalism.L2.Th1.A.compInv (phi W C)) …`. Rewrite using `[subst_sub' hψ0, subst_smul' hψ0]`.

Rewrite `hL1` using `[hN]`. Rewrite `hL1` using `[e3]`. Use `Formalism.L2.Th1.C.Calc.lg_add (Formalism.L2.Th1.C.Calc.lg_add hL1 hL2) (Formalism.L2.Th1.C.Calc.lg_neg hL3)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[smul_add]`.

Normalize the expressions using the abelian group laws.
-/
theorem phNormAt_varChange (W : WeierstrassCurve K) (hW : CoeffIn R' W) (C : WeierstrassCurve.VariableChange K)
    (hu : ((C.u : Kˣ) : K) ∈ R') (hu' : ((C.u⁻¹ : Kˣ) : K) ∈ R') (hr : C.r ∈ R') (hs : C.s ∈ R') (ht : C.t ∈ R')
    (s2 c cb : K) (N : ℤ) (hN : c * cb = N)
    (hE : EndInt R' (Formalism.L2.Th1.A.logSer W) (Formalism.L2.Th1.A.expSer W) c)
    (h : PhNormAt R' (Formalism.L2.Th1.A.logSer W) (Formalism.L2.Th1.A.expSer W) (Formalism.L2.Th1.B.phW W s2) c cb) :
    PhNormAt R' (Formalism.L2.Th1.A.logSer (C • W)) (Formalism.L2.Th1.A.expSer (C • W))
      (Formalism.L2.Th1.B.phW (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2)) c cb := by
  have hφ0 : PowerSeries.constantCoeff (phi W C) = 0 := by
    rw [Formalism.L2.KerInert.VC.phi_eq]; simp
  have hφ := PowerSeries.HasSubst.of_constantCoeff_zero' hφ0
  have h1 : PowerSeries.coeff 1 (phi W C) = ((C.u : Kˣ) : K) := by
    rw [Formalism.L2.KerInert.VC.phi_eq, show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [Formalism.L2.KerInert.VC.vv, PowerSeries.constantCoeff_invOfUnit]
  have huu : ((C.u : Kˣ) : K) * ((C.u⁻¹ : Kˣ) : K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have spec := Formalism.L2.Th1.A.compInvSpec K (phi W C) hφ0 (by rw [h1]; exact (C.u).isUnit)
  have hψ0 : PowerSeries.constantCoeff (Formalism.L2.Th1.A.compInv (phi W C)) = 0 := spec.1
  have hψ := PowerSeries.HasSubst.of_constantCoeff_zero' hψ0
  have hψI : IntPS R' (Formalism.L2.Th1.A.compInv (phi W C)) :=
    Formalism.L2.KerInert.VC.intPS_compInv (R' := R') (hf := Formalism.L2.KerInert.VC.intPS_phi W hW C hu hr hs ht)
      (h0 := hφ0) (hui := hu') (h1 := h1) (huu := huu)
  have hψpt : IsPt R' ((Formalism.L2.Th1.A.compInv (phi W C) : K⟦X⟧) : MvPowerSeries Unit K) := ⟨hψ0, intMv_coe_of_intPS hψI⟩
  have hℓ0 : PowerSeries.constantCoeff (Formalism.L2.Th1.A.logSer W) = 0 := Formalism.L2.Th1.A.ZSer.log_cc (W := W)
  have hm0 : PowerSeries.constantCoeff (mulBy (Formalism.L2.Th1.A.logSer W) (Formalism.L2.Th1.A.expSer W) c) = 0 := by
    unfold mulBy
    exact constantCoeff_subst_eq_zero_inert_coprime (by simp [hℓ0]) (constantCoeff_compInv _)
  have hm := PowerSeries.HasSubst.of_constantCoeff_zero' hm0
  have hmψ0 : PowerSeries.constantCoeff (PowerSeries.subst (Formalism.L2.Th1.A.compInv (phi W C))
      (mulBy (Formalism.L2.Th1.A.logSer W) (Formalism.L2.Th1.A.expSer W) c)) = 0 := constantCoeff_subst_eq_zero_inert_coprime hψ0 hm0
  have hmψ := PowerSeries.HasSubst.of_constantCoeff_zero' hmψ0
  have hmψpt : IsPt R' ((PowerSeries.subst (Formalism.L2.Th1.A.compInv (phi W C))
      (mulBy (Formalism.L2.Th1.A.logSer W) (Formalism.L2.Th1.A.expSer W) c) : K⟦X⟧) : MvPowerSeries Unit K) :=
    ⟨hmψ0, Formalism.L2.Th1.C.intSubst K R' _ hE Unit _ hψpt⟩
  have hD := cong_phi W hW C hu hu' hr hs ht s2
  obtain ⟨D, hDdef⟩ : ∃ D : K⟦X⟧, D = PowerSeries.subst (phi W C)
      (Formalism.L2.Th1.B.phW (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2)) - Formalism.L2.Th1.B.phW W s2 := ⟨_, rfl⟩
  have hDLG : LG R' (D : MvPowerSeries Unit K) := by rw [hDdef]; exact hD
  have e1 : PowerSeries.subst (phi W C) (Formalism.L2.Th1.B.phW (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2)) =
      Formalism.L2.Th1.B.phW W s2 + D := by rw [hDdef]; ring
  have e2 : Formalism.L2.Th1.B.phW (C • W) (((C.u⁻¹ : Kˣ) : K) ^ 2 * s2) =
      PowerSeries.subst (Formalism.L2.Th1.A.compInv (phi W C)) (Formalism.L2.Th1.B.phW W s2 + D) := by
    rw [← e1, PowerSeries.subst_comp_subst_apply hφ hψ, spec.2.1, powerSeries_subst_X]
  have hadd : ∀ (a f g : K⟦X⟧), PowerSeries.HasSubst a →
      PowerSeries.subst a (f + g) = PowerSeries.subst a f + PowerSeries.subst a g := by
    intro a f g ha
    rw [← PowerSeries.coe_substAlgHom ha, map_add]
  have hL1 := Formalism.L2.Th1.C.lGSubst K R' _ h Unit _ hψpt
  have hL2 := Formalism.L2.Th1.C.lGSubst K R' _ hDLG Unit _ hmψpt
  have hL3 := lg_intsmul N (Formalism.L2.Th1.C.lGSubst K R' _ hDLG Unit _ hψpt)
  unfold PhNormAt Cong
  rw [Formalism.L2.KerInert.VC.mulBy_eq, ← PowerSeries.subst_comp_subst_apply hφ hmψ, e1, hadd _ _ _ hmψ,
    ← PowerSeries.subst_comp_subst_apply hm hψ]
  rw [e2]
  rw [hadd _ _ _ hψ, hN]
  have e3 : PowerSeries.subst (Formalism.L2.Th1.A.compInv (phi W C))
      (PowerSeries.subst (mulBy (Formalism.L2.Th1.A.logSer W) (Formalism.L2.Th1.A.expSer W) c) (Formalism.L2.Th1.B.phW W s2)
        - (N : K) • Formalism.L2.Th1.B.phW W s2) =
      PowerSeries.subst (Formalism.L2.Th1.A.compInv (phi W C))
        (PowerSeries.subst (mulBy (Formalism.L2.Th1.A.logSer W) (Formalism.L2.Th1.A.expSer W) c) (Formalism.L2.Th1.B.phW W s2))
      - (N : K) • PowerSeries.subst (Formalism.L2.Th1.A.compInv (phi W C)) (Formalism.L2.Th1.B.phW W s2) := by
    rw [subst_sub' hψ0, subst_smul' hψ0]
  rw [hN] at hL1
  rw [e3] at hL1
  have := Formalism.L2.Th1.C.Calc.lg_add (Formalism.L2.Th1.C.Calc.lg_add hL1 hL2) (Formalism.L2.Th1.C.Calc.lg_neg hL3)
  convert this using 1
  rw [smul_add]
  abel

end Transfer

section Main

open Formalism.BasicNotions Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric NumberField Formalism.L2.KerInert.IwahoriBlocks

/- English proof (translation)
Introduce `D p _ cc δ g hAt h5 hIn hOW a _hcop`. Take `⟨hcurve, -, hδ12, hLam, hOk⟩` from `hAt`. Establish `hcc : cc ≠ ⊥` using `hcurve.1`. Establish `hδ : δ ≠ 0` using `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.brcc_delta_ne D cc hcurve δ hδ12`. Take `⟨⟨L, hL⟩, -⟩` from `Formalism.L2.Th1.F2.lamOfLat D cc δ hcc hδ`.

Establish `hLg : g.abelian₂ = L.lattice.toAddSubgroup` using `hLam.trans hL.symm`. Take `⟨hg2, hg3⟩` from `Formalism.L2.KerInert.Sigma.invAlg' D cc δ hcurve hδ12 L hL`. Establish `hs2` using `Formalism.L2.KerInert.Sigma.secondEisensteinAlgebraic D cc δ hcurve hδ12 L hL`. Use `set a2 : Qbar := ⟨L.g₂, hg2⟩ with ha2`. Use `set a3 : Qbar := ⟨L.g₃, hg3⟩ with ha3`.

Use `set s0 : Qbar := ⟨Formalism.L2.Th1.F.s2 L, hs2⟩ with hs0`. Take `⟨e2, e3⟩` from `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L (congrArg (fun A : AddSubgroup ℂ => (A : Set ℂ)) hLg.symm)`. Establish `hd4 : D.host.d % 4 = 3` using `by have := D.host.hyp.2.2.2.1; omega`. Establish `hcmby` using `Formalism.L2.KerInert.Sigma.ChartWirtingerDerivatives.hasCMBy_curve D cc δ hcurve hδ12 L hL`. Establish `hdisc` using `Formalism.L2.KerInert.Sigma.ChartWirtingerDerivatives.disc_curve D cc δ hcurve hδ12 L hL`.

Take `⟨ι, hι⟩` from `Formalism.L2.KerInert.lamExt p g.lam`. Establish `hιg2 : ι L.g₂ = g.lam a2` using `hι a2`. Establish `hιg3 : ι L.g₃ = g.lam a3` using `hι a3`. Establish `hιs : ι (Formalism.L2.Th1.F.s2 L) = g.lam s0` using `hι s0`. Establish `hwm : wModel g.lam g.abelian₂ = Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃)`.

Establish `e4 : lamC g.lam (-(g2 g.abelian₂) / 4) = -(g.lam a2) / 4`. Establish `: -(g2 g.abelian₂) / 4 = ((-a2 / 4 : Qbar) : ℂ)` using `by rw [e2]; push_cast; rfl`. Rewrite using `[this, Formalism.L2.KerInert.Sigma.lamC_coe, map_div₀, map_neg, map_ofNat]`. Establish `e6 : lamC g.lam (-(g3 g.abelian₂) / 4) = -(g.lam a3) / 4`. Establish `: -(g3 g.abelian₂) / 4 = ((-a3 / 4 : Qbar) : ℂ)` using `by rw [e3]; push_cast; rfl`.

Rewrite using `[this, Formalism.L2.KerInert.Sigma.lamC_coe, map_div₀, map_neg, map_ofNat]`. Rewrite using `[hιg2, hιg3]`. Apply the tactic sequence `ext <;> simp [wModel, Formalism.L2.Th1.A.shortW, e4, e6]`. Use `set W0 : WeierstrassCurve ℂ_[p] := Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃) with hW0`. Establish `hgW : g.W = g.C • W0` using `by rw [G1.W, hwm]`.

Use `set ε : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hε`. Establish `hΔ0 : W0.Δ = 1`. Establish `e : W0.Δ = ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2`. Simplify using `only [hW0, Formalism.L2.Th1.A.shortW, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, ← map_pow, ← map_pow, ← map_ofNat ι 27, ← map_mul, ← map_sub, hdisc, map_one]`. Take `⟨i1, i2, i3, i4, i6, hΔ⟩` from `hOk.1`. Take `⟨w1, w2, w3, w4, w6⟩` from `hOW`. Take `⟨k2, k3, n2, n3, nd⟩` from `Formalism.L2.KerInert.Sigma.inv_good g.W h5 i1 i2 i3 i4 i6 hΔ w1 w2 w3 w4 w6`. Establish `j1 : ‖(g.C • W0).a₁‖ ≤ 1` using `by rw [← hgW]; exact i1`.

Establish `j2 : ‖(g.C • W0).a₂‖ ≤ 1` using `by rw [← hgW]; exact i2`. Establish `j3 : ‖(g.C • W0).a₃‖ ≤ 1` using `by rw [← hgW]; exact i3`. Establish `jΔ : ‖(g.C • W0).Δ‖ = 1` using `by rw [← hgW]; exact hΔ`. Take `⟨hu, hui, hr, hs, ht⟩` from `vc_params h5 W0 rfl rfl rfl (by rw [hΔ0, norm_one]) g.C j1 j2 j3 jΔ`. Establish `hW0'` using `Formalism.L2.KerInert.Sigma.wModel_g g.lam g.abelian₂ a2 a3 e2 e3`.

Rewrite `hW0'` using `[hwm]`. Take `⟨c2, c3⟩` from `g_change' W0 g.C`. Rewrite `c2` using `[← hgW, hW0'.1]`. Rewrite `c3` using `[← hgW, hW0'.2]`. Take `⟨t2, -⟩` from `norm_two_three (p := p) h5`.

Establish `t4 : ‖(4 : ℂ_[p])‖ = 1`. Rewrite using `[show (4 : ℂ_[p]) = 2 * 2 by norm_num, norm_mul, t2, one_mul]`. Establish `m2 : ‖ι L.g₂‖ ≤ 1`. Rewrite `n2` using `[c2, norm_mul, norm_pow, hui, one_pow, one_mul, ← hιg2]`. Conclude with `n2`.

Establish `m3 : ‖ι L.g₃‖ ≤ 1`. Rewrite `n3` using `[c3, norm_mul, norm_pow, hui, one_pow, one_mul, ← hιg3]`. Conclude with `n3`. Establish `hIC : Formalism.L2.Th1.E.IntCurve (Formalism.L2.Th1.E.curveL p L ι)`. Use `⟨by simp [Formalism.L2.Th1.E.curveL, Formalism.L2.Th1.A.shortW], by simp [Formalism.L2.Th1.E.curveL, Formalism.L2.Th1.A.shortW], by simp [Formalism.L2.Th1.E.curveL, Formalism.L2.Th1.A.shortW], ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `show ‖-(ι L.g₂) / 4‖ ≤ 1`. Rewrite using `[norm_div, norm_neg, t4, div_one]`. Conclude with `m2`. Use `show ‖-(ι L.g₃) / 4‖ ≤ 1`. Rewrite using `[norm_div, norm_neg, t4, div_one]`.

Conclude with `m3`. Use `show ‖W0.Δ‖ = 1`. Rewrite using `[hΔ0, norm_one]`. Establish `hcoef0 : Formalism.L2.Th1.C.CoeffIn (RB p) W0`. Take `⟨q1, q2, q3, q4, q6, -⟩` from `hIC`.

Conclude with `⟨q1, q2, q3, q4, q6⟩`. Take `⟨ωK, hω, hspan⟩` from `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.covA_span D.host.K D.host.d (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.discriminant_mod_four D) ⟨D.host.sqrtMinusD, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_sqrt_mem D⟩ (Formalism.L2.Glo …`. Use `set xs : D.host.K := ⟨D.host.sqrtMinusD, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_sqrt_mem D⟩ with hxs`. Establish `hx2 : (D.host.φ₀ (xs : D.host.E)) ^ 2 = -(D.host.d : ℂ)`. Establish `h` using `congrArg (fun y : D.host.K => D.host.φ₀ (y : D.host.E)) (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_sqrt_sq D)`.

Rewrite `h` using `[← hxs]`. Move the coercions through the operations in `at h`. Rewrite `h` using `[map_pow]`. Rewrite using `[h, map_neg, map_natCast]`. Use `set ω := Formalism.L2.Th1.CM.omegaK D.host.d with hωdef`.

Establish `hom : (2 * ω - 1) ^ 2 = -(D.host.d : ℂ)`. Rewrite using `[hωdef]`. Unfold `Formalism.L2.Th1.CM.omegaK`. Establish `hsq : ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 = (D.host.d : ℂ)`. Rewrite using `[← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]`.

Use `push_cast`. Both sides reduce to the same expression. Take the linear combination `(-1 : ℂ) * hsq + (((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2) * Complex.I_sq`. Establish `hconjω : starRingEnd ℂ ω = 1 - ω`. Rewrite using `[hωdef]`.

Unfold `Formalism.L2.Th1.CM.omegaK`. Simplify using `only [map_div₀, map_add, map_one, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2E : ((2 : D.host.K) : D.host.E) = 2`. Rewrite using `[show (2 : D.host.K) = 1 + 1 by norm_num]; push_cast; norm_num`.

Establish `hωφ : D.host.φ₀ ((ωK : D.host.K) : D.host.E) = (1 + D.host.φ₀ (xs : D.host.E)) / 2`. Rewrite using `[hω]`. Use `push_cast`. Simplify using `only [map_div₀, map_add, map_one]`. Rewrite using `[h2E, map_ofNat]`.

Establish `hc : ∀ k : ℤ, ((k : 𝓞 D.host.K) : D.host.K) = (k : D.host.K)` using `fun k => by`. Rewrite using `[NumberField.RingOfIntegers.coe_eq_algebraMap, map_intCast]`. Take `⟨m, n, rfl⟩` from `hspan a`. Establish `ea : (((m : 𝓞 D.host.K) + (n : 𝓞 D.host.K) * ωK : 𝓞 D.host.K) : D.host.K) = (m : D.host.K) + (n : D.host.K) * (ωK : D.host.K)`. Rewrite using `[NumberField.RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_intCast, map_intCast, ← NumberField.RingOfIntegers.coe_eq_algebraMap]`.

Use `set z : ℂ := D.host.φ₀ ((((m : 𝓞 D.host.K) + (n : 𝓞 D.host.K) * ωK : 𝓞 D.host.K) : D.host.K) : D.host.E) with hz`. Establish `hzv : z = (m : ℂ) + (n : ℂ) * D.host.φ₀ ((ωK : D.host.K) : D.host.E)`. Rewrite using `[hz, ea]`. Use `push_cast`. Simplify using `only [map_add, map_mul, map_intCast]`.

Establish `hzb : D.host.φ₀ (D.host.conj ((((m : 𝓞 D.host.K) + (n : 𝓞 D.host.K) * ωK : 𝓞 D.host.K) : D.host.K) : D.host.E)) = starRingEnd ℂ z` using `Formalism.BasicNotions.Examples₂.emb_conj D.host D.host.φ₀ _`. Establish `hpair : ∃ m' n' : ℤ, z = (m' : ℂ) + (n' : ℂ) * ω ∧ starRingEnd ℂ z = (m' : ℂ) + (n' : ℂ) * (1 - ω)`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 (hx2.trans hom.symm) with h | h` into its components or cases. Establish `e : D.host.φ₀ ((ωK : D.host.K) : D.host.E) = ω` using `by rw [hωφ, h]; ring`. Use `⟨m, n, by rw [hzv, e], ?_⟩` and prove the remaining obligations.

Rewrite using `[hzv, e, map_add, map_mul, map_intCast, map_intCast, hconjω]`. Establish `e : D.host.φ₀ ((ωK : D.host.K) : D.host.E) = 1 - ω` using `by rw [hωφ, h]; ring`. Use `⟨m + n, -n, by rw [hzv, e]; push_cast; ring, ?_⟩` and prove the remaining obligations. Rewrite using `[hzv, e, map_add, map_mul, map_intCast, map_intCast, map_sub, map_one, hconjω]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨m', n', hz1, hz2⟩` from `hpair`. Establish `hcτ : tauK D g.lam ((((m : 𝓞 D.host.K) + (n : 𝓞 D.host.K) * ωK : 𝓞 D.host.K) : D.host.K)) = ι z` using `(Formalism.L2.KerInert.lamCIota p g.lam ι hι).1 _ (Formalism.MainNotions.Ext.test_vector_mem_schwartz_bruhat D _)`. Establish `hcbτ : tauKc D g.lam ((((m : 𝓞 D.host.K) + (n : 𝓞 D.host.K) * ωK : 𝓞 D.host.K) : D.host.K)) = ι (starRingEnd ℂ z)`. Unfold `tauKc`.

Rewrite using `[← hzb]`. Conclude with `(Formalism.L2.KerInert.lamCIota p g.lam ι hι).1 _ (Formalism.MainNotions.Ext.test_vector_mem_schwartz_bruhat D _)`. Rewrite using `[hcτ, hcbτ]`. Use `set k : ℕ := (D.host.d + 1) / 4 with hk`. Establish `hq` using `ReciprocityTheory.ChartRestriction.L1.omegaK_quad D.host.d hd4`.

Establish `hN : ι z * ι (starRingEnd ℂ z) = (((m' ^ 2 + m' * n' + n' ^ 2 * (k : ℤ) : ℤ)) : ℂ_[p])`. Rewrite using `[← map_mul, hz2, hz1, ← map_intCast ι]`. Use `congr 1`. Use `push_cast`. Take the linear combination `(-(n' : ℂ) ^ 2) * hq`.

Establish `hmem : (ι z, ι (starRingEnd ℂ z)) ∈ Formalism.L2.Th1.Top.pairsK D.host.d p ι`. Use `subset_closure ⟨(m', n'), ?_⟩` and prove the remaining obligations. Use `show (ι ((m' : ℂ) + (n' : ℂ) * ω), ι ((m' : ℂ) + (n' : ℂ) * (1 - ω))) = (ι z, ι (starRingEnd ℂ z))`. Rewrite using `[hz2, hz1]`. Take `⟨-, -, hpairs, -⟩` from `Formalism.L2.Th1.Top.calcP D.host.d L hd4 hcmby p h5 ι hIC`.

Take `⟨hE0, hPN0, -⟩` from `hpairs _ _ hmem`. Establish `hT` using `phNormAt_varChange W0 hcoef0 g.C hu.le hui.le hr hs ht (ι (Formalism.L2.Th1.F.s2 L)) _ _ _ hN hE0 hPN0`. Rewrite `hT` using `[← hgW]`. Establish `hser : sgSer g.lam g.abelian₂ = Formalism.L2.Th1.B.sgStar (g.lam s0) (Formalism.L2.Th1.F.pOf (g.lam a2) (g.lam a3))`. Rewrite using `[hLg]`.

Conclude with `Formalism.L2.KerInert.Sigma.sgSer_eq g.lam L a2 a3 s0 rfl rfl rfl`. Establish `hwp : Formalism.L2.Th1.A.wpReg g.W = PowerSeries.C (ε ^ 2) * PowerSeries.rescale ε (Formalism.L2.Th1.F.pOf (g.lam a2) (g.lam a3))`. Rewrite using `[Formalism.L2.KerInert.Sigma.wpReg_eq, c2, c3]`. Conclude with `(Formalism.L2.Th1.F.seriesScale ℂ_[p] (g.lam a2) (g.lam a3) ε).2.2.2.1`. Establish `hR : PowerSeries.rescale ε (sgSer g.lam g.abelian₂) = PowerSeries.C ε * Formalism.L2.Th1.B.sgW g.W (ε ^ 2 * ι (Formalism.L2.Th1.F.s2 L))`.

Unfold `Formalism.L2.Th1.B.sgW`. Rewrite using `[hser, hwp, hιs]`. Conclude with `((Formalism.L2.Th1.F.sigmaScale ℂ_[p] (Formalism.L2.Th1.F.pOf (g.lam a2) (g.lam a3)) (g.lam s0) ε).2).symm`. Establish `hph : g.ph = Formalism.L2.Th1.B.phW g.W (ε ^ 2 * ι (Formalism.L2.Th1.F.s2 L))` using `Formalism.L2.KerInert.Dict.formal_phase_agree p g _ hOk hR`. Establish `hX : (g.phAt (Xv ()) : MvPowerSeries Unit ℂ_[p]) = g.ph` using `PowerSeries.X_subst g.ph`.

Establish `hM : (g.phAt (g.mulBy (ι z) (Xv ())) : MvPowerSeries Unit ℂ_[p]) = PowerSeries.subst (Formalism.L2.Th1.C.mulBy (Formalism.L2.Th1.A.logSer g.W) (Formalism.L2.Th1.A.expSer g.W) (ι z)) g.ph`. Unfold `G1.phAt`. Rewrite using `[mulBy_g g hOk]`. Rewrite using `[hM, hX, hph]`. Establish `hsm : (MvPowerSeries.C (ι z * ι (starRingEnd ℂ z)) * Formalism.L2.Th1.B.phW g.W (ε ^ 2 * ι (Formalism.L2.Th1.F.s2 L)) : MvPowerSeries Unit ℂ_[p]) = ((ι z * ι (starRingEnd ℂ z)) • Formalism.L2.Th1.B.phW g.W (ε ^ 2 * ι (Formalism.L2.Th1.F.s2 L)) : ℂ_[p]⟦X⟧)`.

Rewrite using `[PowerSeries.smul_eq_C_mul]`. Both sides reduce to the same expression. Rewrite using `[hsm]`. Take `⟨h0, h1⟩` from `hT`. Use `⟨h0, ?_⟩` and prove the remaining obligations.

Rewrite using `[Formalism.L2.KerInert.Dict.expMv_eq_mvExp h0]`. Introduce `e`. Conclude with `h1 e`.
-/
theorem phNormOKInert_of : Formalism.L2.KerInert.PhNormOKInert := by
  intro D p _ cc δ g hAt h5 hIn hOW a _hcop
  obtain ⟨hcurve, -, hδ12, hLam, hOk⟩ := hAt
  have hcc : cc ≠ ⊥ := hcurve.1
  have hδ : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.brcc_delta_ne D cc hcurve δ hδ12
  obtain ⟨⟨L, hL⟩, -⟩ := Formalism.L2.Th1.F2.lamOfLat D cc δ hcc hδ
  have hLg : g.abelian₂ = L.lattice.toAddSubgroup := hLam.trans hL.symm
  obtain ⟨hg2, hg3⟩ := Formalism.L2.KerInert.Sigma.invAlg' D cc δ hcurve hδ12 L hL
  have hs2 := Formalism.L2.KerInert.Sigma.secondEisensteinAlgebraic D cc δ hcurve hδ12 L hL
  set a2 : Qbar := ⟨L.g₂, hg2⟩ with ha2
  set a3 : Qbar := ⟨L.g₃, hg3⟩ with ha3
  set s0 : Qbar := ⟨Formalism.L2.Th1.F.s2 L, hs2⟩ with hs0
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L (congrArg (fun A : AddSubgroup ℂ => (A : Set ℂ)) hLg.symm)
  have hd4 : D.host.d % 4 = 3 := by have := D.host.hyp.2.2.2.1; omega
  have hcmby := Formalism.L2.KerInert.Sigma.ChartWirtingerDerivatives.hasCMBy_curve D cc δ hcurve hδ12 L hL
  have hdisc := Formalism.L2.KerInert.Sigma.ChartWirtingerDerivatives.disc_curve D cc δ hcurve hδ12 L hL
  obtain ⟨ι, hι⟩ := Formalism.L2.KerInert.lamExt p g.lam
  have hιg2 : ι L.g₂ = g.lam a2 := hι a2
  have hιg3 : ι L.g₃ = g.lam a3 := hι a3
  have hιs : ι (Formalism.L2.Th1.F.s2 L) = g.lam s0 := hι s0
  have hwm : wModel g.lam g.abelian₂ = Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃) := by
    have e4 : lamC g.lam (-(g2 g.abelian₂) / 4) = -(g.lam a2) / 4 := by
      have : -(g2 g.abelian₂) / 4 = ((-a2 / 4 : Qbar) : ℂ) := by rw [e2]; push_cast; rfl
      rw [this, Formalism.L2.KerInert.Sigma.lamC_coe, map_div₀, map_neg, map_ofNat]
    have e6 : lamC g.lam (-(g3 g.abelian₂) / 4) = -(g.lam a3) / 4 := by
      have : -(g3 g.abelian₂) / 4 = ((-a3 / 4 : Qbar) : ℂ) := by rw [e3]; push_cast; rfl
      rw [this, Formalism.L2.KerInert.Sigma.lamC_coe, map_div₀, map_neg, map_ofNat]
    rw [hιg2, hιg3]
    ext <;> simp [wModel, Formalism.L2.Th1.A.shortW, e4, e6]
  set W0 : WeierstrassCurve ℂ_[p] := Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃) with hW0
  have hgW : g.W = g.C • W0 := by rw [G1.W, hwm]
  set ε : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hε

  have hΔ0 : W0.Δ = 1 := by
    have e : W0.Δ = ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2 := by
      simp only [hW0, Formalism.L2.Th1.A.shortW, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring
    rw [e, ← map_pow, ← map_pow, ← map_ofNat ι 27, ← map_mul, ← map_sub, hdisc, map_one]
  obtain ⟨i1, i2, i3, i4, i6, hΔ⟩ := hOk.1
  obtain ⟨w1, w2, w3, w4, w6⟩ := hOW
  obtain ⟨k2, k3, n2, n3, nd⟩ := Formalism.L2.KerInert.Sigma.inv_good g.W h5 i1 i2 i3 i4 i6 hΔ w1 w2 w3 w4 w6
  have j1 : ‖(g.C • W0).a₁‖ ≤ 1 := by rw [← hgW]; exact i1
  have j2 : ‖(g.C • W0).a₂‖ ≤ 1 := by rw [← hgW]; exact i2
  have j3 : ‖(g.C • W0).a₃‖ ≤ 1 := by rw [← hgW]; exact i3
  have jΔ : ‖(g.C • W0).Δ‖ = 1 := by rw [← hgW]; exact hΔ
  obtain ⟨hu, hui, hr, hs, ht⟩ := vc_params h5 W0 rfl rfl rfl (by rw [hΔ0, norm_one]) g.C j1 j2 j3 jΔ
  have hW0' := Formalism.L2.KerInert.Sigma.wModel_g g.lam g.abelian₂ a2 a3 e2 e3
  rw [hwm] at hW0'
  obtain ⟨c2, c3⟩ := g_change' W0 g.C
  rw [← hgW, hW0'.1] at c2
  rw [← hgW, hW0'.2] at c3
  obtain ⟨t2, -⟩ := norm_two_three (p := p) h5
  have t4 : ‖(4 : ℂ_[p])‖ = 1 := by
    rw [show (4 : ℂ_[p]) = 2 * 2 by norm_num, norm_mul, t2, one_mul]
  have m2 : ‖ι L.g₂‖ ≤ 1 := by
    rw [c2, norm_mul, norm_pow, hui, one_pow, one_mul, ← hιg2] at n2; exact n2
  have m3 : ‖ι L.g₃‖ ≤ 1 := by
    rw [c3, norm_mul, norm_pow, hui, one_pow, one_mul, ← hιg3] at n3; exact n3
  have hIC : Formalism.L2.Th1.E.IntCurve (Formalism.L2.Th1.E.curveL p L ι) := by
    refine ⟨by simp [Formalism.L2.Th1.E.curveL, Formalism.L2.Th1.A.shortW], by simp [Formalism.L2.Th1.E.curveL, Formalism.L2.Th1.A.shortW],
      by simp [Formalism.L2.Th1.E.curveL, Formalism.L2.Th1.A.shortW], ?_, ?_, ?_⟩
    · show ‖-(ι L.g₂) / 4‖ ≤ 1
      rw [norm_div, norm_neg, t4, div_one]; exact m2
    · show ‖-(ι L.g₃) / 4‖ ≤ 1
      rw [norm_div, norm_neg, t4, div_one]; exact m3
    · show ‖W0.Δ‖ = 1
      rw [hΔ0, norm_one]
  have hcoef0 : Formalism.L2.Th1.C.CoeffIn (RB p) W0 := by
    obtain ⟨q1, q2, q3, q4, q6, -⟩ := hIC
    exact ⟨q1, q2, q3, q4, q6⟩

  obtain ⟨ωK, hω, hspan⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.covA_span D.host.K D.host.d (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.discriminant_mod_four D)
    ⟨D.host.sqrtMinusD, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_sqrt_mem D⟩ (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_sqrt_sq D)
    (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_finrank_K D)
  set xs : D.host.K := ⟨D.host.sqrtMinusD, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_sqrt_mem D⟩ with hxs
  have hx2 : (D.host.φ₀ (xs : D.host.E)) ^ 2 = -(D.host.d : ℂ) := by
    have h := congrArg (fun y : D.host.K => D.host.φ₀ (y : D.host.E)) (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_sqrt_sq D)
    rw [← hxs] at h
    push_cast at h
    rw [map_pow] at h
    rw [h, map_neg, map_natCast]
  set ω := Formalism.L2.Th1.CM.omegaK D.host.d with hωdef
  have hom : (2 * ω - 1) ^ 2 = -(D.host.d : ℂ) := by
    rw [hωdef]; unfold Formalism.L2.Th1.CM.omegaK
    have hsq : ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 = (D.host.d : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; push_cast; rfl
    linear_combination (-1 : ℂ) * hsq + (((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2) * Complex.I_sq
  have hconjω : starRingEnd ℂ ω = 1 - ω := by
    rw [hωdef]; unfold Formalism.L2.Th1.CM.omegaK
    simp only [map_div₀, map_add, map_one, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  have h2E : ((2 : D.host.K) : D.host.E) = 2 := by
    rw [show (2 : D.host.K) = 1 + 1 by norm_num]; push_cast; norm_num
  have hωφ : D.host.φ₀ ((ωK : D.host.K) : D.host.E) = (1 + D.host.φ₀ (xs : D.host.E)) / 2 := by
    rw [hω]; push_cast; simp only [map_div₀, map_add, map_one]; rw [h2E, map_ofNat]
  have hc : ∀ k : ℤ, ((k : 𝓞 D.host.K) : D.host.K) = (k : D.host.K) := fun k => by
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap, map_intCast]
  obtain ⟨m, n, rfl⟩ := hspan a
  have ea : (((m : 𝓞 D.host.K) + (n : 𝓞 D.host.K) * ωK : 𝓞 D.host.K) : D.host.K) =
      (m : D.host.K) + (n : D.host.K) * (ωK : D.host.K) := by
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_intCast, map_intCast,
      ← NumberField.RingOfIntegers.coe_eq_algebraMap]
  set z : ℂ := D.host.φ₀ ((((m : 𝓞 D.host.K) + (n : 𝓞 D.host.K) * ωK : 𝓞 D.host.K) : D.host.K) : D.host.E) with hz
  have hzv : z = (m : ℂ) + (n : ℂ) * D.host.φ₀ ((ωK : D.host.K) : D.host.E) := by
    rw [hz, ea]; push_cast; simp only [map_add, map_mul, map_intCast]
  have hzb : D.host.φ₀ (D.host.conj ((((m : 𝓞 D.host.K) + (n : 𝓞 D.host.K) * ωK : 𝓞 D.host.K) : D.host.K) : D.host.E)) =
      starRingEnd ℂ z := Formalism.BasicNotions.Examples₂.emb_conj D.host D.host.φ₀ _
  have hpair : ∃ m' n' : ℤ, z = (m' : ℂ) + (n' : ℂ) * ω ∧ starRingEnd ℂ z = (m' : ℂ) + (n' : ℂ) * (1 - ω) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hx2.trans hom.symm) with h | h
    · have e : D.host.φ₀ ((ωK : D.host.K) : D.host.E) = ω := by rw [hωφ, h]; ring
      refine ⟨m, n, by rw [hzv, e], ?_⟩
      rw [hzv, e, map_add, map_mul, map_intCast, map_intCast, hconjω]
    · have e : D.host.φ₀ ((ωK : D.host.K) : D.host.E) = 1 - ω := by rw [hωφ, h]; ring
      refine ⟨m + n, -n, by rw [hzv, e]; push_cast; ring, ?_⟩
      rw [hzv, e, map_add, map_mul, map_intCast, map_intCast, map_sub, map_one, hconjω]; push_cast; ring
  obtain ⟨m', n', hz1, hz2⟩ := hpair
  have hcτ : tauK D g.lam ((((m : 𝓞 D.host.K) + (n : 𝓞 D.host.K) * ωK : 𝓞 D.host.K) : D.host.K)) = ι z :=
    (Formalism.L2.KerInert.lamCIota p g.lam ι hι).1 _ (Formalism.MainNotions.Ext.test_vector_mem_schwartz_bruhat D _)
  have hcbτ : tauKc D g.lam ((((m : 𝓞 D.host.K) + (n : 𝓞 D.host.K) * ωK : 𝓞 D.host.K) : D.host.K)) =
      ι (starRingEnd ℂ z) := by
    unfold tauKc
    rw [← hzb]
    exact (Formalism.L2.KerInert.lamCIota p g.lam ι hι).1 _ (Formalism.MainNotions.Ext.test_vector_mem_schwartz_bruhat D _)
  rw [hcτ, hcbτ]
  set k : ℕ := (D.host.d + 1) / 4 with hk
  have hq := ReciprocityTheory.ChartRestriction.L1.omegaK_quad D.host.d hd4
  have hN : ι z * ι (starRingEnd ℂ z) = (((m' ^ 2 + m' * n' + n' ^ 2 * (k : ℤ) : ℤ)) : ℂ_[p]) := by
    rw [← map_mul, hz2, hz1, ← map_intCast ι]
    congr 1
    push_cast
    linear_combination (-(n' : ℂ) ^ 2) * hq
  have hmem : (ι z, ι (starRingEnd ℂ z)) ∈ Formalism.L2.Th1.Top.pairsK D.host.d p ι := by
    refine subset_closure ⟨(m', n'), ?_⟩
    show (ι ((m' : ℂ) + (n' : ℂ) * ω), ι ((m' : ℂ) + (n' : ℂ) * (1 - ω))) = (ι z, ι (starRingEnd ℂ z))
    rw [hz2, hz1]
  obtain ⟨-, -, hpairs, -⟩ := Formalism.L2.Th1.Top.calcP D.host.d L hd4 hcmby p h5 ι hIC
  obtain ⟨hE0, hPN0, -⟩ := hpairs _ _ hmem
  have hT := phNormAt_varChange W0 hcoef0 g.C hu.le hui.le hr hs ht (ι (Formalism.L2.Th1.F.s2 L)) _ _ _ hN hE0 hPN0
  rw [← hgW] at hT

  have hser : sgSer g.lam g.abelian₂ = Formalism.L2.Th1.B.sgStar (g.lam s0) (Formalism.L2.Th1.F.pOf (g.lam a2) (g.lam a3)) := by
    rw [hLg]; exact Formalism.L2.KerInert.Sigma.sgSer_eq g.lam L a2 a3 s0 rfl rfl rfl
  have hwp : Formalism.L2.Th1.A.wpReg g.W =
      PowerSeries.C (ε ^ 2) * PowerSeries.rescale ε (Formalism.L2.Th1.F.pOf (g.lam a2) (g.lam a3)) := by
    rw [Formalism.L2.KerInert.Sigma.wpReg_eq, c2, c3]
    exact (Formalism.L2.Th1.F.seriesScale ℂ_[p] (g.lam a2) (g.lam a3) ε).2.2.2.1
  have hR : PowerSeries.rescale ε (sgSer g.lam g.abelian₂) =
      PowerSeries.C ε * Formalism.L2.Th1.B.sgW g.W (ε ^ 2 * ι (Formalism.L2.Th1.F.s2 L)) := by
    unfold Formalism.L2.Th1.B.sgW
    rw [hser, hwp, hιs]
    exact ((Formalism.L2.Th1.F.sigmaScale ℂ_[p] (Formalism.L2.Th1.F.pOf (g.lam a2) (g.lam a3)) (g.lam s0) ε).2).symm
  have hph : g.ph = Formalism.L2.Th1.B.phW g.W (ε ^ 2 * ι (Formalism.L2.Th1.F.s2 L)) :=
    Formalism.L2.KerInert.Dict.formal_phase_agree p g _ hOk hR

  have hX : (g.phAt (Xv ()) : MvPowerSeries Unit ℂ_[p]) = g.ph := PowerSeries.X_subst g.ph
  have hM : (g.phAt (g.mulBy (ι z) (Xv ())) : MvPowerSeries Unit ℂ_[p]) =
      PowerSeries.subst (Formalism.L2.Th1.C.mulBy (Formalism.L2.Th1.A.logSer g.W) (Formalism.L2.Th1.A.expSer g.W) (ι z)) g.ph := by
    unfold G1.phAt; rw [mulBy_g g hOk]
  rw [hM, hX, hph]
  have hsm : (MvPowerSeries.C (ι z * ι (starRingEnd ℂ z)) *
      Formalism.L2.Th1.B.phW g.W (ε ^ 2 * ι (Formalism.L2.Th1.F.s2 L)) : MvPowerSeries Unit ℂ_[p]) =
      ((ι z * ι (starRingEnd ℂ z)) • Formalism.L2.Th1.B.phW g.W (ε ^ 2 * ι (Formalism.L2.Th1.F.s2 L)) : ℂ_[p]⟦X⟧) := by
    rw [PowerSeries.smul_eq_C_mul]; rfl
  rw [hsm]
  obtain ⟨h0, h1⟩ := hT
  refine ⟨h0, ?_⟩
  rw [Formalism.L2.KerInert.Dict.expMv_eq_mvExp h0]
  intro e
  exact h1 e

end Main

end Formalism.L2.KerInert.PN

namespace Formalism.L2.KerInert

/- English proof (translation)
The claim follows from `PN.phNormOKInert_of`.
-/
theorem phi_norm_inert_prime : PhNormOKInert := PN.phNormOKInert_of

end Formalism.L2.KerInert
