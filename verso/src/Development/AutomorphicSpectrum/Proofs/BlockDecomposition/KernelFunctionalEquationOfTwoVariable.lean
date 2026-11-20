import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOfTrivialInteger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRightTranslation

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.R
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.RSKernel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

def mt (r₁ r₃ : Fin 2 → F) : Matrix (Fin 2) (Fin 2) F := !![r₁ 0, r₃ 0; r₁ 1, r₃ 1]

def sw (D : F) : Matrix (Fin 2) (Fin 2) F := !![0, D; -D, 0]

/- English proof (translation)
Simplify using `[mt, det_fin_two, dt]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mt_det (r₁ r₃ : Fin 2 → F) : (mt r₁ r₃).det = dt r₁ r₃ := by
  simp [mt, det_fin_two, dt]; ring

/- English proof (translation)
Simplify using `[sw, det_fin_two]`.
-/
theorem sw_det (D : F) : (sw D).det = D * D := by
  simp [sw, det_fin_two]

/- English proof (translation)
Simplify using `[sw, mulVec, dotProduct, Fin.sum_univ_two]`.
-/
theorem sw_zero (D : F) (v : Fin 2 → F) : (sw D *ᵥ v) 0 = D * v 1 := by
  simp [sw, mulVec, dotProduct, Fin.sum_univ_two]

/- English proof (translation)
Simplify using `[sw, mulVec, dotProduct, Fin.sum_univ_two]`.
-/
theorem sw_one (D : F) (v : Fin 2 → F) : (sw D *ᵥ v) 1 = -D * v 0 := by
  simp [sw, mulVec, dotProduct, Fin.sum_univ_two]

/- English proof (translation)
Rewrite using `[sw_zero]`. Simplify using `[mt, mulVec, dotProduct, Fin.sum_univ_two, dt]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dt_left (r₁ r₃ v : Fin 2 → F) : dt r₁ (mt r₁ r₃ *ᵥ v) = (sw (dt r₁ r₃) *ᵥ v) 0 := by
  rw [sw_zero]
  simp [mt, mulVec, dotProduct, Fin.sum_univ_two, dt]; ring

/- English proof (translation)
Rewrite using `[sw_one]`. Simplify using `[mt, mulVec, dotProduct, Fin.sum_univ_two, dt]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dt_right (r₁ r₃ v : Fin 2 → F) : dt r₃ (mt r₁ r₃ *ᵥ v) = (sw (dt r₁ r₃) *ᵥ v) 1 := by
  rw [sw_one]
  simp [mt, mulVec, dotProduct, Fin.sum_univ_two, dt]; ring

/- English proof (translation)
Rewrite using `[sw_zero, sw_one]`. Simplify using `[mt, mulVec, dotProduct, Fin.sum_univ_two, dt]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dt_both (r₁ r₃ v' v : Fin 2 → F) : dt (mt r₁ r₃ *ᵥ v') (mt r₁ r₃ *ᵥ v) =
    v' 0 * (sw (dt r₁ r₃) *ᵥ v) 0 + v' 1 * (sw (dt r₁ r₃) *ᵥ v) 1 := by
  rw [sw_zero, sw_one]
  simp [mt, mulVec, dotProduct, Fin.sum_univ_two, dt]; ring

/- English proof (translation)
Simplify using `[chF]`.
-/
theorem chF_zero (c : Fˣ →* ℂˣ) (s : ℂ) : chF c s (0 : F) = 0 := by
  simp [chF]

/- English proof (translation)
Simplify using `[chF]`.
-/
theorem chF_unit (c : Fˣ →* ℂˣ) (s : ℂ) (u : Fˣ) : chF c s (u : F) = ((c u : ℂˣ) : ℂ) * mp u s := by
  simp [chF]

/- English proof (translation)
Distinguish the cases in `ha : a = 0`. Simplify using `[chF, ha]`. Distinguish the cases in `hb : b = 0`. Simplify using `[chF, hb]`. Establish `h : a * b = ((Units.mk0 a ha * Units.mk0 b hb : Fˣ) : F)` using `rfl`.

Establish `ha' : a = ((Units.mk0 a ha : Fˣ) : F)` using `rfl`. Establish `hb' : b = ((Units.mk0 b hb : Fˣ) : F)` using `rfl`. Rewrite using `[h, chF_unit]`. Use `conv_rhs => rw [ha', hb', chF_unit, chF_unit]`. Rewrite using `[map_mul, Units.val_mul, GlobalTheory.CompanionTheory.WhittakerTrans.mp_mul']`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem chF_mul (c : Fˣ →* ℂˣ) (s : ℂ) (a b : F) : chF c s (a * b) = chF c s a * chF c s b := by
  by_cases ha : a = 0
  · simp [chF, ha]
  by_cases hb : b = 0
  · simp [chF, hb]
  have h : a * b = ((Units.mk0 a ha * Units.mk0 b hb : Fˣ) : F) := rfl
  have ha' : a = ((Units.mk0 a ha : Fˣ) : F) := rfl
  have hb' : b = ((Units.mk0 b hb : Fˣ) : F) := rfl
  rw [h, chF_unit]
  conv_rhs => rw [ha', hb', chF_unit, chF_unit]
  rw [map_mul, Units.val_mul, GlobalTheory.CompanionTheory.WhittakerTrans.mp_mul']
  ring

/- English proof (translation)
Simplify using `[mp, modulus_neg_eq]`.
-/
theorem mp_neg_one (s : ℂ) : mp (-1 : Fˣ) s = 1 := by
  simp [mp, modulus_neg_eq]

/- English proof (translation)
Establish `h : -x = ((-1 : Fˣ) : F) * x` using `by simp`. Rewrite using `[h, chF_mul, chF_unit, mp_neg_one, mul_one]`.
-/
theorem chF_neg (c : Fˣ →* ℂˣ) (s : ℂ) (x : F) : chF c s (-x) = ((c (-1) : ℂˣ) : ℂ) * chF c s x := by
  have h : -x = ((-1 : Fˣ) : F) * x := by simp
  rw [h, chF_mul, chF_unit, mp_neg_one, mul_one]

/- English proof (translation)
Establish `h : ((modulus (u : F) : ℝ) : ℂ) ≠ 0`. Conclude with `modulus_ne_zero u.ne_zero` after adjusting the coercions. Conclude with `Complex.cpow_add _ _ h`.
-/
theorem mp_add (u : Fˣ) (a b : ℂ) : mp u (a + b) = mp u a * mp u b := by
  have h : ((modulus (u : F) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast modulus_ne_zero u.ne_zero
  exact Complex.cpow_add _ _ h

/- English proof (translation)
Simplify using `only [chF_unit]`. Establish `e : (((ν * c) u : ℂˣ) : ℂ) * (((ν⁻¹ * c) u : ℂˣ) : ℂ) * ((c⁻¹ u : ℂˣ) : ℂ) = ((c u : ℂˣ) : ℂ)`. Rewrite using `[← Units.val_mul, ← Units.val_mul]`. Use `congr 1`. Simplify using `only [MonoidHom.mul_apply, MonoidHom.inv_apply]`.

Rewrite using `[mul_mul_mul_comm, mul_inv_cancel, one_mul, mul_inv_cancel_right]`. Establish `e2 : ((modulus (u : F) : ℝ) : ℂ) * mp u (s - 1) * mp u (-s) = 1`. Establish `h1 : mp u 1 = ((modulus (u : F) : ℝ) : ℂ)` using `by simp [mp]`. Rewrite using `[← h1, ← mp_add, ← mp_add]`. Establish `: (1 + (s - 1) + -s : ℂ) = 0` using `by ring`.

Rewrite using `[this]`. Simplify using `[mp]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem const_eq (ν c : Fˣ →* ℂˣ) (s : ℂ) (u : Fˣ) :
    ((modulus (u : F) : ℝ) : ℂ) * (chF (ν * c) (s - 1) (u : F) * chF (ν⁻¹ * c) (s - 1) (u : F) *
      chF c⁻¹ (-s) (u : F)) = chF c (s - 1) (u : F) := by
  simp only [chF_unit]
  have e : (((ν * c) u : ℂˣ) : ℂ) * (((ν⁻¹ * c) u : ℂˣ) : ℂ) * ((c⁻¹ u : ℂˣ) : ℂ) = ((c u : ℂˣ) : ℂ) := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
    rw [mul_mul_mul_comm, mul_inv_cancel, one_mul, mul_inv_cancel_right]
  have e2 : ((modulus (u : F) : ℝ) : ℂ) * mp u (s - 1) * mp u (-s) = 1 := by
    have h1 : mp u 1 = ((modulus (u : F) : ℝ) : ℂ) := by simp [mp]
    rw [← h1, ← mp_add, ← mp_add]
    have : (1 + (s - 1) + -s : ℂ) = 0 := by ring
    rw [this]
    simp [mp]
  calc _ = ((((ν * c) u : ℂˣ) : ℂ) * (((ν⁻¹ * c) u : ℂˣ) : ℂ) * ((c⁻¹ u : ℂˣ) : ℂ)) *
        (((modulus (u : F) : ℝ) : ℂ) * mp u (s - 1) * mp u (-s)) * mp u (s - 1) := by ring
    _ = _ := by rw [e, e2, mul_one]

/- English proof (translation)
Rewrite using `[← Units.val_mul]`. Establish `h : (c (-1)) * (c (-1)) = 1` using `by rw [← map_mul]; simp`. Establish `: (ν * c) (-1) * (ν⁻¹ * c) (-1) = 1`. Simplify using `only [MonoidHom.mul_apply, MonoidHom.inv_apply]`. Rewrite using `[mul_mul_mul_comm, mul_inv_cancel, one_mul, h]`.

Rewrite using `[this, Units.val_one]`.
-/
theorem sign_eq (ν c : Fˣ →* ℂˣ) :
    (((ν * c) (-1) : ℂˣ) : ℂ) * (((ν⁻¹ * c) (-1) : ℂˣ) : ℂ) = 1 := by
  rw [← Units.val_mul]
  have h : (c (-1)) * (c (-1)) = 1 := by rw [← map_mul]; simp
  have : (ν * c) (-1) * (ν⁻¹ * c) (-1) = 1 := by
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
    rw [mul_mul_mul_comm, mul_inv_cancel, one_mul, h]
  rw [this, Units.val_one]

/- English proof (translation)
Assemble the required witnesses or components as `⟨h₁.1.mul h₂.1, fun x => by simp [h₁.2, h₂.2]⟩`.
-/
theorem isUnit1_mul {μ ν : Fˣ →* ℂˣ} (h₁ : IsUnit1 μ) (h₂ : IsUnit1 ν) : IsUnit1 (μ * ν) :=
  ⟨h₁.1.mul h₂.1, fun x => by simp [h₁.2, h₂.2]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1.inv, fun x => by simp [h.2]⟩`.
-/
theorem isUnit1_inv {μ : Fˣ →* ℂˣ} (h : IsUnit1 μ) : IsUnit1 μ⁻¹ :=
  ⟨h.1.inv, fun x => by simp [h.2]⟩

/- English proof (translation)
Establish `e1 : (ν⁻¹ * c)⁻¹ = ν * c⁻¹` using `by rw [mul_inv, inv_inv]`. Establish `e2 : (ν * c)⁻¹ = ν⁻¹ * c⁻¹` using `mul_inv ν c`. Establish `e3 : (1 - s - 1 : ℂ) = -s` using `by ring`. Establish `e4 : (-(1 - s) : ℂ) = s - 1` using `by ring`. Simplify using `only [Kr, dt_left, dt_right, e1, e2, e3, e4, inv_inv]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem kr_left (ν c : Fˣ →* ℂˣ) (s : ℂ) (r₁ r₃ v : Fin 2 → F) :
    Kr ν c⁻¹ (1 - s) r₁ (mt r₁ r₃ *ᵥ v) r₃ = chF c (s - 1) (dt r₁ r₃) *
      (chF (ν⁻¹ * c)⁻¹ (-s) ((sw (dt r₁ r₃) *ᵥ v) 0) * chF (ν * c)⁻¹ (-s) ((sw (dt r₁ r₃) *ᵥ v) 1)) := by
  have e1 : (ν⁻¹ * c)⁻¹ = ν * c⁻¹ := by rw [mul_inv, inv_inv]
  have e2 : (ν * c)⁻¹ = ν⁻¹ * c⁻¹ := mul_inv ν c
  have e3 : (1 - s - 1 : ℂ) = -s := by ring
  have e4 : (-(1 - s) : ℂ) = s - 1 := by ring
  simp only [Kr, dt_left, dt_right, e1, e2, e3, e4, inv_inv]
  ring

/- English proof (translation)
Simplify using `only [Kr, dt_left, dt_right, sw_zero, sw_one, chF_mul, neg_mul, chF_neg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem kr_right (ν c : Fˣ →* ℂˣ) (s : ℂ) (r₁ r₃ v : Fin 2 → F) :
    Kr ν c s r₁ (mt r₁ r₃ *ᵥ v) r₃ = (((ν⁻¹ * c) (-1) : ℂˣ) : ℂ) *
      (chF (ν * c) (s - 1) (dt r₁ r₃) * chF (ν⁻¹ * c) (s - 1) (dt r₁ r₃) * chF c⁻¹ (-s) (dt r₁ r₃)) *
      (chF (ν⁻¹ * c) (s - 1) (v 0) * chF (ν * c) (s - 1) (v 1)) := by
  simp only [Kr, dt_left, dt_right, sw_zero, sw_one, chF_mul, neg_mul, chF_neg]
  ring

variable [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Use `set g := GeneralLinearGroup.mkOfDetNeZero M hM with hg`. Establish `hgM : (g : Matrix (Fin 2) (Fin 2) F) = M` using `rfl`. Establish `h` using `GlobalTheory.CompanionTheory.JSBound.setIntegral_image_mulVec (selfDualMeasure ψ) g Set.univ f`. Establish `hs : (fun x => (g : Matrix (Fin 2) (Fin 2) F) *ᵥ x) '' Set.univ = Set.univ`. Use `Set.eq_univ_of_forall fun y => ⟨((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ y, trivial, ?_⟩` and prove the remaining obligations.

Simplify using `only [Matrix.mulVec_mulVec]`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Rewrite `h` using `[hs, Measure.restrict_univ, hgM]`. Establish `hu : Measures.modulus M.det = modulus M.det`. Use `Measures.modulus_units (Units.mk0 M.det hM)` as an intermediate fact.

Rewrite `this` using `[distribHaarChar_eq_modulus]`. Conclude with `this`. Rewrite `h` using `[hu]`. Conclude with `h`.
-/
theorem integral_eq_mulVec (ψ : AddChar F Circle) (M : Matrix (Fin 2) (Fin 2) F) (hM : M.det ≠ 0)
    (f : (Fin 2 → F) → ℂ) :
    ∫ x, f x ∂m2 ψ = ((modulus M.det : ℝ) : ℂ) * ∫ x, f (M *ᵥ x) ∂m2 ψ := by
  set g := GeneralLinearGroup.mkOfDetNeZero M hM with hg
  have hgM : (g : Matrix (Fin 2) (Fin 2) F) = M := rfl
  have h := GlobalTheory.CompanionTheory.JSBound.setIntegral_image_mulVec (selfDualMeasure ψ) g Set.univ f
  have hs : (fun x => (g : Matrix (Fin 2) (Fin 2) F) *ᵥ x) '' Set.univ = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ⟨((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ y, trivial, ?_⟩
    simp only [Matrix.mulVec_mulVec]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  rw [hs, Measure.restrict_univ, hgM] at h
  have hu : Measures.modulus M.det = modulus M.det := by
    have := Measures.modulus_units (Units.mk0 M.det hM)
    rw [distribHaarChar_eq_modulus] at this
    exact this
  rw [hu] at h
  exact h

/- English proof (translation)
Establish `hM : (mt r₁ r₃).det ≠ 0` using `by rwa [mt_det]`. Rewrite using `[sF, integral_eq_mulVec ψ _ hM, mt_det]`. Simplify using `only [dt_both]`.
-/
theorem sF_comp (ψ : AddChar F Circle) (Ψ : (Fin 2 → F) → ℂ) (r₁ r₃ v : Fin 2 → F)
    (hD : dt r₁ r₃ ≠ 0) :
    sF ψ Ψ (mt r₁ r₃ *ᵥ v) = ((modulus (dt r₁ r₃) : ℝ) : ℂ) *
      ∫ r', Ψ (mt r₁ r₃ *ᵥ r') * (ψ (r' 0 * (sw (dt r₁ r₃) *ᵥ v) 0 + r' 1 * (sw (dt r₁ r₃) *ᵥ v) 1) : ℂ) ∂m2 ψ := by
  have hM : (mt r₁ r₃).det ≠ 0 := by rwa [mt_det]
  rw [sF, integral_eq_mulVec ψ _ hM, mt_det]
  simp only [dt_both]

/- English proof (translation)
Introduce `hA F _ _ _ _ _ _ ψ hψ ν c hν hc Ψ hΨ s hs r₁ r₃`. Distinguish the cases in `hD : dt r₁ r₃ = 0`. Simplify using `only [Kr, hD, chF_zero, mul_zero, integral_zero]`. Establish `hM : (mt r₁ r₃).det ≠ 0` using `by rwa [mt_det]`. Establish `hS : (sw (dt r₁ r₃)).det ≠ 0` using `by rw [sw_det]; exact mul_ne_zero hD hD`.

Establish `hf : SB (fun v => Ψ (mt r₁ r₃ *ᵥ v))`. Establish `hT : (mt r₁ r₃)ᵀ.det ≠ 0` using `by rwa [det_transpose]`. Establish `h` using `GlobalTheory.CompanionTheory.WhittakerTrans.rt_mem hΨ (GeneralLinearGroup.mkOfDetNeZero _ hT)`. Establish `e : (fun v => Ψ (mt r₁ r₃ *ᵥ v)) = Ad3.SchwartzSpaceL2.rt Ψ (GeneralLinearGroup.mkOfDetNeZero _ hT)`. Use function extensionality and compare the values at `v`.

Use `show _ = Ψ (v ᵥ* (mt r₁ r₃)ᵀ)`. Rewrite using `[vecMul_transpose]`. Rewrite using `[e]`. Conclude with `h`. Establish `h1 : IsUnit1 (ν⁻¹ * c)` using `isUnit1_mul (isUnit1_inv hν) hc`.

Establish `h2 : IsUnit1 (ν * c)` using `isUnit1_mul hν hc`. Establish `h7 : ∫ r, (∫ r', Ψ (mt r₁ r₃ *ᵥ r') * (ψ (r' 0 * r 0 + r' 1 * r 1) : ℂ) ∂m2 ψ) * (chF (ν⁻¹ * c)⁻¹ (-s) (r 0) * chF (ν * c)⁻¹ (-s) (r 1)) ∂m2 ψ = gam ψ (ν⁻¹ * c) s * gam ψ (ν * c) s * ∫ r, Ψ (mt r₁ r₃ *ᵥ r) * (chF (ν⁻¹ * c) (s - 1) (r 0) * chF (ν * c) (s - 1) (r 1)) ∂m2 ψ` using `hA F ψ hψ (ν⁻¹ * c) (ν * c) h1 h2 _ hf s hs`. Establish `hSm : ((modulus (sw (dt r₁ r₃)).det : ℝ) : ℂ) = ((modulus (dt r₁ r₃) : ℝ) : ℂ) * ((modulus (dt r₁ r₃) : ℝ) : ℂ)`. Rewrite using `[sw_det, modulus_mul]`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite `h7` using `[integral_eq_mulVec ψ _ hS, hSm]`. Rewrite using `[integral_eq_mulVec ψ _ hM, integral_eq_mulVec ψ (f := fun r => Ψ r * Kr ν c s r₁ r r₃) _ hM, mt_det]`. Simplify using `only [sF_comp ψ Ψ r₁ r₃ _ hD, kr_left]`. Simplify using `only [kr_right]`.

Establish `hK` using `const_eq ν c s (Units.mk0 _ hD)`. Simplify using `only [Units.val_mk0] at hK`. Establish `hτ` using `sign_eq ν c`. Generalize the expression as in `((modulus (dt r₁ r₃) : ℝ) : ℂ) = A at h7 hK ⊢`. Generalize the expression as in `chF c (s - 1) (dt r₁ r₃) = C at hK ⊢`.

Generalize the expression as in `chF (ν * c) (s - 1) (dt r₁ r₃) * chF (ν⁻¹ * c) (s - 1) (dt r₁ r₃) * chF c⁻¹ (-s) (dt r₁ r₃) = K at hK ⊢`. Generalize the expression as in `(((ν * c) (-1) : ℂˣ) : ℂ) = τ at hτ ⊢`. Generalize the expression as in `(((ν⁻¹ * c) (-1) : ℂˣ) : ℂ) = σ at hτ ⊢`. Establish `eL : ∀ (J P : (Fin 2 → F) → ℂ), ∫ v, A * J v * (C * P v) ∂m2 ψ = A * C * ∫ v, J v * P v ∂m2 ψ`. Introduce `J P`.

Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `v`. Expand and normalize the polynomial expressions, which then agree. Establish `eR : ∀ (J P : (Fin 2 → F) → ℂ), ∫ v, J v * (σ * K * P v) ∂m2 ψ = σ * K * ∫ v, J v * P v ∂m2 ψ`.

Introduce `J P`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `v`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[eL (fun v => ∫ r', Ψ (mt r₁ r₃ *ᵥ r') * (ψ (r' 0 * (sw (dt r₁ r₃) *ᵥ v) 0 + r' 1 * (sw (dt r₁ r₃) *ᵥ v) 1) : ℂ) ∂m2 ψ) (fun v => chF (ν⁻¹ * c)⁻¹ (-s) ((sw (dt r₁ r₃) *ᵥ v) 0) * chF (ν * c)⁻¹ (-s) ((sw (dt r₁ r₃) *ᵥ v) 1)), eR (fun v => Ψ (mt r₁ r₃ *ᵥ v)) (fun v => chF (ν⁻¹ * c) …`. Generalize the expression as in `(∫ v, (∫ r', Ψ (mt r₁ r₃ *ᵥ r') * (ψ (r' 0 * (sw (dt r₁ r₃) *ᵥ v) 0 + r' 1 * (sw (dt r₁ r₃) *ᵥ v) 1) : ℂ) ∂m2 ψ) * (chF (ν⁻¹ * c)⁻¹ (-s) ((sw (dt r₁ r₃) *ᵥ v) 0) * chF (ν * c)⁻¹ (-s) ((sw (dt r₁ r₃) *ᵥ v) 1)) ∂m2 ψ) = X at h7 ⊢`. Generalize the expression as in `(∫ v, Ψ (mt r₁ r₃ *ᵥ v) * (chF (ν⁻¹ * c) (s - 1) (v 0) * chF (ν * c) (s - 1) (v 1)) ∂m2 ψ) = I at h7 ⊢`. Generalize the expression as in `gam ψ (ν⁻¹ * c) s = g₁ at h7 ⊢`. Generalize the expression as in `gam ψ (ν * c) s = g₂ at h7 ⊢`.

Take the linear combination `C * h7 - g₁ * g₂ * I * τ * σ * hK - g₁ * g₂ * I * C * hτ`.
-/
theorem kernel_local_functional_equation : A7 → A8 := by
  intro hA F _ _ _ _ _ _ ψ hψ ν c hν hc Ψ hΨ s hs r₁ r₃
  by_cases hD : dt r₁ r₃ = 0
  · simp only [Kr, hD, chF_zero, mul_zero, integral_zero]
  have hM : (mt r₁ r₃).det ≠ 0 := by rwa [mt_det]
  have hS : (sw (dt r₁ r₃)).det ≠ 0 := by rw [sw_det]; exact mul_ne_zero hD hD
  have hf : SB (fun v => Ψ (mt r₁ r₃ *ᵥ v)) := by
    have hT : (mt r₁ r₃)ᵀ.det ≠ 0 := by rwa [det_transpose]
    have h := GlobalTheory.CompanionTheory.WhittakerTrans.rt_mem hΨ (GeneralLinearGroup.mkOfDetNeZero _ hT)
    have e : (fun v => Ψ (mt r₁ r₃ *ᵥ v)) = Ad3.SchwartzSpaceL2.rt Ψ (GeneralLinearGroup.mkOfDetNeZero _ hT) := by
      funext v
      show _ = Ψ (v ᵥ* (mt r₁ r₃)ᵀ)
      rw [vecMul_transpose]
    rw [e]
    exact h
  have h1 : IsUnit1 (ν⁻¹ * c) := isUnit1_mul (isUnit1_inv hν) hc
  have h2 : IsUnit1 (ν * c) := isUnit1_mul hν hc
  have h7 : ∫ r, (∫ r', Ψ (mt r₁ r₃ *ᵥ r') * (ψ (r' 0 * r 0 + r' 1 * r 1) : ℂ) ∂m2 ψ) *
        (chF (ν⁻¹ * c)⁻¹ (-s) (r 0) * chF (ν * c)⁻¹ (-s) (r 1)) ∂m2 ψ =
      gam ψ (ν⁻¹ * c) s * gam ψ (ν * c) s * ∫ r, Ψ (mt r₁ r₃ *ᵥ r) *
        (chF (ν⁻¹ * c) (s - 1) (r 0) * chF (ν * c) (s - 1) (r 1)) ∂m2 ψ :=
    hA F ψ hψ (ν⁻¹ * c) (ν * c) h1 h2 _ hf s hs
  have hSm : ((modulus (sw (dt r₁ r₃)).det : ℝ) : ℂ) =
      ((modulus (dt r₁ r₃) : ℝ) : ℂ) * ((modulus (dt r₁ r₃) : ℝ) : ℂ) := by
    rw [sw_det, modulus_mul]
    push_cast
    rfl
  rw [integral_eq_mulVec ψ _ hS, hSm] at h7
  rw [integral_eq_mulVec ψ _ hM, integral_eq_mulVec ψ (f := fun r => Ψ r * Kr ν c s r₁ r r₃) _ hM, mt_det]
  simp only [sF_comp ψ Ψ r₁ r₃ _ hD, kr_left]
  simp only [kr_right]
  have hK := const_eq ν c s (Units.mk0 _ hD)
  simp only [Units.val_mk0] at hK
  have hτ := sign_eq ν c
  generalize ((modulus (dt r₁ r₃) : ℝ) : ℂ) = A at h7 hK ⊢
  generalize chF c (s - 1) (dt r₁ r₃) = C at hK ⊢
  generalize chF (ν * c) (s - 1) (dt r₁ r₃) * chF (ν⁻¹ * c) (s - 1) (dt r₁ r₃) *
    chF c⁻¹ (-s) (dt r₁ r₃) = K at hK ⊢
  generalize (((ν * c) (-1) : ℂˣ) : ℂ) = τ at hτ ⊢
  generalize (((ν⁻¹ * c) (-1) : ℂˣ) : ℂ) = σ at hτ ⊢
  have eL : ∀ (J P : (Fin 2 → F) → ℂ), ∫ v, A * J v * (C * P v) ∂m2 ψ = A * C * ∫ v, J v * P v ∂m2 ψ := by
    intro J P
    rw [← integral_const_mul]
    congr 1
    funext v
    ring
  have eR : ∀ (J P : (Fin 2 → F) → ℂ), ∫ v, J v * (σ * K * P v) ∂m2 ψ = σ * K * ∫ v, J v * P v ∂m2 ψ := by
    intro J P
    rw [← integral_const_mul]
    congr 1
    funext v
    ring
  rw [eL (fun v => ∫ r', Ψ (mt r₁ r₃ *ᵥ r') *
      (ψ (r' 0 * (sw (dt r₁ r₃) *ᵥ v) 0 + r' 1 * (sw (dt r₁ r₃) *ᵥ v) 1) : ℂ) ∂m2 ψ)
      (fun v => chF (ν⁻¹ * c)⁻¹ (-s) ((sw (dt r₁ r₃) *ᵥ v) 0) * chF (ν * c)⁻¹ (-s) ((sw (dt r₁ r₃) *ᵥ v) 1)),
    eR (fun v => Ψ (mt r₁ r₃ *ᵥ v))
      (fun v => chF (ν⁻¹ * c) (s - 1) (v 0) * chF (ν * c) (s - 1) (v 1))]
  generalize (∫ v, (∫ r', Ψ (mt r₁ r₃ *ᵥ r') *
      (ψ (r' 0 * (sw (dt r₁ r₃) *ᵥ v) 0 + r' 1 * (sw (dt r₁ r₃) *ᵥ v) 1) : ℂ) ∂m2 ψ) *
      (chF (ν⁻¹ * c)⁻¹ (-s) ((sw (dt r₁ r₃) *ᵥ v) 0) * chF (ν * c)⁻¹ (-s) ((sw (dt r₁ r₃) *ᵥ v) 1)) ∂m2 ψ) = X at h7 ⊢
  generalize (∫ v, Ψ (mt r₁ r₃ *ᵥ v) *
      (chF (ν⁻¹ * c) (s - 1) (v 0) * chF (ν * c) (s - 1) (v 1)) ∂m2 ψ) = I at h7 ⊢
  generalize gam ψ (ν⁻¹ * c) s = g₁ at h7 ⊢
  generalize gam ψ (ν * c) s = g₂ at h7 ⊢
  linear_combination C * h7 - g₁ * g₂ * I * τ * σ * hK - g₁ * g₂ * I * C * hτ

end GlobalTheory.CompanionTheory.RSKernel

end
