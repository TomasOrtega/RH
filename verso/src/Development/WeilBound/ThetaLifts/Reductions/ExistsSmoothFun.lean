import Development.WeilBound.ThetaLifts.Reductions.MetaDef

noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E
open scoped Real RealInnerProductSpace FourierTransform

namespace PositivityTheory.ThKR

variable {l : Type} [Fintype l] [DecidableEq l]

/- English proof (translation)
Establish `hsJ : ∀ w w' : l ⊕ l → ℝ, GlobalTheory.RealWeil.sympl w w' = -(w ⬝ᵥ (Matrix.J l ℝ *ᵥ w'))`. Introduce `w w'`. Simplify using `[GlobalTheory.RealWeil.sympl, GlobalTheory.RealWeil.pPart, GlobalTheory.RealWeil.qPart, Matrix.J, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks, PiLp.inner_apply, Matrix.one_apply]`. Simplify using `only [mul_comm]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hent : ∀ (N : Matrix (l ⊕ l) (l ⊕ l) ℝ) i j, N i j = Pi.single i 1 ⬝ᵥ (N *ᵥ Pi.single j 1)`. Introduce `N i j`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Establish `hinv : ∀ t, (LinearMap.toMatrix' (s t))ᵀ * Matrix.J l ℝ * LinearMap.toMatrix' (s t) = Matrix.J l ℝ`. Introduce `t`.

Use extensionality with `i j`. Establish `h` using `ss t (Pi.single i 1) (Pi.single j 1)`. Rewrite `h` using `[hsJ, hsJ, neg_inj, ← LinearMap.toMatrix'_mulVec (s t), ← LinearMap.toMatrix'_mulVec (s t)]`. Rewrite using `[hent ((LinearMap.toMatrix' (s t))ᵀ * Matrix.J l ℝ * LinearMap.toMatrix' (s t)) i j, hent (Matrix.J l ℝ) i j, ← h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]`. Use `letI : NormedAddCommGroup (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAddCommGroup`.

Use `letI : NormedSpace ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedSpace`. Use `letI : NormedRing (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAlgebra`. Set `Φ : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ` to `fun t => LinearMap.toMatrix' (s t)`. Establish `hΦw : ∀ t w, s t w = Φ t *ᵥ w` using `fun t w => (LinearMap.toMatrix'_mulVec (s t) w).symm`.

Establish `hΦc : Continuous Φ`. Apply `continuous_pi` to reduce the goal to its premises. Introduce `i`. Apply `continuous_pi` to reduce the goal to its premises. Introduce `j`.

Simplify using `only [Φ, LinearMap.toMatrix'_apply]`. Conclude with `(continuous_apply i).comp (sc _)`. Establish `hΦ0 : Φ 0 = 1`. Establish `: s 0 = LinearMap.id` using `LinearMap.ext s0`. Simplify using `only [Φ, this, LinearMap.toMatrix'_id]`.

Establish `hΦm : ∀ t u, Φ (t + u) = Φ t * Φ u`. Introduce `t u`. Establish `: s (t + u) = (s t).comp (s u)` using `LinearMap.ext fun w => sm t u w`. Simplify using `only [Φ, this, LinearMap.toMatrix'_comp]`. Use `haveI : CompleteSpace (Matrix (l ⊕ l) (l ⊕ l) ℝ) := FiniteDimensional.complete ℝ _`.

Set `G : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ` to `fun x => ∫ u in (0 : ℝ)..x, Φ u`. Establish `hG : ∀ x, HasDerivAt G (Φ x) x` using `fun x => (hΦc.integral_hasStrictDerivAt 0 x).hasDerivAt`. Establish `hslope : Filter.Tendsto (fun h : ℝ => h⁻¹ • G h) (nhdsWithin 0 {0}ᶜ) (nhds 1)`. Establish `h1` using `(hasDerivAt_iff_tendsto_slope.1 (hG 0))`. Establish `hG0 : G 0 = 0` using `intervalIntegral.integral_same`.

Rewrite `h1` using `[hΦ0]`. Use `h1.congr fun h => ?_` and prove the remaining obligations. Rewrite using `[slope_def_module, hG0, sub_zero, sub_zero]`. Choose the witnesses or unpack the hypotheses as in `⟨h0, hh0, hsmall⟩ : ∃ h0 : ℝ, h0 ≠ 0 ∧ ‖1 - h0⁻¹ • G h0‖ < 1 := by`. Establish `hev : ∀ᶠ h in nhdsWithin (0 : ℝ) {0}ᶜ, ‖1 - h⁻¹ • G h‖ < 1`.

Use `(hslope.const_sub (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ)).norm` as an intermediate fact. Simplify using `only [sub_self, norm_zero] at this`. Conclude with `this.eventually (gt_mem_nhds one_pos)`. Take `⟨h, hh, hm⟩` from `(hev.and self_mem_nhdsWithin).exists`. Conclude with `⟨h, hm, hh⟩`.

Set `u : Matrix (l ⊕ l) (l ⊕ l) ℝ` to `h0⁻¹ • G h0`. Set `U : (Matrix (l ⊕ l) (l ⊕ l) ℝ)ˣ` to `Units.oneSub (1 - u) hsmall`. Establish `hU : (U : Matrix (l ⊕ l) (l ⊕ l) ℝ) = u` using `by simp [U, Units.val_oneSub]`. Set `Binv : Matrix (l ⊕ l) (l ⊕ l) ℝ` to `h0⁻¹ • ((U⁻¹ : (Matrix (l ⊕ l) (l ⊕ l) ℝ)ˣ) : Matrix (l ⊕ l) (l ⊕ l) ℝ)`. Establish `hGB : G h0 * Binv = 1`.

Establish `e : G h0 = h0 • (U : Matrix (l ⊕ l) (l ⊕ l) ℝ)` using `by rw [hU]; simp only [u]; rw [smul_inv_smul₀ hh0]`. Rewrite using `[e, smul_mul_smul_comm, mul_inv_cancel₀ hh0, Units.mul_inv, one_smul]`. Establish `hshift : ∀ t, Φ t * G h0 = G (t + h0) - G t`. Introduce `t`. Establish `e1 : Φ t * G h0 = ∫ x in (0 : ℝ)..h0, Φ t * Φ x`.

Simplify using `using ((ContinuousLinearMap.mul ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) (Φ t)).intervalIntegral_comp_comm (hΦc.intervalIntegrable 0 h0)).symm`. Rewrite using `[e1]`. Repeatedly rewrite using `[← hΦm]`. Rewrite using `[intervalIntegral.integral_comp_add_left (fun x => Φ x) t, add_zero]`. Conclude with `(intervalIntegral.integral_interval_sub_left (hΦc.intervalIntegrable 0 (t + h0)) (hΦc.intervalIntegrable 0 t)).symm`.

Set `A : Matrix (l ⊕ l) (l ⊕ l) ℝ` to `(Φ h0 - 1) * Binv`. Establish `hΦd : ∀ t, HasDerivAt Φ (Φ t * A) t`. Introduce `t`. Establish `hrep : Φ = fun x => (G (x + h0) - G x) * Binv`. Use function extensionality and compare the values at `x`.

Rewrite using `[← hshift x, mul_assoc, hGB, mul_one]`. Establish `hd` using `(((hG (t + h0)).comp_add_const t h0).sub (hG t)).mul_const Binv`. Establish `hval : (Φ (t + h0) - Φ t) * Binv = Φ t * A`. Rewrite using `[hΦm, ← mul_sub_one, mul_assoc]`. Rewrite `hd` using `[hval]`.

Conclude with `hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => congrFun hrep x)`. Establish `hE : ∀ t : ℝ, HasDerivAt (fun x : ℝ => NormedSpace.exp ((-x) • A)) (-(A * NormedSpace.exp ((-t) • A))) t`. Introduce `t`. Establish `h1` using `(hasDerivAt_exp_smul_const' (𝕂 := ℝ) A (-t)).scomp t (hasDerivAt_neg t)`. Apply the tactic sequence `exact h1.congr_deriv (by simp <;> rfl)`.

Establish `hP : ∀ t, Φ t * NormedSpace.exp ((-t) • A) = 1`. Introduce `t`. Establish `hd : ∀ x, HasDerivAt (fun x => Φ x * NormedSpace.exp ((-x) • A)) 0 x`. Introduce `x`. Establish `h1` using `(hΦd x).mul (hE x)`.

Conclude with `h1.congr_deriv (by rw [mul_neg, mul_assoc, add_neg_cancel])`. Establish `hc` using `is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) t 0`. Rewrite using `[hc, hΦ0, neg_zero, zero_smul, NormedSpace.exp_zero, one_mul]`. Use `letI : NormedAlgebra ℚ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := { (inferInstance : Algebra ℚ (Matrix (l ⊕ l) (l ⊕ l) ℝ)) with norm_smul_le := fun q M => by`. Rewrite using `[← Rat.cast_smul_eq_qsmul ℝ q M, norm_smul, Rat.norm_cast_real] }`.

Establish `hΦe : ∀ t, Φ t = NormedSpace.exp (t • A)`. Introduce `t`. Establish `hcomm : Commute ((-t) • A) (t • A)` using `((Commute.refl A).smul_left _).smul_right _`. Establish `h1 : NormedSpace.exp ((-t) • A) * NormedSpace.exp (t • A) = 1`. Establish `h2` using `(NormedSpace.exp_add_of_commute hcomm).symm`.

Rewrite `h2` using `[← add_smul, neg_add_cancel, zero_smul, NormedSpace.exp_zero]`. Conclude with `h2`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1, mul_one]`. Use `_ = NormedSpace.exp (t • A) := by rw [← mul_assoc, hP t, one_mul]`.

Use `⟨A, ?_, fun t w => ?_⟩` and prove the remaining obligations. Rewrite using `[LieAlgebra.Symplectic.sp, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]`. Set `T : Matrix (l ⊕ l) (l ⊕ l) ℝ →L[ℝ] Matrix (l ⊕ l) (l ⊕ l) ℝ` to `LinearMap.toContinuousLinearMap (Matrix.transposeLinearEquiv (l ⊕ l) (l ⊕ l) ℝ ℝ).toLinearMap`. Establish `hT : HasDerivAt (fun t => (Φ t)ᵀ) (T (Φ 0 * A)) 0` using `T.hasFDerivAt.comp_hasDerivAt 0 (hΦd 0)`. Establish `hF` using `(hT.mul_const (Matrix.J l ℝ)).mul (hΦd 0)`.

Establish `hF0 : HasDerivAt (fun t => (Φ t)ᵀ * Matrix.J l ℝ * Φ t) 0 0`. Establish `e : (fun t => (Φ t)ᵀ * Matrix.J l ℝ * Φ t) = fun _ => Matrix.J l ℝ` using `funext hinv`. Rewrite using `[e]`. Conclude with `hasDerivAt_const 0 _`. Establish `huniq` using `hF.unique hF0`.

Simplify using `only [T, hΦ0, one_mul, mul_one] at huniq`. Establish `h2 : Aᵀ * Matrix.J l ℝ + Matrix.J l ℝ * A = 0` using `by simpa using huniq`. Use `show Aᵀ * Matrix.J l ℝ = Matrix.J l ℝ * -A`. Rewrite using `[mul_neg]`. Conclude with `eq_neg_of_add_eq_zero_left h2`.

Rewrite using `[hΦw, hΦe t]`.
-/
theorem exists_sp (s : ℝ → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ))
    (sc : ∀ w, Continuous fun t => s t w) (s0 : ∀ w, s 0 w = w) (sm : ∀ t u w, s (t + u) w = s t (s u w))
    (ss : ∀ t w w', sympl (s t w) (s t w') = sympl w w') :
    ∃ X ∈ LieAlgebra.Symplectic.sp l ℝ, ∀ (t : ℝ) w, s t w = NormedSpace.exp (t • X) *ᵥ w := by
  have hsJ : ∀ w w' : l ⊕ l → ℝ, GlobalTheory.RealWeil.sympl w w' = -(w ⬝ᵥ (Matrix.J l ℝ *ᵥ w')) := by
    intro w w'
    simp [GlobalTheory.RealWeil.sympl, GlobalTheory.RealWeil.pPart, GlobalTheory.RealWeil.qPart, Matrix.J, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Matrix.fromBlocks, PiLp.inner_apply, Matrix.one_apply]
    simp only [mul_comm]
    ring
  have hent : ∀ (N : Matrix (l ⊕ l) (l ⊕ l) ℝ) i j, N i j = Pi.single i 1 ⬝ᵥ (N *ᵥ Pi.single j 1) := by
    intro N i j
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hinv : ∀ t, (LinearMap.toMatrix' (s t))ᵀ * Matrix.J l ℝ * LinearMap.toMatrix' (s t) = Matrix.J l ℝ := by
    intro t
    ext i j
    have h := ss t (Pi.single i 1) (Pi.single j 1)
    rw [hsJ, hsJ, neg_inj, ← LinearMap.toMatrix'_mulVec (s t), ← LinearMap.toMatrix'_mulVec (s t)] at h
    rw [hent ((LinearMap.toMatrix' (s t))ᵀ * Matrix.J l ℝ * LinearMap.toMatrix' (s t)) i j, hent (Matrix.J l ℝ) i j, ← h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
  letI : NormedAddCommGroup (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedSpace
  letI : NormedRing (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAlgebra
  let Φ : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ := fun t => LinearMap.toMatrix' (s t)
  have hΦw : ∀ t w, s t w = Φ t *ᵥ w := fun t w => (LinearMap.toMatrix'_mulVec (s t) w).symm
  have hΦc : Continuous Φ := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simp only [Φ, LinearMap.toMatrix'_apply]
    exact (continuous_apply i).comp (sc _)
  have hΦ0 : Φ 0 = 1 := by
    have : s 0 = LinearMap.id := LinearMap.ext s0
    simp only [Φ, this, LinearMap.toMatrix'_id]
  have hΦm : ∀ t u, Φ (t + u) = Φ t * Φ u := by
    intro t u
    have : s (t + u) = (s t).comp (s u) := LinearMap.ext fun w => sm t u w
    simp only [Φ, this, LinearMap.toMatrix'_comp]
  haveI : CompleteSpace (Matrix (l ⊕ l) (l ⊕ l) ℝ) := FiniteDimensional.complete ℝ _
  let G : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ := fun x => ∫ u in (0 : ℝ)..x, Φ u
  have hG : ∀ x, HasDerivAt G (Φ x) x := fun x => (hΦc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hslope : Filter.Tendsto (fun h : ℝ => h⁻¹ • G h) (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
    have h1 := (hasDerivAt_iff_tendsto_slope.1 (hG 0))
    have hG0 : G 0 = 0 := intervalIntegral.integral_same
    rw [hΦ0] at h1
    refine h1.congr fun h => ?_
    rw [slope_def_module, hG0, sub_zero, sub_zero]
  obtain ⟨h0, hh0, hsmall⟩ : ∃ h0 : ℝ, h0 ≠ 0 ∧ ‖1 - h0⁻¹ • G h0‖ < 1 := by
    have hev : ∀ᶠ h in nhdsWithin (0 : ℝ) {0}ᶜ, ‖1 - h⁻¹ • G h‖ < 1 := by
      have := (hslope.const_sub (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ)).norm
      simp only [sub_self, norm_zero] at this
      exact this.eventually (gt_mem_nhds one_pos)
    obtain ⟨h, hh, hm⟩ := (hev.and self_mem_nhdsWithin).exists
    exact ⟨h, hm, hh⟩
  let u : Matrix (l ⊕ l) (l ⊕ l) ℝ := h0⁻¹ • G h0
  let U : (Matrix (l ⊕ l) (l ⊕ l) ℝ)ˣ := Units.oneSub (1 - u) hsmall
  have hU : (U : Matrix (l ⊕ l) (l ⊕ l) ℝ) = u := by simp [U, Units.val_oneSub]
  let Binv : Matrix (l ⊕ l) (l ⊕ l) ℝ := h0⁻¹ • ((U⁻¹ : (Matrix (l ⊕ l) (l ⊕ l) ℝ)ˣ) : Matrix (l ⊕ l) (l ⊕ l) ℝ)
  have hGB : G h0 * Binv = 1 := by
    have e : G h0 = h0 • (U : Matrix (l ⊕ l) (l ⊕ l) ℝ) := by rw [hU]; simp only [u]; rw [smul_inv_smul₀ hh0]
    rw [e, smul_mul_smul_comm, mul_inv_cancel₀ hh0, Units.mul_inv, one_smul]
  have hshift : ∀ t, Φ t * G h0 = G (t + h0) - G t := by
    intro t
    have e1 : Φ t * G h0 = ∫ x in (0 : ℝ)..h0, Φ t * Φ x := by
      simpa using ((ContinuousLinearMap.mul ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) (Φ t)).intervalIntegral_comp_comm
        (hΦc.intervalIntegrable 0 h0)).symm
    rw [e1]
    simp_rw [← hΦm]
    rw [intervalIntegral.integral_comp_add_left (fun x => Φ x) t, add_zero]
    exact (intervalIntegral.integral_interval_sub_left (hΦc.intervalIntegrable 0 (t + h0))
      (hΦc.intervalIntegrable 0 t)).symm
  let A : Matrix (l ⊕ l) (l ⊕ l) ℝ := (Φ h0 - 1) * Binv
  have hΦd : ∀ t, HasDerivAt Φ (Φ t * A) t := by
    intro t
    have hrep : Φ = fun x => (G (x + h0) - G x) * Binv := by
      funext x
      rw [← hshift x, mul_assoc, hGB, mul_one]
    have hd := (((hG (t + h0)).comp_add_const t h0).sub (hG t)).mul_const Binv
    have hval : (Φ (t + h0) - Φ t) * Binv = Φ t * A := by
      rw [hΦm, ← mul_sub_one, mul_assoc]
    rw [hval] at hd
    exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => congrFun hrep x)
  have hE : ∀ t : ℝ, HasDerivAt (fun x : ℝ => NormedSpace.exp ((-x) • A)) (-(A * NormedSpace.exp ((-t) • A))) t := by
    intro t
    have h1 := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A (-t)).scomp t (hasDerivAt_neg t)
    exact h1.congr_deriv (by simp <;> rfl)
  have hP : ∀ t, Φ t * NormedSpace.exp ((-t) • A) = 1 := by
    intro t
    have hd : ∀ x, HasDerivAt (fun x => Φ x * NormedSpace.exp ((-x) • A)) 0 x := by
      intro x
      have h1 := (hΦd x).mul (hE x)
      exact h1.congr_deriv (by rw [mul_neg, mul_assoc, add_neg_cancel])
    have hc := is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) t 0
    rw [hc, hΦ0, neg_zero, zero_smul, NormedSpace.exp_zero, one_mul]
  letI : NormedAlgebra ℚ (Matrix (l ⊕ l) (l ⊕ l) ℝ) :=
    { (inferInstance : Algebra ℚ (Matrix (l ⊕ l) (l ⊕ l) ℝ)) with
      norm_smul_le := fun q M => by
        rw [← Rat.cast_smul_eq_qsmul ℝ q M, norm_smul, Rat.norm_cast_real] }
  have hΦe : ∀ t, Φ t = NormedSpace.exp (t • A) := by
    intro t
    have hcomm : Commute ((-t) • A) (t • A) := ((Commute.refl A).smul_left _).smul_right _
    have h1 : NormedSpace.exp ((-t) • A) * NormedSpace.exp (t • A) = 1 := by
      have h2 := (NormedSpace.exp_add_of_commute hcomm).symm
      rw [← add_smul, neg_add_cancel, zero_smul, NormedSpace.exp_zero] at h2
      exact h2
    calc Φ t = Φ t * (NormedSpace.exp ((-t) • A) * NormedSpace.exp (t • A)) := by
          rw [h1, mul_one]
      _ = NormedSpace.exp (t • A) := by rw [← mul_assoc, hP t, one_mul]
  refine ⟨A, ?_, fun t w => ?_⟩
  · rw [LieAlgebra.Symplectic.sp, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
    let T : Matrix (l ⊕ l) (l ⊕ l) ℝ →L[ℝ] Matrix (l ⊕ l) (l ⊕ l) ℝ :=
      LinearMap.toContinuousLinearMap (Matrix.transposeLinearEquiv (l ⊕ l) (l ⊕ l) ℝ ℝ).toLinearMap
    have hT : HasDerivAt (fun t => (Φ t)ᵀ) (T (Φ 0 * A)) 0 := T.hasFDerivAt.comp_hasDerivAt 0 (hΦd 0)
    have hF := (hT.mul_const (Matrix.J l ℝ)).mul (hΦd 0)
    have hF0 : HasDerivAt (fun t => (Φ t)ᵀ * Matrix.J l ℝ * Φ t) 0 0 := by
      have e : (fun t => (Φ t)ᵀ * Matrix.J l ℝ * Φ t) = fun _ => Matrix.J l ℝ := funext hinv
      rw [e]
      exact hasDerivAt_const 0 _
    have huniq := hF.unique hF0
    simp only [T, hΦ0, one_mul, mul_one] at huniq
    have h2 : Aᵀ * Matrix.J l ℝ + Matrix.J l ℝ * A = 0 := by simpa using huniq
    show Aᵀ * Matrix.J l ℝ = Matrix.J l ℝ * -A
    rw [mul_neg]
    exact eq_neg_of_add_eq_zero_left h2
  · rw [hΦw, hΦe t]

/- English proof (translation)
Set `lam : Sch l →L[ℂ] ℂ` to `(innerSL ℂ (φ.toLp 2 volume)).comp (schwartzToL2 l)`. Establish `h2 : lam φ ≠ 0` using `fun h => hφ (by`. Apply `injective_toLp 2 volume` to reduce the goal to its premises. Establish `: φ.toLp 2 volume = 0` using `inner_self_eq_zero.1 h`. Conclude with `this.trans (map_zero (schwartzToL2 l)).symm)`.

Establish `hb : ∀ t f, ‖lam (S t f)‖ ≤ ‖φ.toLp 2 volume‖ * ‖schwartzToL2 l f‖` using `fun t f => by`. Use `norm_inner_le_norm (𝕜 := ℂ) (φ.toLp 2 volume) ((S t f).toLp 2 volume)` as an intermediate fact. Rewrite `this` using `[hn]`. Conclude with `this`. Establish `hc` using `Sc φ lam`.

Establish `hI : ∀ t, HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, lam (S s φ)) (lam (S t φ)) t` using `fun t => intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _) (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt`. Choose the witnesses or unpack the hypotheses as in `⟨δ, hδ⟩ : ∃ δ : ℝ, (∫ s in (0 : ℝ)..δ, lam (S s φ)) ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `h3` using `hI 0`.

Simplify using `only [h, S0] at h3`. Conclude with `h2 (h3.unique (hasDerivAt_const _ _))`. Set `m : Sch l →ₗ[ℂ] ℂ` to `{ toFun := fun f => ∫ s in (0 : ℝ)..δ, lam (S s f) map_add' := fun f g => by`. Simplify using `only [map_add]`. Conclude with `intervalIntegral.integral_add ((Sc f lam).intervalIntegrable _ _) ((Sc g lam).intervalIntegrable _ _)`.

Use the proof step `map_smul' := fun a f => by`. Simplify using `only [map_smul, RingHom.id_apply]`. Conclude with `intervalIntegral.integral_smul _ _ }`. Establish `mc : Continuous m`. Use `continuous_of_continuousAt_zero m ?_` and prove the remaining obligations.

Rewrite using `[ContinuousAt, map_zero]`. Establish `h0 : Continuous fun f : Sch l => ‖φ.toLp 2 volume‖ * ‖schwartzToL2 l f‖ * |δ - 0|` using `by fun_prop`. Establish `h1` using `h0.tendsto 0`. Simplify using `only [map_zero, norm_zero, mul_zero, zero_mul] at h1`. Conclude with `squeeze_zero_norm (fun f => intervalIntegral.norm_integral_le_of_norm_le_const fun s _ => hb s f) h1`.

Use `⟨⟨m, mc⟩, hδ, ?_⟩` and prove the remaining obligations. Establish `key : ∀ t, m (S t φ) = (∫ s in (0 : ℝ)..(δ + t), lam (S s φ)) - ∫ s in (0 : ℝ)..t, lam (S s φ)` using `fun t => by`. Rewrite using `[intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]`. Use `intervalIntegral.integral_comp_add_right (fun s => lam (S s φ)) (a := 0) (b := δ) t` as an intermediate fact. Rewrite `this` using `[zero_add]`.

Rewrite using `[← this]`. Simplify using `only [Sm]`. Both sides reduce to the same expression. Use `show DifferentiableAt ℝ (fun t => m (S t φ)) 0`. Simplify using `only [key]`.

Conclude with `(((hI (δ + 0)).comp_const_add δ 0).sub (hI 0)).differentiableAt`.
-/
theorem exists_smooth_fun (S : ℝ → Sch l →ₗ[ℂ] Sch l) (hn : ∀ t f, ‖(S t f).toLp 2 volume‖ = ‖f.toLp 2 volume‖)
    (S0 : ∀ f, S 0 f = f) (Sm : ∀ t u f, S (t + u) f = S t (S u f))
    (Sc : ∀ f (lam : Sch l →L[ℂ] ℂ), Continuous fun t => lam (S t f)) {φ : Sch l} (hφ : φ ≠ 0) :
    ∃ mu : Sch l →L[ℂ] ℂ, mu φ ≠ 0 ∧ DifferentiableAt ℝ (fun t => mu (S t φ)) 0 := by
  let lam : Sch l →L[ℂ] ℂ := (innerSL ℂ (φ.toLp 2 volume)).comp (schwartzToL2 l)
  have h2 : lam φ ≠ 0 := fun h => hφ (by
    apply injective_toLp 2 volume
    have : φ.toLp 2 volume = 0 := inner_self_eq_zero.1 h
    exact this.trans (map_zero (schwartzToL2 l)).symm)
  have hb : ∀ t f, ‖lam (S t f)‖ ≤ ‖φ.toLp 2 volume‖ * ‖schwartzToL2 l f‖ := fun t f => by
    have := norm_inner_le_norm (𝕜 := ℂ) (φ.toLp 2 volume) ((S t f).toLp 2 volume)
    rw [hn] at this
    exact this
  have hc := Sc φ lam
  have hI : ∀ t, HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, lam (S s φ)) (lam (S t φ)) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _) (hc.stronglyMeasurableAtFilter _ _)
      hc.continuousAt
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, (∫ s in (0 : ℝ)..δ, lam (S s φ)) ≠ 0 := by
    by_contra h
    push Not at h
    have h3 := hI 0
    simp only [h, S0] at h3
    exact h2 (h3.unique (hasDerivAt_const _ _))
  let m : Sch l →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ s in (0 : ℝ)..δ, lam (S s f)
      map_add' := fun f g => by
        simp only [map_add]
        exact intervalIntegral.integral_add ((Sc f lam).intervalIntegrable _ _) ((Sc g lam).intervalIntegrable _ _)
      map_smul' := fun a f => by
        simp only [map_smul, RingHom.id_apply]
        exact intervalIntegral.integral_smul _ _ }
  have mc : Continuous m := by
    refine continuous_of_continuousAt_zero m ?_
    rw [ContinuousAt, map_zero]
    have h0 : Continuous fun f : Sch l => ‖φ.toLp 2 volume‖ * ‖schwartzToL2 l f‖ * |δ - 0| := by fun_prop
    have h1 := h0.tendsto 0
    simp only [map_zero, norm_zero, mul_zero, zero_mul] at h1
    exact squeeze_zero_norm (fun f => intervalIntegral.norm_integral_le_of_norm_le_const fun s _ => hb s f) h1
  refine ⟨⟨m, mc⟩, hδ, ?_⟩
  have key : ∀ t, m (S t φ) = (∫ s in (0 : ℝ)..(δ + t), lam (S s φ)) - ∫ s in (0 : ℝ)..t, lam (S s φ) := fun t => by
    rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    have := intervalIntegral.integral_comp_add_right (fun s => lam (S s φ)) (a := 0) (b := δ) t
    rw [zero_add] at this
    rw [← this]
    simp only [Sm]
    rfl
  show DifferentiableAt ℝ (fun t => m (S t φ)) 0
  simp only [key]
  exact (((hI (δ + 0)).comp_const_add δ 0).sub (hI 0)).differentiableAt

/- English proof (translation)
Take `⟨X, hsp, hs⟩` from `exists_sp s sc s0 sm ss`. Take `⟨ε, V, W, a, hε, V0, Vi, -, Vd⟩` from `hL l X hsp`. Take `⟨φ, hφ⟩` from `exists_ne_zero (0 : EuclideanSpace ℝ l)`. Establish `hφ0 : φ ≠ 0` using `fun h => hφ (by simp [h])`. Establish `hc : ∀ t, |t| < ε → ∃ c : ℂ, ∀ f, S t f = c • V t f` using `fun t ht => by`.

Take `⟨h1, h2, h3⟩` from `Vi t ht`. Establish `hi : Impl id (S (-t) ∘ₗ (V t).toLinearMap)` using `⟨fun f => ((hS (-t)).norm _).trans (h3.norm f), fun w f g hg => by`. Use `(hS (-t)).impl _ _ _ (h3.impl w f g hg)` as an intermediate fact. Rewrite `this` using `[← hs, ← sm, neg_add_cancel, s0]`. Conclude with `this⟩`.

Take `⟨c, hc⟩` from `hi.scalar fun f => ⟨W t (S t f), by show S (-t) (V t (W t _)) = f`. Rewrite using `[h1, ← Sm, neg_add_cancel, S0]⟩`. Establish `h4 : ∀ f, V t f = c • S t f` using `fun f => by`. Rewrite using `[← map_smul, ← hc]`. Use `show _ = S t (S (-t) (V t f))`.

Rewrite using `[← Sm, add_neg_cancel, S0]`. Establish `h5 : c ≠ 0` using `fun h => hφ0 (by rw [← h2 φ, h4, h, zero_smul, map_zero])`. Conclude with `⟨c⁻¹, fun f => by rw [h4, smul_smul, inv_mul_cancel₀ h5, one_smul]⟩`. Take `⟨mu, hmu, md⟩` from `exists_smooth_fun S (fun t => (hS t).norm) S0 Sm Sc hφ0`. Establish `hV0 : mu (V 0 φ) ≠ 0` using `by rwa [V0]`.

Set `c : ℝ → ℂ` to `fun t => mu (S t φ) / mu (V t φ)`. Establish `cd : DifferentiableAt ℝ c 0` using `md.div (Vd φ mu).differentiableAt hV0`. Establish `c0 : c 0 = 1` using `by simp only [c, S0, V0]; exact div_self hmu`. Establish `ev : ∀ᶠ t in nhds (0 : ℝ), ∀ f, S t f = c t • V t f`. Establish `e1 : ∀ᶠ t in nhds (0 : ℝ), |t| < ε` using `continuous_abs.continuousAt.eventually_lt continuousAt_const (by simpa using hε)`.

Use `filter_upwards [e1, (Vd φ mu).continuousAt.eventually_ne hV0] with t ht hne f`. Take `⟨b, hb⟩` from `hc t ht`. Establish `: c t = b`. Simplify using `only [c, hb, map_smul, smul_eq_mul]`. Conclude with `mul_div_cancel_right₀ _ hne`.

Rewrite using `[this, hb]`. Use `⟨(deriv c 0 + a) • 1 + quad X, add_mem (Subalgebra.smul_mem _ (one_mem _) _) (quad_mem X), fun f lam => ?_⟩` and prove the remaining obligations. Use `((cd.hasDerivAt.fun_mul (Vd f lam)).congr_deriv ?_).congr_of_eventuallyEq ?_` and prove the remaining obligations. Simplify using `[c0, V0]`. Expand and normalize the polynomial expressions, which then agree.

Use `filter_upwards [ev] with t ht`. Rewrite using `[ht, map_smul, smul_eq_mul]`.
-/
theorem lie' (hL : PositivityTheory.ThKR.LocalLift) (s : ℝ → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ))
    (sc : ∀ w, Continuous fun t => s t w) (s0 : ∀ w, s 0 w = w) (sm : ∀ t u w, s (t + u) w = s t (s u w))
    (ss : ∀ t w w', sympl (s t w) (s t w') = sympl w w') (S : ℝ → Sch l →ₗ[ℂ] Sch l) (hS : ∀ t, Impl (s t) (S t))
    (S0 : ∀ f, S 0 f = f) (Sm : ∀ t u f, S (t + u) f = S t (S u f))
    (Sc : ∀ f (lam : Sch l →L[ℂ] ℂ), Continuous fun t => lam (S t f)) :
    ∃ Q ∈ weylAlg l, ∀ f (lam : Sch l →L[ℂ] ℂ), HasDerivAt (fun t => lam (S t f)) (lam (Q f)) 0 := by
  obtain ⟨X, hsp, hs⟩ := exists_sp s sc s0 sm ss
  obtain ⟨ε, V, W, a, hε, V0, Vi, -, Vd⟩ := hL l X hsp
  obtain ⟨φ, hφ⟩ := exists_ne_zero (0 : EuclideanSpace ℝ l)
  have hφ0 : φ ≠ 0 := fun h => hφ (by simp [h])
  have hc : ∀ t, |t| < ε → ∃ c : ℂ, ∀ f, S t f = c • V t f := fun t ht => by
    obtain ⟨h1, h2, h3⟩ := Vi t ht
    have hi : Impl id (S (-t) ∘ₗ (V t).toLinearMap) := ⟨fun f => ((hS (-t)).norm _).trans (h3.norm f), fun w f g hg => by
      have := (hS (-t)).impl _ _ _ (h3.impl w f g hg)
      rw [← hs, ← sm, neg_add_cancel, s0] at this
      exact this⟩
    obtain ⟨c, hc⟩ := hi.scalar fun f => ⟨W t (S t f), by
      show S (-t) (V t (W t _)) = f
      rw [h1, ← Sm, neg_add_cancel, S0]⟩
    have h4 : ∀ f, V t f = c • S t f := fun f => by
      rw [← map_smul, ← hc]
      show _ = S t (S (-t) (V t f))
      rw [← Sm, add_neg_cancel, S0]
    have h5 : c ≠ 0 := fun h => hφ0 (by rw [← h2 φ, h4, h, zero_smul, map_zero])
    exact ⟨c⁻¹, fun f => by rw [h4, smul_smul, inv_mul_cancel₀ h5, one_smul]⟩
  obtain ⟨mu, hmu, md⟩ := exists_smooth_fun S (fun t => (hS t).norm) S0 Sm Sc hφ0
  have hV0 : mu (V 0 φ) ≠ 0 := by rwa [V0]
  let c : ℝ → ℂ := fun t => mu (S t φ) / mu (V t φ)
  have cd : DifferentiableAt ℝ c 0 := md.div (Vd φ mu).differentiableAt hV0
  have c0 : c 0 = 1 := by simp only [c, S0, V0]; exact div_self hmu
  have ev : ∀ᶠ t in nhds (0 : ℝ), ∀ f, S t f = c t • V t f := by
    have e1 : ∀ᶠ t in nhds (0 : ℝ), |t| < ε := continuous_abs.continuousAt.eventually_lt continuousAt_const (by simpa using hε)
    filter_upwards [e1, (Vd φ mu).continuousAt.eventually_ne hV0] with t ht hne f
    obtain ⟨b, hb⟩ := hc t ht
    have : c t = b := by
      simp only [c, hb, map_smul, smul_eq_mul]
      exact mul_div_cancel_right₀ _ hne
    rw [this, hb]
  refine ⟨(deriv c 0 + a) • 1 + quad X, add_mem (Subalgebra.smul_mem _ (one_mem _) _) (quad_mem X), fun f lam => ?_⟩
  refine ((cd.hasDerivAt.fun_mul (Vd f lam)).congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp [c0, V0]
    ring
  · filter_upwards [ev] with t ht
    rw [ht, map_smul, smul_eq_mul]

end PositivityTheory.ThKR
