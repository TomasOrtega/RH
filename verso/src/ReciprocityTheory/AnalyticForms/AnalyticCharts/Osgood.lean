import ReciprocityTheory.AnalyticForms.AnalyticCharts.OsgoodA

noncomputable section

namespace ReciprocityTheory.AnForm.Osgood

open Complex Metric MeasureTheory Set Filter Topology

open scoped Real

def OsgoodStatement : Prop :=
  ∀ (e : ℕ) (U : Set (Fin e → ℂ)) (f : (Fin e → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ f U →
    AnalyticOnNhd ℂ f U

variable {n : ℕ}

abbrev Cube (n : ℕ) : Type := Icc (0 : Fin n → ℝ) (fun _ => 2 * π)

instance : CompactSpace (Cube n) := isCompact_iff_compactSpace.mp isCompact_Icc

def cubeProj (θ : Fin n → ℝ) : Cube n :=
  ⟨fun i => (projIcc 0 (2 * π) Real.two_pi_pos.le (θ i) : ℝ),
    fun i => (projIcc 0 (2 * π) Real.two_pi_pos.le (θ i)).2.1,
    fun i => (projIcc 0 (2 * π) Real.two_pi_pos.le (θ i)).2.2⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem continuous_cubeProj : Continuous (cubeProj (n := n)) := by
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  exact continuous_subtype_val.comp (continuous_projIcc.comp (continuous_apply i))

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem cubeProj_of_mem {θ : Fin n → ℝ} (hθ : θ ∈ Icc (0 : Fin n → ℝ) (fun _ => 2 * π)) :
    (cubeProj θ : Fin n → ℝ) = θ := by
  funext i
  show ((projIcc 0 (2 * π) Real.two_pi_pos.le (θ i) : ℝ)) = θ i
  have hi : θ i ∈ Icc (0 : ℝ) (2 * π) := ⟨hθ.1 i, hθ.2 i⟩
  rw [projIcc_of_mem _ hi]

def cubeCoord (c : Fin n → ℂ) (r : ℝ) (i : Fin n) : C(Cube n, ℂ) :=
  ⟨fun θ => torusMap c (fun _ => r) θ.1 i,
    ((continuous_apply i).comp (continuous_torusMap c r)).comp continuous_subtype_val⟩

def kern (c : Fin n → ℂ) (r : ℝ) (z : Fin n → ℂ) : C(Cube n, ℂ) :=
  ∏ i, Ring.inverse (cubeCoord c r i - z i • (1 : C(Cube n, ℂ)))

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem cubeCoord_sub_smul_one_apply (c z : Fin n → ℂ) (r : ℝ) (i : Fin n) (θ : Cube n) :
    (cubeCoord c r i - z i • (1 : C(Cube n, ℂ))) θ = torusMap c (fun _ => r) θ.1 i - z i := by
  simp [cubeCoord]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem cubeCoord_sub_smul_one_ne_zero_of_mem_ball {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) (hz : z ∈ ball c r) (i : Fin n)
    (θ : Cube n) : (cubeCoord c r i - z i • (1 : C(Cube n, ℂ))) θ ≠ 0 := by
  rw [cubeCoord_sub_smul_one_apply]
  exact torusMap_sub_ne hr hz θ.1 i

/- English proof (translation)
Supply the required witnesses or components.
-/
private theorem continuousMap_isUnit_of_forall_ne_zero {X : Type*} [TopologicalSpace X] (g : C(X, ℂ)) (hg : ∀ x, g x ≠ 0) :
    IsUnit g :=
  ⟨⟨g, ⟨fun x => (g x)⁻¹, g.continuous.inv₀ hg⟩, by ext x; simp [hg x], by ext x; simp [hg x]⟩, rfl⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem continuousMap_ring_inverse_apply {X : Type*} [TopologicalSpace X] (g : C(X, ℂ)) (hg : ∀ x, g x ≠ 0)
    (x : X) : Ring.inverse g x = (g x)⁻¹ := by
  obtain ⟨u, rfl⟩ := continuousMap_isUnit_of_forall_ne_zero g hg
  rw [Ring.inverse_unit]
  exact eq_inv_of_mul_eq_one_right (by rw [← ContinuousMap.mul_apply, Units.mul_inv, ContinuousMap.one_apply])

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem kern_apply {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) (hz : z ∈ ball c r) (θ : Cube n) :
    kern c r z θ = ∏ i, (torusMap c (fun _ => r) θ.1 i - z i)⁻¹ := by
  unfold kern
  simp only [ContinuousMap.coe_prod, Finset.prod_apply]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [continuousMap_ring_inverse_apply _ (cubeCoord_sub_smul_one_ne_zero_of_mem_ball hr hz i) θ, cubeCoord_sub_smul_one_apply]

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem kern_analyticAt (c : Fin n → ℂ) {r : ℝ} (hr : 0 < r) : AnalyticAt ℂ (kern c r) c := by
  have hK : kern c r = ∏ i ∈ Finset.univ,
      fun z : Fin n → ℂ => Ring.inverse (cubeCoord c r i - z i • (1 : C(Cube n, ℂ))) := by
    funext z
    rw [Finset.prod_apply]
    rfl
  rw [hK]
  refine Finset.analyticAt_prod _ fun i _ => ?_
  have hlin : AnalyticAt ℂ (fun z : Fin n → ℂ => z i • (1 : C(Cube n, ℂ))) c :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).smulRight
      (1 : C(Cube n, ℂ))).analyticAt c
  obtain ⟨u, hu⟩ := continuousMap_isUnit_of_forall_ne_zero _ (cubeCoord_sub_smul_one_ne_zero_of_mem_ball hr (mem_ball_self hr) i)
  exact (analyticAt_inverse (𝕜 := ℂ) u).comp_of_eq (analyticAt_const.sub hlin) hu.symm

def jac (r : ℝ) (θ : Fin n → ℝ) : ℂ := ∏ i, (r : ℂ) * exp (θ i * I) * I

def fctl (c : Fin n → ℂ) (r : ℝ) (f : (Fin n → ℂ) → ℂ) (g : C(Cube n, ℂ)) : ℂ :=
  ∫ θ in Icc (0 : Fin n → ℝ) (fun _ => 2 * π), jac r θ * g (cubeProj θ) * f (torusMap c (fun _ => r) θ)

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem continuous_jac (r : ℝ) : Continuous (jac (n := n) r) := by
  unfold jac
  exact continuous_finsetProd _ fun i _ => by fun_prop

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem integrableOn_fctl {c : Fin n → ℂ} {r : ℝ} (hr : 0 < r) {f : (Fin n → ℂ) → ℂ}
    (hf : ∀ ζ ∈ closedBall c r, DifferentiableAt ℂ f ζ) (g : C(Cube n, ℂ)) :
    IntegrableOn (fun θ => jac r θ * g (cubeProj θ) * f (torusMap c (fun _ => r) θ))
      (Icc (0 : Fin n → ℝ) (fun _ => 2 * π)) :=
  (((continuous_jac r).mul (g.continuous.comp continuous_cubeProj)).mul
    (continuous_comp_torusMap hr.le hf)).integrableOn_Icc

def fctlCLM (c : Fin n → ℂ) {r : ℝ} (hr : 0 < r) (f : (Fin n → ℂ) → ℂ)
    (hf : ∀ ζ ∈ closedBall c r, DifferentiableAt ℂ f ζ) : C(Cube n, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fctl c r f
      map_add' := fun g g' => by
        simp only [fctl, ContinuousMap.add_apply, mul_add, add_mul]
        exact integral_add (integrableOn_fctl hr hf g) (integrableOn_fctl hr hf g')
      map_smul' := fun a g => by
        simp only [fctl, ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext θ
        ring }
    (by
      obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := fun _ => 2 * π)).exists_bound_of_continuousOn
        (((continuous_jac r).mul (continuous_comp_torusMap hr.le hf)).continuousOn)
      refine ⟨M * volume.real (Icc (0 : Fin n → ℝ) (fun _ => 2 * π)), fun g => ?_⟩
      refine (norm_setIntegral_le_of_norm_le_const (C := M * ‖g‖) measure_Icc_lt_top
        fun θ hθ => ?_).trans (le_of_eq (by ring))
      have h1 : ‖jac r θ * f (torusMap c (fun _ => r) θ)‖ ≤ M := hM θ hθ
      rw [mul_comm (jac r θ), mul_assoc, norm_mul, mul_comm M]
      calc ‖g (cubeProj θ)‖ * ‖jac r θ * f (torusMap c (fun _ => r) θ)‖
          ≤ ‖g‖ * ‖jac r θ * f (torusMap c (fun _ => r) θ)‖ :=
            mul_le_mul_of_nonneg_right (g.norm_coe_le_norm _) (norm_nonneg _)
        _ ≤ ‖g‖ * M := mul_le_mul_of_nonneg_left h1 (norm_nonneg _))

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Simplify by unfolding definitions. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem fctlCLM_kern {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) {f : (Fin n → ℂ) → ℂ}
    (hf : ∀ ζ ∈ closedBall c r, DifferentiableAt ℂ f ζ) (hz : z ∈ ball c r) :
    fctlCLM c hr f hf (kern c r z) = (2 * π * I) ^ n * f z := by
  rw [← cauchy_polydisc n f c r hr hf z hz]
  show fctl c r f (kern c r z) = _
  unfold fctl torusIntegral
  refine setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  dsimp only
  rw [kern_apply hr hz, cubeProj_of_mem hθ, smul_eq_mul, jac]
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem osgood : OsgoodStatement := by
  intro e U f hU hf x hx
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hx)
  have hfd : ∀ ζ ∈ closedBall x r, DifferentiableAt ℂ f ζ := fun ζ hζ =>
    hf.differentiableAt (hU.mem_nhds (hrU hζ))
  have hne : ((2 * π * I) ^ e : ℂ) ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero)) I_ne_zero)
  have hA : AnalyticAt ℂ
      (fun z => ((2 * π * I) ^ e)⁻¹ * fctlCLM x hr f hfd (kern x r z)) x :=
    analyticAt_const.mul (((fctlCLM x hr f hfd).analyticAt _).comp (kern_analyticAt x hr))
  refine hA.congr ?_
  filter_upwards [ball_mem_nhds x hr] with z hz
  rw [fctlCLM_kern hr hfd hz, inv_mul_cancel_left₀ hne]

end ReciprocityTheory.AnForm.Osgood
