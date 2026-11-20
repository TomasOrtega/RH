import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QxChain
import Formalism.FormalDegreeBessel.FormalDegreeRatio.WRWeyl
import Formalism.FormalDegreeBessel.FormalDegreeRatio.WRPres
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AlgebraSmulCommClassComplex

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff Topology
open Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.TVCrdLoc

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {k r : ℕ}

def gam (k r : ℕ) (a : Fin r) (x : Fin r → ℂ) : ℂ := ((‖x a‖ ^ (Mdim k r a - 1) : ℝ) : ℂ)

/- English proof (translation)
Use function extensionality and compare the values at `x`. Unfold `gaugeF Formalism.FourierDecayAlt.Q.resG`. Simplify using `only [smul_eq_mul, mul_one, gam, Complex.ofReal_prod]`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[if_pos (by simp)]`.
-/
theorem gaugeF_eq (k r : ℕ) : gaugeF k r = fun x => ∏ a : Fin r, gam k r a x := by
  funext x
  unfold gaugeF Formalism.FourierDecayAlt.Q.resG
  simp only [smul_eq_mul, mul_one, gam, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [if_pos (by simp)]

/- English proof (translation)
Introduce `x hx`. Establish `h1 : ContDiffAt ℝ ∞ (fun c : Fin r → ℂ => ‖c a‖) x` using `(contDiffAt_norm ℝ (hx a)).comp x (ContinuousLinearMap.proj a : (Fin r → ℂ) →L[ℝ] ℂ).contDiff.contDiffAt`. Establish `h2` using `Complex.ofRealCLM.contDiff.contDiffAt.comp x (h1.pow (Mdim k r a - 1))`. Conclude with `h2.contDiffWithinAt`.
-/
theorem gam_smooth (a : Fin r) : ContDiffOn ℝ ∞ (gam k r a) (OmX r) := by
  intro x hx
  have h1 : ContDiffAt ℝ ∞ (fun c : Fin r → ℂ => ‖c a‖) x :=
    (contDiffAt_norm ℝ (hx a)).comp x
      (ContinuousLinearMap.proj a : (Fin r → ℂ) →L[ℝ] ℂ).contDiff.contDiffAt
  have h2 := Complex.ofRealCLM.contDiff.contDiffAt.comp x (h1.pow (Mdim k r a - 1))
  exact h2.contDiffWithinAt

/- English proof (translation)
Rewrite using `[gaugeF_eq]`. Conclude with `contDiffOn_prod fun a _ => gam_smooth a`.
-/
theorem gaugeF_smooth : ContDiffOn ℝ ∞ (gaugeF k r) (OmX r) := by
  rw [gaugeF_eq]
  exact contDiffOn_prod fun a _ => gam_smooth a

/- English proof (translation)
Rewrite using `[gaugeF_eq]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun a _ => Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr (hc a)))`.
-/
theorem gaugeF_ne {c : Fin r → ℂ} (hc : c ∈ OmX r) : gaugeF k r c ≠ 0 := by
  rw [gaugeF_eq]
  exact Finset.prod_ne_zero_iff.mpr fun a _ =>
    Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr (hc a)))

/- English proof (translation)
Establish `hf : HasDerivAt (fun t : ℝ => x + t • v) v 0`. Simplify using `using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x`. Establish `h1 : HasDerivAt (fun t : ℝ => h (x + t • v)) (fderiv ℝ h x v) 0` using `hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hf (by simp)`. Establish `h2 : HasDerivAt (fun t : ℝ => h (x + t • v)) 0 0`. Repeatedly rewrite using `[hc]`.

Conclude with `hasDerivAt_const _ _`. Conclude with `h1.unique h2`.
-/
theorem fderiv_zero_of_const {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {h : (Fin r → ℂ) → F}
    {x v : Fin r → ℂ} (hd : DifferentiableAt ℝ h x) (hc : ∀ t : ℝ, h (x + t • v) = h x) :
    fderiv ℝ h x v = 0 := by
  have hf : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have h1 : HasDerivAt (fun t : ℝ => h (x + t • v)) (fderiv ℝ h x v) 0 :=
    hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hf (by simp)
  have h2 : HasDerivAt (fun t : ℝ => h (x + t • v)) 0 0 := by
    simp_rw [hc]
    exact hasDerivAt_const _ _
  exact h1.unique h2

def gamO (k r : ℕ) (i : Fin r) (x : Fin r → ℂ) : ℂ := ∏ a ∈ Finset.univ.erase i, gam k r a x

/- English proof (translation)
Unfold `gamO`. Conclude with `contDiffOn_prod fun a _ => gam_smooth a`.
-/
theorem gamO_smooth (i : Fin r) : ContDiffOn ℝ ∞ (gamO k r i) (OmX r) := by
  unfold gamO
  exact contDiffOn_prod fun a _ => gam_smooth a

/- English proof (translation)
Unfold `gamO`. Use `Finset.prod_congr rfl fun a ha => ?_` and prove the remaining obligations. Establish `hai : a ≠ i` using `Finset.ne_of_mem_erase ha`. Simplify using `only [gam, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hai, smul_zero, add_zero]`.
-/
theorem gamO_line (i : Fin r) (x : Fin r → ℂ) (w : ℂ) (t : ℝ) :
    gamO k r i (x + t • (Pi.single i w : Fin r → ℂ)) = gamO k r i x := by
  unfold gamO
  refine Finset.prod_congr rfl fun a ha => ?_
  have hai : a ≠ i := Finset.ne_of_mem_erase ha
  simp only [gam, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hai, smul_zero, add_zero]

/- English proof (translation)
Rewrite using `[gaugeF_eq, gamO]`. Conclude with `(Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm`.
-/
theorem gauge_split (i : Fin r) (x : Fin r → ℂ) : gaugeF k r x = gam k r i x * gamO k r i x := by
  rw [gaugeF_eq, gamO]
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

/- English proof (translation)
Unfold `Formalism.QuantumDeterminants.wirtBar`. Establish `e : (fun y => c y • φ y) = c • φ` using `rfl`. Rewrite using `[e, fderiv_smul hc hφ]`. Simplify using `only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]`. Use `module`.
-/
private theorem wbar_smul_lemma {m : ℕ} (l : Fin m) (c : (Fin m → ℂ) → ℂ) (φ : (Fin m → ℂ) → X)
    (x : Fin m → ℂ) (hc : DifferentiableAt ℝ c x) (hφ : DifferentiableAt ℝ φ x) :
    wirtBar l (fun y => c y • φ y) x = c x • wirtBar l φ x + wirtBar l c x • φ x := by
  unfold Formalism.QuantumDeterminants.wirtBar
  have e : (fun y => c y • φ y) = c • φ := rfl
  rw [e, fderiv_smul hc hφ]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  module

/- English proof (translation)
Use function extensionality and compare the values at `x`. Use `show pbOp i (fun x => gaugeF k r x • f x) x = gaugeF k r x • pbOp i f x + (((Mdim k r i - 1 : ℕ) : ℂ) / 2) • (gaugeF k r x • f x)`. Distinguish the cases in `hx : x ∈ OmX r`. Establish `hO : IsOpen (OmX r)`. Establish `e : OmX r = ⋂ l, {y : Fin r → ℂ | y l ≠ 0}`.

Use extensionality with `y`. Simplify using `[OmX]`. Rewrite using `[e]`. Conclude with `isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const`. Establish `hfd : DifferentiableAt ℝ f x` using `(hf.1.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)`.

Establish `hgi : DifferentiableAt ℝ (gam k r i) x` using `Formalism.FourierDecayAlt.P.Qx6.diff_gamma i _ hx`. Establish `hgO : DifferentiableAt ℝ (gamO k r i) x` using `((gamO_smooth i).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)`. Establish `hsplit : (fun y => gaugeF k r y • f y) = fun y => gam k r i y • (gamO k r i y • f y)`. Use function extensionality and compare the values at `y`. Rewrite using `[gauge_split, mul_smul]`.

Establish `hwO : wirtBar i (gamO k r i) x = 0`. Unfold `Formalism.QuantumDeterminants.wirtBar`. Rewrite using `[fderiv_zero_of_const hgO (gamO_line i x 1), fderiv_zero_of_const hgO (gamO_line i x Complex.I)]`. Simplify using the standard rewrite rules. Establish `hpg` using `Formalism.FourierDecayAlt.P.Qx6.pbOp_gamma i hx (Mdim k r i - 1)`.

Unfold `pbOp at hpg`. Rewrite `hpg` using `[if_pos hx]`. Establish `key : star (x i) * wirtBar i (gam k r i) x = ((Mdim k r i - 1 : ℕ) : ℂ) / 2 * gam k r i x`. Rewrite using `[← smul_eq_mul]`. Conclude with `hpg`.

Unfold `pbOp`. Rewrite using `[if_pos hx, if_pos hx, hsplit, wbar_smul_lemma i (gam k r i) (fun y => gamO k r i y • f y) x hgi (hgO.smul hfd), wbar_smul_lemma i _ _ x hgO hfd, hwO, gauge_split]`. Simplify using `only [smul_add, zero_smul, add_zero, smul_smul]`. Rewrite using `[← mul_assoc (star (x i)) (wirtBar i (gam k r i) x), key]`. Apply the tactic sequence `congr 1 <;> congr 1 <;> ring`.

Unfold `pbOp`. Rewrite using `[if_neg hx, if_neg hx, hf.2 x hx]`. Simplify using the standard rewrite rules.
-/
theorem pbOp_gauge (i : Fin r) (f : (Fin r → ℂ) → X) (hf : f ∈ WSm r X) :
    pbOp i (fun x => gaugeF k r x • f x) =
      fun x => gaugeF k r x • pbOp i f x + (((Mdim k r i - 1 : ℕ) : ℂ) / 2) • (gaugeF k r x • f x) := by
  funext x
  show pbOp i (fun x => gaugeF k r x • f x) x =
    gaugeF k r x • pbOp i f x + (((Mdim k r i - 1 : ℕ) : ℂ) / 2) • (gaugeF k r x • f x)
  by_cases hx : x ∈ OmX r
  · have hO : IsOpen (OmX r) := by
      have e : OmX r = ⋂ l, {y : Fin r → ℂ | y l ≠ 0} := by
        ext y
        simp [OmX]
      rw [e]
      exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
    have hfd : DifferentiableAt ℝ f x :=
      (hf.1.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
    have hgi : DifferentiableAt ℝ (gam k r i) x := Formalism.FourierDecayAlt.P.Qx6.diff_gamma i _ hx
    have hgO : DifferentiableAt ℝ (gamO k r i) x :=
      ((gamO_smooth i).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
    have hsplit : (fun y => gaugeF k r y • f y) = fun y => gam k r i y • (gamO k r i y • f y) := by
      funext y
      rw [gauge_split, mul_smul]

    have hwO : wirtBar i (gamO k r i) x = 0 := by
      unfold Formalism.QuantumDeterminants.wirtBar
      rw [fderiv_zero_of_const hgO (gamO_line i x 1), fderiv_zero_of_const hgO (gamO_line i x Complex.I)]
      simp
    have hpg := Formalism.FourierDecayAlt.P.Qx6.pbOp_gamma i hx (Mdim k r i - 1)
    unfold pbOp at hpg
    rw [if_pos hx] at hpg
    have key : star (x i) * wirtBar i (gam k r i) x =
        ((Mdim k r i - 1 : ℕ) : ℂ) / 2 * gam k r i x := by
      rw [← smul_eq_mul]
      exact hpg
    unfold pbOp
    rw [if_pos hx, if_pos hx, hsplit, wbar_smul_lemma i (gam k r i) (fun y => gamO k r i y • f y) x hgi (hgO.smul hfd),
      wbar_smul_lemma i _ _ x hgO hfd, hwO, gauge_split]
    simp only [smul_add, zero_smul, add_zero, smul_smul]
    rw [← mul_assoc (star (x i)) (wirtBar i (gam k r i) x), key]
    congr 1 <;> congr 1 <;> ring
  · unfold pbOp
    rw [if_neg hx, if_neg hx, hf.2 x hx]
    simp

/- English proof (translation)
Establish `hO : IsOpen (OmX r)`. Establish `e : OmX r = ⋂ l, {y : Fin r → ℂ | y l ≠ 0}`. Use extensionality with `y`. Simplify using `[OmX]`. Rewrite using `[e]`.

Conclude with `isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const`. Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.mp hU c hc`. Set `χ : ContDiffBump c` to `⟨ε / 4, ε / 2, by positivity, by linarith⟩`. Establish `hcl : Metric.closedBall c (ε / 2) ⊆ U` using `(Metric.closedBall_subset_ball (by linarith)).trans hball`. Establish `hχ0 : ∀ z, z ∉ Metric.closedBall c (ε / 2) → χ z = 0`.

Introduce `z hz`. Establish `h1 : z ∉ Function.support χ`. Rewrite using `[χ.support_eq]`. Conclude with `fun h => hz (Metric.ball_subset_closedBall h)`. Simplify `h1` using `[Function.mem_support]`.

Set `φ : (Fin r → ℂ) → X` to `fun y => χ y • ((gaugeF k r y)⁻¹ • (gaugeF k r y • Φ y))`. Establish `hev : Φ =ᶠ[𝓝 c] φ`. Use `Filter.eventually_of_mem (Metric.ball_mem_nhds c (by positivity : (0 : ℝ) < ε / 4)) fun y hy => ?_` and prove the remaining obligations. Establish `hyU : y ∈ U` using `hball (Metric.ball_subset_ball (by linarith) hy)`. Establish `h1 : χ y = 1` using `χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)`.

Use `show Φ y = χ y • ((gaugeF k r y)⁻¹ • (gaugeF k r y • Φ y))`. Rewrite using `[h1, one_smul, inv_smul_smul₀ (gaugeF_ne (hUO hyU))]`. Establish `hsm : ∀ y ∈ OmX r, ContDiffAt ℝ ∞ φ y`. Introduce `y hyO`. Distinguish the cases in `hyU : y ∈ U`.

Establish `hg` using `(gaugeF_smooth (k := k)).contDiffAt (hO.mem_nhds hyO)`. Establish `hgi` using `hg.inv (gaugeF_ne hyO)`. Establish `hΨ'` using `hΨ.contDiffAt (hU.mem_nhds hyU)`. Conclude with `χ.contDiff.contDiffAt.smul (hgi.smul hΨ')`. Establish `hyc : y ∉ Metric.closedBall c (ε / 2)` using `fun h => hyU (hcl h)`.

Use `(contDiffAt_const (c := (0 : X))).congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `Filter.eventually_of_mem (Metric.isClosed_closedBall.isOpen_compl.mem_nhds hyc) fun z hz => ?_` and prove the remaining obligations. Use `show χ z • ((gaugeF k r z)⁻¹ • (gaugeF k r z • Φ z)) = 0`. Rewrite using `[hχ0 z hz, zero_smul]`. Use `⟨φ, ?_, hev, hev.mono fun y hy => congrArg (gaugeF k r y • ·) hy⟩` and prove the remaining obligations.

Use `show ContDiffOn ℝ ∞ φ (OmX r) ∧ ∀ x, x ∉ OmX r → φ x = 0`. Use `⟨fun y hy => (hsm y hy).contDiffWithinAt, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hyc : y ∉ Metric.closedBall c (ε / 2)` using `fun h => hy (hUO (hcl h))`. Use `show χ y • ((gaugeF k r y)⁻¹ • (gaugeF k r y • Φ y)) = 0`. Rewrite using `[hχ0 y hyc, zero_smul]`.
-/
theorem loc (Φ : (Fin r → ℂ) → X) (U : Set (Fin r → ℂ)) (c : Fin r → ℂ) (hU : IsOpen U) (hUO : U ⊆ OmX r)
    (hc : c ∈ U) (hΨ : ContDiffOn ℝ ∞ (fun c' => gaugeF k r c' • Φ c') U) :
    ∃ φ : (Fin r → ℂ) → X, φ ∈ WSm r X ∧ Φ =ᶠ[𝓝 c] φ ∧
      (fun c' => gaugeF k r c' • Φ c') =ᶠ[𝓝 c] (fun c' => gaugeF k r c' • φ c') := by
  have hO : IsOpen (OmX r) := by
    have e : OmX r = ⋂ l, {y : Fin r → ℂ | y l ≠ 0} := by
      ext y
      simp [OmX]
    rw [e]
    exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU c hc

  let χ : ContDiffBump c := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hcl : Metric.closedBall c (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hχ0 : ∀ z, z ∉ Metric.closedBall c (ε / 2) → χ z = 0 := by
    intro z hz
    have h1 : z ∉ Function.support χ := by
      rw [χ.support_eq]
      exact fun h => hz (Metric.ball_subset_closedBall h)
    simpa [Function.mem_support] using h1
  let φ : (Fin r → ℂ) → X := fun y => χ y • ((gaugeF k r y)⁻¹ • (gaugeF k r y • Φ y))
  have hev : Φ =ᶠ[𝓝 c] φ := by
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds c (by positivity : (0 : ℝ) < ε / 4))
      fun y hy => ?_
    have hyU : y ∈ U := hball (Metric.ball_subset_ball (by linarith) hy)
    have h1 : χ y = 1 := χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
    show Φ y = χ y • ((gaugeF k r y)⁻¹ • (gaugeF k r y • Φ y))
    rw [h1, one_smul, inv_smul_smul₀ (gaugeF_ne (hUO hyU))]
  have hsm : ∀ y ∈ OmX r, ContDiffAt ℝ ∞ φ y := by
    intro y hyO
    by_cases hyU : y ∈ U
    · have hg := (gaugeF_smooth (k := k)).contDiffAt (hO.mem_nhds hyO)
      have hgi := hg.inv (gaugeF_ne hyO)
      have hΨ' := hΨ.contDiffAt (hU.mem_nhds hyU)
      exact χ.contDiff.contDiffAt.smul (hgi.smul hΨ')
    · have hyc : y ∉ Metric.closedBall c (ε / 2) := fun h => hyU (hcl h)
      refine (contDiffAt_const (c := (0 : X))).congr_of_eventuallyEq ?_
      refine Filter.eventually_of_mem (Metric.isClosed_closedBall.isOpen_compl.mem_nhds hyc)
        fun z hz => ?_
      show χ z • ((gaugeF k r z)⁻¹ • (gaugeF k r z • Φ z)) = 0
      rw [hχ0 z hz, zero_smul]
  refine ⟨φ, ?_, hev, hev.mono fun y hy => congrArg (gaugeF k r y • ·) hy⟩
  show ContDiffOn ℝ ∞ φ (OmX r) ∧ ∀ x, x ∉ OmX r → φ x = 0
  refine ⟨fun y hy => (hsm y hy).contDiffWithinAt, fun y hy => ?_⟩
  have hyc : y ∉ Metric.closedBall c (ε / 2) := fun h => hy (hUO (hcl h))
  show χ y • ((gaugeF k r y)⁻¹ • (gaugeF k r y • Φ y)) = 0
  rw [hχ0 y hyc, zero_smul]

end Formalism.FourierDecayAlt.P.CutMP.TVCrdLoc
