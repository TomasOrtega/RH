import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivedActionIntertwinesOfGroupStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzEqGaussianOfFderivAddEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfOrthogonalSchrodingerGaussianStatement
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz

noncomputable section

open MeasureTheory Complex
open scoped SchwartzMap Matrix Real RealInnerProductSpace

namespace GlobalTheory.RealWeil

/- English proof (translation)
Establish `h1 : HasFDerivAt (fun y : EuclideanSpace ℝ l => -Real.pi * ‖y‖ ^ 2) (-Real.pi • (2 • (innerSL ℝ) x ∘L ContinuousLinearMap.id ℝ _)) x` using `((hasFDerivAt_id x).norm_sq).const_mul (-Real.pi)`. Establish `h2` using `(ofRealCLM.hasFDerivAt (x := Real.exp (-Real.pi * ‖x‖ ^ 2))).comp x h1.exp`. Establish `e : ⇑(GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l)) = (ofRealCLM : ℝ →L[ℝ] ℂ) ∘ fun y : EuclideanSpace ℝ l => Real.exp (-Real.pi * ‖y‖ ^ 2)`. Use function extensionality and compare the values at `y`. Simplify using the standard rewrite rules.

Rewrite using `[e, h2.fderiv]`. Simplify using `[EuclideanSpace.inner_single_right]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fderiv_gaussianSchwartz_single_add {l : Type} [Fintype l] [DecidableEq l] (j : l) (x : EuclideanSpace ℝ l) :
    fderiv ℝ (⇑(GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l))) x (EuclideanSpace.single j 1) +
      2 * Real.pi * (x j : ℂ) * GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l) x = 0 := by
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ l => -Real.pi * ‖y‖ ^ 2)
      (-Real.pi • (2 • (innerSL ℝ) x ∘L ContinuousLinearMap.id ℝ _)) x :=
    ((hasFDerivAt_id x).norm_sq).const_mul (-Real.pi)
  have h2 := (ofRealCLM.hasFDerivAt (x := Real.exp (-Real.pi * ‖x‖ ^ 2))).comp x h1.exp
  have e : ⇑(GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l)) =
      (ofRealCLM : ℝ →L[ℝ] ℂ) ∘ fun y : EuclideanSpace ℝ l => Real.exp (-Real.pi * ‖y‖ ^ 2) := by
    funext y; simp
  rw [e, h2.fderiv]
  simp [EuclideanSpace.inner_single_right]
  ring

/- English proof (translation)
Introduce `l _ S hiso f g`. Use `set U := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ l)) with hU`. Establish `hn : ∀ h : Sch l, ‖U (S h)‖ = ‖U h‖`. Introduce `h`. Simplify using `only [hU, SchwartzMap.toLpCLM_apply]`.

Rewrite using `[SchwartzMap.norm_toLp' (by norm_num) (by norm_num), SchwartzMap.norm_toLp' (by norm_num) (by norm_num)]`. Simplify using `only [ENNReal.toReal_ofNat, Real.rpow_two]`. Rewrite using `[hiso]`. Establish `e1 : (S f).toLp 2 volume = U (S f)` using `rfl`. Establish `e2 : (S g).toLp 2 volume = U (S g)` using `rfl`.

Establish `e3 : f.toLp 2 volume = U f` using `rfl`. Establish `e4 : g.toLp 2 volume = U g` using `rfl`. Rewrite using `[e1, e2, e3, e4, inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four]`. Simplify using `only [← map_add, ← map_sub, ← map_smul, hn]`.
-/
theorem inner_toLp_map_of_integral_norm_sq : ∀ (l : Type) [Fintype l] (S : Sch l →ₗ[ℂ] Sch l),
    (∀ f, ∫ x, ‖S f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) →
    ∀ f g, inner ℂ ((S f).toLp 2 volume) ((S g).toLp 2 volume) = inner ℂ (f.toLp 2 volume) (g.toLp 2 volume) := by
  intro l _ S hiso f g
  set U := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ l)) with hU
  have hn : ∀ h : Sch l, ‖U (S h)‖ = ‖U h‖ := by
    intro h
    simp only [hU, SchwartzMap.toLpCLM_apply]
    rw [SchwartzMap.norm_toLp' (by norm_num) (by norm_num), SchwartzMap.norm_toLp' (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    rw [hiso]
  have e1 : (S f).toLp 2 volume = U (S f) := rfl
  have e2 : (S g).toLp 2 volume = U (S g) := rfl
  have e3 : f.toLp 2 volume = U f := rfl
  have e4 : g.toLp 2 volume = U g := rfl
  rw [e1, e2, e3, e4, inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four]
  simp only [← map_add, ← map_sub, ← map_smul, hn]

/- English proof (translation)
Introduce `l _ S hiso hcomm`. Establish `hl : ∀ g : Sch l, ∫⁻ x, ‖g x‖ₑ ^ 2 = ENNReal.ofReal (∫ x, ‖g x‖ ^ 2)`. Introduce `g`. Rewrite using `[ofReal_integral_eq_lintegral_ofReal ((g.memLp (2 : ℕ) volume).integrable_norm_pow (by norm_num)) (.of_forall fun x => by positivity)]`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations.

Rewrite using `[ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]`. Establish `hbound : ∀ f, ∫⁻ x, ‖S f x‖ₑ ^ 2 ≤ 1 * ∫⁻ x, ‖f x‖ₑ ^ 2`. Introduce `f`. Rewrite using `[one_mul, hl, hl, hiso]`. Establish `hd` using `GlobalTheory.T.derived_action_intertwines_of_group l LinearMap.id S 1 ENNReal.one_ne_top hbound (by simpa using hcomm)`.

Use `set G : Sch l := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l) with hG`. Establish `hN : ∀ (j : l) (h : Sch l) x, (dRho (Pi.single (Sum.inl j) 1) h - I • dRho (Pi.single (Sum.inr j) 1) h) x = fderiv ℝ (⇑h) x (EuclideanSpace.single j 1) + 2 * Real.pi * (x j : ℂ) * h x`. Introduce `j h x`. Rewrite using `[SchwartzMap.sub_apply, SchwartzMap.smul_apply, dRho_single_inl, dRho_single_inr, SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul]`. Put the polynomial expressions in normal form.

Rewrite using `[I_sq]`. Expand and normalize the polynomial expressions, which then agree. Establish `hSG : ∀ j (x : EuclideanSpace ℝ l), fderiv ℝ (⇑(S G)) x (EuclideanSpace.single j 1) + 2 * Real.pi * (x j : ℂ) * S G x = 0`. Introduce `j x`. Establish `h0 : dRho (Pi.single (Sum.inl j) 1) G - I • dRho (Pi.single (Sum.inr j) 1) G = 0`.

Use extensionality with `y`. Rewrite using `[hN, hG, fderiv_gaussianSchwartz_single_add]`. Both sides reduce to the same expression. Use `congrArg S h0` as an intermediate fact. Rewrite `this` using `[map_sub, map_smul, hd, hd, map_zero]`.

Rewrite `*` using `[← hN, LinearMap.id_apply, LinearMap.id_apply]`. Rewrite using `[this]`. Both sides reduce to the same expression. Use `set c : ℂ := S G 0 with hc`. Establish `hSGc : S G = c • G`.

Use extensionality with `x`. Rewrite using `[GlobalTheory.T.schwartz_eq_gaussian_of_fderiv_add_eq_zero' l (S G) hSG x, SchwartzMap.smul_apply, smul_eq_mul, hG, GroundTheory.Global.gaussianSchwartz_apply]`. Establish `hrho : ∀ w, S (rhoSch w G) = c • rhoSch w G`. Introduce `w`. Use extensionality with `x`.

Rewrite using `[hcomm w G (rhoSch w G) (coe_rhoSch w G), hSGc, SchwartzMap.smul_apply, coe_rhoSch]`. Simplify using `only [rhoFun, SchwartzMap.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `key : ∀ f : Sch l, (starRingEnd ℂ c) • S f = f`. Introduce `f`.

Rewrite using `[← sub_eq_zero]`. Apply `GlobalTheory.T.eq_zero_of_orthogonal_schrodinger_gaussian l` to reduce the goal to its premises. Introduce `w`. Establish `hsm : ∀ (a : ℂ) (g : Sch l), (a • g).toLp 2 volume = a • g.toLp 2 volume` using `fun a g => (SchwartzMap.toLpCLM ℂ ℂ 2 volume).map_smul a g`. Establish `hsub : ∀ (g g' : Sch l), (g - g').toLp 2 volume = g.toLp 2 volume - g'.toLp 2 volume` using `fun g g' => (SchwartzMap.toLpCLM ℂ ℂ 2 volume).map_sub g g'`.

Establish `hp` using `inner_toLp_map_of_integral_norm_sq l S hiso (rhoSch w G) f`. Rewrite `hp` using `[hrho, hsm, inner_smul_left]`. Rewrite using `[hsub, hsm, inner_sub_right, inner_smul_right, hp, sub_self]`. Establish `hc0 : starRingEnd ℂ c ≠ 0`. Introduce `h0`.

Use `congrArg (fun g : Sch l => g 0) (key G)` as an intermediate fact. Simplify using `[h0, hG] at this`. Conclude with `⟨(starRingEnd ℂ c)⁻¹, fun f => by rw [← key f, smul_smul, inv_mul_cancel₀ hc0, one_smul, key]⟩`.
-/
theorem exists_eq_smul_of_commute_rhoFun : ∀ (l : Type) [Fintype l] (S : Sch l →ₗ[ℂ] Sch l),
    (∀ f, ∫ x, ‖S f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) →
    (∀ w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(S f₁) = rhoFun w ⇑(S f)) → ∃ c : ℂ, ∀ f, S f = c • f := by
  intro l _ S hiso hcomm
  classical
  have hl : ∀ g : Sch l, ∫⁻ x, ‖g x‖ₑ ^ 2 = ENNReal.ofReal (∫ x, ‖g x‖ ^ 2) := by
    intro g
    rw [ofReal_integral_eq_lintegral_ofReal ((g.memLp (2 : ℕ) volume).integrable_norm_pow (by norm_num))
      (.of_forall fun x => by positivity)]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have hbound : ∀ f, ∫⁻ x, ‖S f x‖ₑ ^ 2 ≤ 1 * ∫⁻ x, ‖f x‖ₑ ^ 2 := by
    intro f
    rw [one_mul, hl, hl, hiso]
  have hd := GlobalTheory.T.derived_action_intertwines_of_group l LinearMap.id S 1 ENNReal.one_ne_top hbound (by simpa using hcomm)
  set G : Sch l := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l) with hG
  have hN : ∀ (j : l) (h : Sch l) x, (dRho (Pi.single (Sum.inl j) 1) h - I • dRho (Pi.single (Sum.inr j) 1) h) x =
      fderiv ℝ (⇑h) x (EuclideanSpace.single j 1) + 2 * Real.pi * (x j : ℂ) * h x := by
    intro j h x
    rw [SchwartzMap.sub_apply, SchwartzMap.smul_apply, dRho_single_inl, dRho_single_inr,
      SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul]
    ring_nf
    rw [I_sq]
    ring
  have hSG : ∀ j (x : EuclideanSpace ℝ l), fderiv ℝ (⇑(S G)) x (EuclideanSpace.single j 1) +
      2 * Real.pi * (x j : ℂ) * S G x = 0 := by
    intro j x
    have h0 : dRho (Pi.single (Sum.inl j) 1) G - I • dRho (Pi.single (Sum.inr j) 1) G = 0 := by
      ext y
      rw [hN, hG, fderiv_gaussianSchwartz_single_add]
      rfl
    have := congrArg S h0
    rw [map_sub, map_smul, hd, hd, map_zero] at this
    rw [← hN, LinearMap.id_apply, LinearMap.id_apply] at *
    rw [this]
    rfl
  set c : ℂ := S G 0 with hc
  have hSGc : S G = c • G := by
    ext x
    rw [GlobalTheory.T.schwartz_eq_gaussian_of_fderiv_add_eq_zero' l (S G) hSG x, SchwartzMap.smul_apply, smul_eq_mul, hG, GroundTheory.Global.gaussianSchwartz_apply]
  have hrho : ∀ w, S (rhoSch w G) = c • rhoSch w G := by
    intro w
    ext x
    rw [hcomm w G (rhoSch w G) (coe_rhoSch w G), hSGc, SchwartzMap.smul_apply, coe_rhoSch]
    simp only [rhoFun, SchwartzMap.smul_apply, smul_eq_mul]
    ring
  have key : ∀ f : Sch l, (starRingEnd ℂ c) • S f = f := by
    intro f
    rw [← sub_eq_zero]
    apply GlobalTheory.T.eq_zero_of_orthogonal_schrodinger_gaussian l
    intro w
    have hsm : ∀ (a : ℂ) (g : Sch l), (a • g).toLp 2 volume = a • g.toLp 2 volume := fun a g =>
      (SchwartzMap.toLpCLM ℂ ℂ 2 volume).map_smul a g
    have hsub : ∀ (g g' : Sch l), (g - g').toLp 2 volume = g.toLp 2 volume - g'.toLp 2 volume := fun g g' =>
      (SchwartzMap.toLpCLM ℂ ℂ 2 volume).map_sub g g'
    have hp := inner_toLp_map_of_integral_norm_sq l S hiso (rhoSch w G) f
    rw [hrho, hsm, inner_smul_left] at hp
    rw [hsub, hsm, inner_sub_right, inner_smul_right, hp, sub_self]
  have hc0 : starRingEnd ℂ c ≠ 0 := by
    intro h0
    have := congrArg (fun g : Sch l => g 0) (key G)
    simp [h0, hG] at this
  exact ⟨(starRingEnd ℂ c)⁻¹, fun f => by rw [← key f, smul_smul, inv_mul_cancel₀ hc0, one_smul, key]⟩

end GlobalTheory.RealWeil
