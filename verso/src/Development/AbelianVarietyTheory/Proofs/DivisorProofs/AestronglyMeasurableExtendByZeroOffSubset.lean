import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZeroMemSolSet
import Formalism.UnipotentAdelicQuotients.EllRegCheck

open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction

noncomputable section

namespace GlobalTheory.HCA.SolSub

variable {d : ℕ}

/- English proof (translation)
The claim follows from `| [] => hf | j :: w => by have h := contDiff_dw hf w show ContDiff ℝ ∞ (fun x => fderiv ℝ (dw w f) x (ev j)) exact (h.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const`.
-/
theorem contDiff_dw {f : E d → ℂ} (hf : ContDiff ℝ ∞ f) : ∀ w : List (Fin d), ContDiff ℝ ∞ (dw w f)
  | [] => hf
  | j :: w => by
      have h := contDiff_dw hf w
      show ContDiff ℝ ∞ (fun x => fderiv ℝ (dw w f) x (ev j))
      exact (h.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/- English proof (translation)
The claim follows from `| [] => hf | j :: w => by have h := hasCompactSupport_dw hf w show HasCompactSupport (fun x => fderiv ℝ (dw w f) x (ev j)) exact h.fderiv_apply (𝕜 := ℝ) (ev j)`.
-/
theorem hasCompactSupport_dw {f : E d → ℂ} (hf : HasCompactSupport f) :
    ∀ w : List (Fin d), HasCompactSupport (dw w f)
  | [] => hf
  | j :: w => by
      have h := hasCompactSupport_dw hf w
      show HasCompactSupport (fun x => fderiv ℝ (dw w f) x (ev j))
      exact h.fderiv_apply (𝕜 := ℝ) (ev j)

/- English proof (translation)
Rewrite using `[contDiff_iff_contDiffAt]`. Introduce `x`. Distinguish the cases in `hx : x ∈ U`. Conclude with `(hb.contDiffAt (hU.mem_nhds hx)).mul hφ.contDiffAt`. Establish `hx' : x ∉ tsupport φ` using `fun h => hx (hs h)`.

Establish `h0 : φ =ᶠ[nhds x] fun _ => 0` using `notMem_tsupport_iff_eventuallyEq.mp hx'`. Establish `: (fun y => b y * φ y) =ᶠ[nhds x] fun _ => (0 : ℂ)` using `by filter_upwards [h0] with y hy`. Simplify using `[hy]`. Conclude with `contDiffAt_const.congr_of_eventuallyEq this`.
-/
theorem contDiff_mul_of_on {U : Set (E d)} (hU : IsOpen U) {b φ : E d → ℂ}
    (hb : ContDiffOn ℝ ∞ b U) (hφ : ContDiff ℝ ∞ φ) (hs : tsupport φ ⊆ U) :
    ContDiff ℝ ∞ (fun y => b y * φ y) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact (hb.contDiffAt (hU.mem_nhds hx)).mul hφ.contDiffAt
  · have hx' : x ∉ tsupport φ := fun h => hx (hs h)
    have h0 : φ =ᶠ[nhds x] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp hx'
    have : (fun y => b y * φ y) =ᶠ[nhds x] fun _ => (0 : ℂ) := by
      filter_upwards [h0] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq this

/- English proof (translation)
Unfold `Sys.tr trOp`. Use `integrable_finset_sum _ (fun n _ => integrable_finset_sum _ (fun w _ => ?_))` and prove the remaining obligations. Use `Integrable.const_mul ?_ _` and prove the remaining obligations. Use `Continuous.integrable_of_hasCompactSupport ?_ ?_` and prove the remaining obligations. Conclude with `(contDiff_dw (contDiff_mul_of_on hU (ha i n w) hφ hs) _).continuous`.

Use `hasCompactSupport_dw ?_ _` and prove the remaining obligations. Conclude with `hc.mul_left`.
-/
theorem integrable_tr {ι : Type} (P : Sys d ι) {U : Set (E d)} (hU : IsOpen U)
    (ha : ∀ i n w, ContDiffOn ℝ ∞ (P.a i n w) U) (i : ι) {φ : E d → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) :
    Integrable (P.tr i φ) := by
  unfold Sys.tr trOp
  refine integrable_finset_sum _ (fun n _ => integrable_finset_sum _ (fun w _ => ?_))
  refine Integrable.const_mul ?_ _
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (contDiff_dw (contDiff_mul_of_on hU (ha i n w) hφ hs) _).continuous
  · refine hasCompactSupport_dw ?_ _
    exact hc.mul_left

/- English proof (translation)
Distinguish the cases in `hx : x ∈ U`. Simplify using `only [ext0, hx, dif_pos]`. Conclude with `u.norm_coe_le_norm _`. Simplify using `[ext0, hx]`.
-/
theorem norm_extendByZeroOffSubset_le {U : Set (E d)} (u : U →ᵇ ℂ) (x : E d) : ‖ext0 U u x‖ ≤ ‖u‖ := by
  by_cases hx : x ∈ U
  · simp only [ext0, hx, dif_pos]; exact u.norm_coe_le_norm _
  · simp [ext0, hx]

/- English proof (translation)
Establish `heq : U.indicator (ext0 U u) = ext0 U u`. Apply the tactic sequence `funext x; by_cases hx : x ∈ U <;> simp [ext0, hx]`. Establish `hc : ContinuousOn (ext0 U u) U`. Rewrite using `[continuousOn_iff_continuous_restrict]`. Establish `: U.domRestrict (ext0 U u) = u` using `by funext x; exact dif_pos x.2`.

Rewrite using `[this]`. Conclude with `u.continuous`. Establish `: AEStronglyMeasurable (U.indicator (ext0 U u)) volume` using `(aestronglyMeasurable_indicator_iff hU.measurableSet).mpr (hc.aestronglyMeasurable hU.measurableSet)`. Rewrite `this` using `[heq]`. Then use the resulting hypothesis.
-/
theorem aestronglyMeasurable_extendByZeroOffSubset {U : Set (E d)} (hU : IsOpen U) (u : U →ᵇ ℂ) :
    AEStronglyMeasurable (ext0 U u) volume := by
  have heq : U.indicator (ext0 U u) = ext0 U u := by
    funext x; by_cases hx : x ∈ U <;> simp [ext0, hx]
  have hc : ContinuousOn (ext0 U u) U := by
    rw [continuousOn_iff_continuous_restrict]
    have : U.domRestrict (ext0 U u) = u := by funext x; exact dif_pos x.2
    rw [this]; exact u.continuous
  have : AEStronglyMeasurable (U.indicator (ext0 U u)) volume :=
    (aestronglyMeasurable_indicator_iff hU.measurableSet).mpr (hc.aestronglyMeasurable hU.measurableSet)
  rwa [heq] at this

/- English proof (translation)
The claim follows from `hψ.bdd_mul (aestronglyMeasurable_extendByZeroOffSubset hU u) (Filter.Eventually.of_forall fun x => norm_extendByZeroOffSubset_le u x)`.
-/
theorem integrable_extendByZeroOffSubset_mul {U : Set (E d)} (hU : IsOpen U) (u : U →ᵇ ℂ) {ψ : E d → ℂ}
    (hψ : Integrable ψ) : Integrable (fun x => ext0 U u x * ψ x) :=
  hψ.bdd_mul (aestronglyMeasurable_extendByZeroOffSubset hU u) (Filter.Eventually.of_forall fun x => norm_extendByZeroOffSubset_le u x)

/- English proof (translation)
Apply the tactic sequence `by_cases hx : x ∈ U <;> simp [ext0, hx]`.
-/
theorem matrixExtendByZero_add {U : Set (E d)} (u v : U →ᵇ ℂ) (x : E d) :
    ext0 U (⇑(u + v)) x = ext0 U u x + ext0 U v x := by
  by_cases hx : x ∈ U <;> simp [ext0, hx]

/- English proof (translation)
Apply the tactic sequence `by_cases hx : x ∈ U <;> simp [ext0, hx]`.
-/
theorem extendByZeroOffSubset_smul_apply {U : Set (E d)} (c : ℂ) (u : U →ᵇ ℂ) (x : E d) :
    ext0 U (⇑(c • u)) x = c * ext0 U u x := by
  by_cases hx : x ∈ U <;> simp [ext0, hx]

def pair {U : Set (E d)} (hU : IsOpen U) (ψ : E d → ℂ) (hψ : Integrable ψ) : (U →ᵇ ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun u => ∫ x, ext0 U u x * ψ x
      map_add' := fun u v => by
        simp only [matrixExtendByZero_add, add_mul]
        exact integral_add (integrable_extendByZeroOffSubset_mul hU u hψ) (integrable_extendByZeroOffSubset_mul hU v hψ)
      map_smul' := fun c u => by
        simp only [extendByZeroOffSubset_smul_apply, mul_assoc, RingHom.id_apply, smul_eq_mul]
        exact integral_const_mul c _ }
    (∫ x, ‖ψ x‖) (fun u => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      calc ‖∫ x, ext0 U u x * ψ x‖ ≤ ∫ x, ‖u‖ * ‖ψ x‖ := by
            refine norm_integral_le_of_norm_le (hψ.norm.const_mul _) (Filter.Eventually.of_forall ?_)
            intro x
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right (norm_extendByZeroOffSubset_le u x) (norm_nonneg _)
        _ = (∫ x, ‖ψ x‖) * ‖u‖ := by rw [integral_const_mul, mul_comm])

end GlobalTheory.HCA.SolSub

open GlobalTheory.HCA.SolSub in

/- English proof (translation)
Introduce `d ι P U hU ha`. Establish `hint : ∀ (i : ι) (φ : E d → ℂ) (h : ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U), Integrable (P.tr i φ)` using `fun i φ h => integrable_tr P hU ha i h.1 h.2.1 h.2.2`. Establish `key : ∀ u : U →ᵇ ℂ, u ∈ solSet P U ↔ ∀ (i : ι) (φ : E d → ℂ) (h : ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U), pair hU (P.tr i φ) (hint i φ h) u = 0`. Introduce `u`. Prove the components needed by the constructor for the conclusion.

Introduce `hu i φ h`. Conclude with `hu i φ h.1 h.2.1 h.2.2`. Introduce `hu i φ h1 h2 h3`. Conclude with `hu i φ ⟨h1, h2, h3⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Establish `: solSet P U = ⋂ (i : ι) (φ : E d → ℂ) (h : ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U), {u | pair hU (P.tr i φ) (hint i φ h) u = 0}`. Use extensionality with `u`. Simplify using `only [Set.mem_iInter, Set.mem_setOf_eq]`. Conclude with `key u`. Rewrite using `[this]`.

Conclude with `isClosed_iInter fun i => isClosed_iInter fun φ => isClosed_iInter fun h => isClosed_eq (pair hU (P.tr i φ) (hint i φ h)).continuous continuous_const`. Use `⟨{ carrier := solSet P U, add_mem' := ?_, zero_mem' := zero_mem_solSet P U, smul_mem' := ?_ }, rfl⟩` and prove the remaining obligations. Introduce `u v hu hv`. Rewrite `hu`, `hv`, the goal using `[key]`. Introduce `i φ h`.

Rewrite using `[map_add, hu i φ h, hv i φ h, add_zero]`. Introduce `c u hu`. Rewrite `hu`, the goal using `[key]`. Introduce `i φ h`. Rewrite using `[map_smul, hu i φ h, smul_zero]`.
-/
theorem GlobalTheory.HCA.solSet_closed_submodule :
    ∀ (d : ℕ) (ι : Type) (P : Sys d ι) (U : Set (E d)), IsOpen U → (∀ i n w, ContDiffOn ℝ ∞ (P.a i n w) U) →
      IsClosed (solSet P U) ∧ ∃ S : Submodule ℂ (U →ᵇ ℂ), (S : Set (U →ᵇ ℂ)) = solSet P U := by
  intro d ι P U hU ha
  have hint : ∀ (i : ι) (φ : E d → ℂ) (h : ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U),
      Integrable (P.tr i φ) := fun i φ h => integrable_tr P hU ha i h.1 h.2.1 h.2.2
  have key : ∀ u : U →ᵇ ℂ, u ∈ solSet P U ↔
      ∀ (i : ι) (φ : E d → ℂ) (h : ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U),
        pair hU (P.tr i φ) (hint i φ h) u = 0 := by
    intro u
    constructor
    · intro hu i φ h
      exact hu i φ h.1 h.2.1 h.2.2
    · intro hu i φ h1 h2 h3
      exact hu i φ ⟨h1, h2, h3⟩
  refine ⟨?_, ?_⟩
  · have : solSet P U = ⋂ (i : ι) (φ : E d → ℂ) (h : ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U),
        {u | pair hU (P.tr i φ) (hint i φ h) u = 0} := by
      ext u; simp only [Set.mem_iInter, Set.mem_setOf_eq]; exact key u
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun φ => isClosed_iInter fun h =>
      isClosed_eq (pair hU (P.tr i φ) (hint i φ h)).continuous continuous_const
  · refine ⟨{ carrier := solSet P U, add_mem' := ?_, zero_mem' := zero_mem_solSet P U, smul_mem' := ?_ }, rfl⟩
    · intro u v hu hv
      rw [key] at hu hv ⊢
      intro i φ h
      rw [map_add, hu i φ h, hv i φ h, add_zero]
    · intro c u hu
      rw [key] at hu ⊢
      intro i φ h
      rw [map_smul, hu i φ h, smul_zero]
