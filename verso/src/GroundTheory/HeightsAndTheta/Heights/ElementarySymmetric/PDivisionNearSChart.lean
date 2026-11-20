import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.DivisionSkodaStep
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.PExtNonIntChart
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.PExtension
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDivisionNearSLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
  GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

namespace DivisionNearS

variable {D : ℕ}

/- English proof (translation)
The claim follows from `Classical.choose_spec (A.cover x)`.
-/
theorem mem_source_chartIdx {U : Type} [TopologicalSpace U] (A : FinHolAtlas D U) (x : U) :
    x ∈ (A.chart (chartIdx A x)).source :=
  Classical.choose_spec (A.cover x)

/- English proof (translation)
Use `set G : (Fin D → ℂ) → ℝ≥0∞ := fun z => f c ((A.chart c).symm z)`. Use `set B := piece A j ∩ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) with hBdef`. Set `φ : (Fin D → ℂ) → (Fin D → ℂ)` to `A.chart c ∘ (A.chart j).symm`. Establish `hBmeas : MeasurableSet B` using `(ExtensionProof.measurableSet_piece A j).inter ((A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target hW).measurableSet`. Establish `hBmem : ∀ y ∈ B, y ∈ (A.chart j).target ∧ (A.chart j).symm y ∈ W` using `fun y hy => ⟨hy.2.1, hy.2.2⟩`.

Establish `hderiv : ∀ y ∈ B, HasFDerivWithinAt φ ((fderiv ℂ φ y).restrictScalars ℝ) B y`. Introduce `y hy`. Take `⟨hyt, hyW⟩` from `hBmem y hy`. Establish `han : AnalyticAt ℂ φ y` using `A.holo j c y ⟨hyt, hWc hyW⟩`. Conclude with `(han.differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt`.

Establish `hinj : InjOn φ B`. Introduce `y₁ h₁ y₂ h₂ h`. Take `⟨h₁t, h₁W⟩` from `hBmem y₁ h₁`. Take `⟨h₂t, h₂W⟩` from `hBmem y₂ h₂`. Use `(A.chart c).injOn (hWc h₁W) (hWc h₂W) h` as an intermediate fact.

Rewrite using `[← (A.chart j).right_inv h₁t, ← (A.chart j).right_inv h₂t, this]`. Establish `hcv` using `lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hBmeas hderiv hinj G`. Establish `heq : ∫⁻ y in B, ENNReal.ofReal |((fderiv ℂ φ y).restrictScalars ℝ).det| * G (φ y) = ∫⁻ y in B, f j ((A.chart j).symm y)`. Use `setLIntegral_congr_fun hBmeas fun y hy => ?_` and prove the remaining obligations. Take `⟨hyt, hyW⟩` from `hBmem y hy`.

Establish `hys : (A.chart j).symm y ∈ (A.chart j).source` using `(A.chart j).map_target hyt`. Rewrite using `[hf j _ ⟨hys, hyW⟩, ExtNonInt.det_restrictScalars_complex, abs_of_nonneg (by positivity)]`. Simplify using `only [G, φ, Function.comp_apply, (A.chart c).left_inv (hWc hyW), jac, (A.chart j).right_inv hyt]`. Establish `hsub : φ '' B ⊆ A.chart c '' W`. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Conclude with `⟨(A.chart j).symm y, (hBmem y hy).2, rfl⟩`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem setLIntegral_piece_le_chart {U : Type} [TopologicalSpace U] (A : FinHolAtlas D U)
    (f : Fin A.n → U → ℝ≥0∞) (c : Fin A.n) (W : Set U) (hW : IsOpen W)
    (hWc : W ⊆ (A.chart c).source)
    (hf : ∀ j, ∀ p ∈ (A.chart j).source ∩ W,
      f j p = ENNReal.ofReal (‖jac A j c p‖ ^ 2) * f c p) (j : Fin A.n) :
    ∫⁻ y in piece A j ∩ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W), f j ((A.chart j).symm y) ≤
      ∫⁻ z in A.chart c '' W, f c ((A.chart c).symm z) := by
  set G : (Fin D → ℂ) → ℝ≥0∞ := fun z => f c ((A.chart c).symm z)
  set B := piece A j ∩ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) with hBdef
  let φ : (Fin D → ℂ) → (Fin D → ℂ) := A.chart c ∘ (A.chart j).symm
  have hBmeas : MeasurableSet B := (ExtensionProof.measurableSet_piece A j).inter
    ((A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target hW).measurableSet
  have hBmem : ∀ y ∈ B, y ∈ (A.chart j).target ∧ (A.chart j).symm y ∈ W := fun y hy =>
    ⟨hy.2.1, hy.2.2⟩
  have hderiv : ∀ y ∈ B, HasFDerivWithinAt φ ((fderiv ℂ φ y).restrictScalars ℝ) B y := by
    intro y hy
    obtain ⟨hyt, hyW⟩ := hBmem y hy
    have han : AnalyticAt ℂ φ y := A.holo j c y ⟨hyt, hWc hyW⟩
    exact (han.differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hinj : InjOn φ B := by
    intro y₁ h₁ y₂ h₂ h
    obtain ⟨h₁t, h₁W⟩ := hBmem y₁ h₁
    obtain ⟨h₂t, h₂W⟩ := hBmem y₂ h₂
    have := (A.chart c).injOn (hWc h₁W) (hWc h₂W) h
    rw [← (A.chart j).right_inv h₁t, ← (A.chart j).right_inv h₂t, this]
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hBmeas hderiv hinj G
  have heq : ∫⁻ y in B, ENNReal.ofReal |((fderiv ℂ φ y).restrictScalars ℝ).det| * G (φ y)
      = ∫⁻ y in B, f j ((A.chart j).symm y) := by
    refine setLIntegral_congr_fun hBmeas fun y hy => ?_
    obtain ⟨hyt, hyW⟩ := hBmem y hy
    have hys : (A.chart j).symm y ∈ (A.chart j).source := (A.chart j).map_target hyt
    rw [hf j _ ⟨hys, hyW⟩, ExtNonInt.det_restrictScalars_complex, abs_of_nonneg (by positivity)]
    simp only [G, φ, Function.comp_apply, (A.chart c).left_inv (hWc hyW), jac,
      (A.chart j).right_inv hyt]
  have hsub : φ '' B ⊆ A.chart c '' W := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨(A.chart j).symm y, (hBmem y hy).2, rfl⟩
  calc ∫⁻ y in B, f j ((A.chart j).symm y) = ∫⁻ z in φ '' B, G z := by rw [hcv, heq]
    _ ≤ ∫⁻ z in A.chart c '' W, G z := lintegral_mono_set hsub

variable (X : EmbDatum D)

/- English proof (translation)
Use `(X.e_mem k).2.1 j c x hx` as an intermediate fact. Simplify using `using this`.
-/
theorem e_transform (k : Fin X.N) (j c : Fin X.A.n) (x : X.U)
    (hx : x ∈ (X.A.chart j).source ∩ (X.A.chart c).source) :
    X.e k j x = X.L.g j c x * X.e k c x := by
  have := (X.e_mem k).2.1 j c x hx
  simpa using this

/- English proof (translation)
Simplify using `[lin, Finset.sum_apply]`.
-/
theorem lin_apply (a : Fin X.N → ℂ) (j : Fin X.A.n) (x : X.U) :
    lin X.e a j x = ∑ k, a k * X.e k j x := by
  simp [lin, Finset.sum_apply]

/- English proof (translation)
Simplify using `only [ZeroDatum.s, lin_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[e_transform X k j c x hx]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem s_transform (Z : ZeroDatum X) (i : Fin D) (j c : Fin X.A.n) (x : X.U)
    (hx : x ∈ (X.A.chart j).source ∩ (X.A.chart c).source) :
    Z.s i j x = X.L.g j c x * Z.s i c x := by
  simp only [ZeroDatum.s, lin_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [e_transform X k j c x hx]; ring

/- English proof (translation)
Use `show lin X.e (Z.c i) ∈ X.L.sections 1`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (X.e_mem k)`.
-/
theorem s_mem (Z : ZeroDatum X) (i : Fin D) : Z.s i ∈ X.L.sections 1 := by
  show lin X.e (Z.c i) ∈ X.L.sections 1
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (X.e_mem k)

/- English proof (translation)
Take `⟨k, hk⟩` from `X.gen x`. Establish `hc` using `mem_source_chartIdx X.A x`. Establish `hg` using `X.L.ne_zero j (chartIdx X.A x) x ⟨hx, hc⟩`. Establish `hne : X.e k j x ≠ 0`. Rewrite using `[e_transform X k j (chartIdx X.A x) x ⟨hx, hc⟩]`.

Conclude with `mul_ne_zero hg hk`. Conclude with `lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun k => ‖X.e k j x‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ k))`.
-/
theorem esum_pos (j : Fin X.A.n) (x : X.U) (hx : x ∈ (X.A.chart j).source) :
    0 < ∑ k, ‖X.e k j x‖ ^ 2 := by
  obtain ⟨k, hk⟩ := X.gen x
  have hc := mem_source_chartIdx X.A x
  have hg := X.L.ne_zero j (chartIdx X.A x) x ⟨hx, hc⟩
  have hne : X.e k j x ≠ 0 := by
    rw [e_transform X k j (chartIdx X.A x) x ⟨hx, hc⟩]; exact mul_ne_zero hg hk
  exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun k => ‖X.e k j x‖ ^ 2)
    (fun _ _ => by positivity) (Finset.mem_univ k))

/- English proof (translation)
Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[e_transform X k j c x hx, norm_mul, mul_pow]`.
-/
theorem esum_transform (j c : Fin X.A.n) (x : X.U)
    (hx : x ∈ (X.A.chart j).source ∩ (X.A.chart c).source) :
    ∑ k, ‖X.e k j x‖ ^ 2 = ‖X.L.g j c x‖ ^ 2 * ∑ k, ‖X.e k c x‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [e_transform X k j c x hx, norm_mul, mul_pow]

/- English proof (translation)
Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[s_transform X Z i j c x hx, norm_mul, mul_pow]`.
-/
theorem ssum_transform (Z : ZeroDatum X) (j c : Fin X.A.n) (x : X.U)
    (hx : x ∈ (X.A.chart j).source ∩ (X.A.chart c).source) :
    ∑ i, ‖Z.s i j x‖ ^ 2 = ‖X.L.g j c x‖ ^ 2 * ∑ i, ‖Z.s i c x‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [s_transform X Z i j c x hx, norm_mul, mul_pow]

/- English proof (translation)
Unfold `rSq`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Establish `h1 : ‖Z.s i j x‖ ≤ ∑ k, ‖Z.c i k‖ * ‖X.e k j x‖`. Simplify using `only [ZeroDatum.s, lin_apply]`.

Conclude with `(norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => norm_mul _ _))`. Establish `h2` using `Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖Z.c i k‖) (fun k => ‖X.e k j x‖)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ssum_le (Z : ZeroDatum X) (j : Fin X.A.n) (x : X.U) :
    ∑ i, ‖Z.s i j x‖ ^ 2 ≤ rSq Z.c * ∑ k, ‖X.e k j x‖ ^ 2 := by
  unfold rSq
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖Z.s i j x‖ ≤ ∑ k, ‖Z.c i k‖ * ‖X.e k j x‖ := by
    simp only [ZeroDatum.s, lin_apply]
    exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => norm_mul _ _))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖Z.c i k‖)
    (fun k => ‖X.e k j x‖)
  calc ‖Z.s i j x‖ ^ 2 ≤ (∑ k, ‖Z.c i k‖ * ‖X.e k j x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

end DivisionNearS

end

end GroundTheory.Heights₂.Heights.EffectiveHS
