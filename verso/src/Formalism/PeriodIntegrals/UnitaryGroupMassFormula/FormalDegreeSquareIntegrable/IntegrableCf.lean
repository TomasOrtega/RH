import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeSquareIntegrable.FormalDegreeFromOrthogonality

noncomputable section

namespace PIW.HCFdeg

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

section Orth

variable {G : Type} [Group G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def cf (π : G →* (H →L[ℂ] H)) (v w : H) : G → ℂ := fun g => ⟪w, π g v⟫_ℂ

def cfL (π : G →* (H →L[ℂ] H)) (w : H) : H →ₗ[ℂ] (G → ℂ) where
  toFun v := cf π v w
  map_add' a b := by funext g; simp [cf]
  map_smul' c a := by funext g; simp [cf]

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma cfL_apply (π : G →* (H →L[ℂ] H)) (w v : H) : cfL π w v = cf π v w := rfl

/- English proof (translation)
Set `L : H →ₗᵢ[ℂ] H` to `{ toLinearMap := (π g).toLinearMap, norm_map' := hiso g }`. Conclude with `L.inner_map_map x y`.
-/
lemma inner_pi (π : G →* (H →L[ℂ] H)) (hiso : ∀ g v, ‖π g v‖ = ‖v‖) (g : G) (x y : H) :
    ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ := by
  let L : H →ₗᵢ[ℂ] H := { toLinearMap := (π g).toLinearMap, norm_map' := hiso g }
  exact L.inner_map_map x y

/- English proof (translation)
Rewrite using `[map_mul, ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply (π h), ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]`.
-/
lemma pi_mul_inv (π : G →* (H →L[ℂ] H)) (g h : G) (x : H) : π (g * h) (π h⁻¹ x) = π g x := by
  rw [map_mul, ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply (π h), ← map_mul, mul_inv_cancel, map_one,
    ContinuousLinearMap.one_apply]

/- English proof (translation)
Establish `hv : π g (π g⁻¹ v) = v`. Rewrite using `[← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]`. Rewrite using `[← inner_pi π hiso g w (π g⁻¹ v), hv]`. Conclude with `(inner_conj_symm _ _).symm`.
-/
lemma pi_inv (π : G →* (H →L[ℂ] H)) (hiso : ∀ g v, ‖π g v‖ = ‖v‖) (g : G) (v w : H) :
    ⟪w, π g⁻¹ v⟫_ℂ = star ⟪v, π g w⟫_ℂ := by
  have hv : π g (π g⁻¹ v) = v := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]
  rw [← inner_pi π hiso g w (π g⁻¹ v), hv]
  exact (inner_conj_symm _ _).symm

variable [MeasurableSpace G] {μ : Measure G}

/- English proof (translation)
Conclude with `(hL2 v w).integrable_mul (p := 2) (q := 2) (hL2 v' w').star`.
-/
lemma integrable_cf (π : G →* (H →L[ℂ] H)) (hL2 : ∀ v w : H, MemLp (cf π v w) 2 μ) (v w v' w' : H) :
    Integrable (fun g => cf π v w g * star (cf π v' w' g)) μ := by
  exact (hL2 v w).integrable_mul (p := 2) (q := 2) (hL2 v' w').star

end Orth

/- English proof (translation)
Introduce `hSchur hBdd G _ _ _ _ _ _ _ μ _ _ _ H _ _ _ _ π hiso hcont hirr hL2`. Establish `hcv : ∀ (w : H) (g : G), Continuous fun v => cfL π w v g` using `fun w g => by show Continuous fun v => ⟪w, π g v⟫_ℂ`. Conclude with `continuous_const.inner (π g).continuous`. Use `choose T hT using fun w : H => hBdd G H μ (cfL π w) (hcv w) (fun v => hL2 v w)`. Set `B : H → H → H → H → ℂ` to `fun v w v' w' => ∫ g, cf π v w g * star (cf π v' w' g) ∂μ`.

Establish `hBT : ∀ v w v' w', B v w v' w' = ⟪v', (T w').adjoint (T w v)⟫_ℂ`. Introduce `v w v' w'`. Rewrite using `[ContinuousLinearMap.adjoint_inner_right, MeasureTheory.L2.inner_def]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hT w v, hT w' v'] with g h1 h2`.

Rewrite using `[h1, h2]`. Simplify using `[cfL_apply, RCLike.inner_apply, mul_comm]`. Establish `hpiadj : ∀ (h : G) (x y : H), ⟪π h⁻¹ x, y⟫_ℂ = ⟪x, π h y⟫_ℂ`. Introduce `h x y`. Rewrite using `[← inner_pi π hiso h (π h⁻¹ x) y, ← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]`.

Establish `hshift : ∀ (h : G) v w v' w', B (π h v) w v' w' = B v w (π h⁻¹ v') w'`. Introduce `h v w v' w'`. Use `show ∫ g, cf π (π h v) w g * star (cf π v' w' g) ∂μ = ∫ g, cf π v w g * star (cf π (π h⁻¹ v') w' g) ∂μ`. Use `conv_rhs => rw [← integral_mul_right_eq_self _ h]`. Use `congr 1`.

Use function extensionality and compare the values at `g`. Simplify using `only [cf]`. Rewrite using `[pi_mul_inv, map_mul, ContinuousLinearMap.mul_apply]`. Establish `hcomm : ∀ w w' (h : G), ((T w').adjoint ∘L T w) ∘L π h = π h ∘L ((T w').adjoint ∘L T w)`. Introduce `w w' h`.

Use `ContinuousLinearMap.ext fun v => ?_` and prove the remaining obligations. Apply `ext_inner_left ℂ` to reduce the goal to its premises. Introduce `v'`. Simplify using `only [ContinuousLinearMap.comp_apply]`. Rewrite using `[← hBT, hshift, hBT, hpiadj]`.

Use `choose c hc using fun w w' : H => hSchur G H π hiso hirr _ (hcomm w w')`. Establish `hBc : ∀ v w v' w', B v w v' w' = c w w' * ⟪v', v⟫_ℂ`. Introduce `v w v' w'`. Rewrite using `[hBT]`. Establish `e` using `congrArg (fun A : H →L[ℂ] H => A v) (hc w w')`.

Simplify using `only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] at e`. Rewrite using `[e, inner_smul_right]`. Establish `hcfinv : ∀ v w g, cf π v w g = star (cf π w v g⁻¹)`. Introduce `v w g`. Establish `e` using `pi_inv π hiso g⁻¹ v w`.

Rewrite `e` using `[inv_inv]`. Conclude with `e`. Establish `hBsymm : ∀ v w v' w', B v w v' w' = conj (B w v w' v')`. Introduce `v w v' w'`. Use `show ∫ g, cf π v w g * star (cf π v' w' g) ∂μ = conj (∫ g, cf π w v g * star (cf π w' v' g) ∂μ)`.

Rewrite using `[← integral_conj]`. Use `conv_rhs => rw [← integral_inv_eq_self _ μ]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Rewrite using `[hcfinv v w g, hcfinv v' w' g]`.

Simplify using `[RCLike.star_def, map_mul]`. Establish `hrel : ∀ v w v' w', c w w' * ⟪v', v⟫_ℂ = conj (c v v') * ⟪w, w'⟫_ℂ`. Introduce `v w v' w'`. Rewrite using `[← hBc, hBsymm, hBc, map_mul, inner_conj_symm]`. Take `⟨x0, hx0⟩` from `exists_ne (0 : H)`.

Use `set e : H := ((‖x0‖ : ℂ))⁻¹ • x0 with he`. Establish `hn : ‖e‖ = 1`. Rewrite using `[he]`. Conclude with `norm_smul_inv_norm hx0`. Establish `hee : ⟪e, e⟫_ℂ = 1`.

Rewrite using `[inner_self_eq_norm_sq_to_K, hn]`. Simplify using the standard rewrite rules. Establish `hne : e ≠ 0`. Introduce `h0`. Rewrite `hn` using `[h0, norm_zero]`.

Conclude with `zero_ne_one hn`. Set `φ : G → ℝ` to `fun g => Complex.normSq (cf π e e g)`. Establish `hφc : Continuous φ` using `Complex.continuous_normSq.comp (continuous_const.inner (hcont e))`. Establish `hBφ : B e e e e = ((∫ g, φ g ∂μ : ℝ) : ℂ)` using `by show ∫ g, cf π e e g * star (cf π e e g) ∂μ = _`. Rewrite using `[← integral_complex_ofReal]`.

Use `congr 1`. Use function extensionality and compare the values at `g`. Simplify using `only [φ, RCLike.star_def, Complex.mul_conj]`. Establish `hφi : Integrable φ μ`. Establish `h2` using `(memLp_two_iff_integrable_sq_norm (hL2 e e).1).mp (hL2 e e)`.

Use `h2.congr (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Simplify using `only [φ, cf, Complex.normSq_eq_norm_sq]`. Establish `hφpos : 0 < ∫ g, φ g ∂μ`. Rewrite using `[integral_pos_iff_support_of_nonneg (fun g => Complex.normSq_nonneg _) hφi]`. Apply `hφc.isOpen_support.measure_pos μ` to reduce the goal to its premises.

Use `⟨1, ?_⟩` and prove the remaining obligations. Simplify using `[φ, cf, hee, hne]`. Use `⟨(∫ g, φ g ∂μ)⁻¹, inv_pos.mpr hφpos, fun v w v' w' => ⟨integrable_cf π hL2 v w v' w', ?_⟩⟩` and prove the remaining obligations. Establish `hκ : conj (c e e) = ((∫ g, φ g ∂μ : ℝ) : ℂ)`. Establish `h1` using `hBc e e e e`.

Rewrite `h1` using `[hee, mul_one]`. Establish `h2` using `hrel e e e e`. Rewrite `h2` using `[hee, mul_one, mul_one]`. Rewrite using `[← h2, ← h1, hBφ]`. Establish `hcw : c w w' = conj (c e e) * ⟪w, w'⟫_ℂ`.

Establish `h3` using `hrel e w e w'`. Rewrite `h3` using `[hee, mul_one]`. Then use the resulting hypothesis. Use `show B v w v' w' = _`. Rewrite using `[hBc, hcw, hκ, Complex.ofReal_inv, div_inv_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem stOrthOf : StOrthOf := by
  intro hSchur hBdd G _ _ _ _ _ _ _ μ _ _ _ H _ _ _ _ π hiso hcont hirr hL2
  have hcv : ∀ (w : H) (g : G), Continuous fun v => cfL π w v g := fun w g => by
    show Continuous fun v => ⟪w, π g v⟫_ℂ
    exact continuous_const.inner (π g).continuous
  choose T hT using fun w : H => hBdd G H μ (cfL π w) (hcv w) (fun v => hL2 v w)
  let B : H → H → H → H → ℂ := fun v w v' w' => ∫ g, cf π v w g * star (cf π v' w' g) ∂μ
  have hBT : ∀ v w v' w', B v w v' w' = ⟪v', (T w').adjoint (T w v)⟫_ℂ := by
    intro v w v' w'
    rw [ContinuousLinearMap.adjoint_inner_right, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hT w v, hT w' v'] with g h1 h2
    rw [h1, h2]
    simp [cfL_apply, RCLike.inner_apply, mul_comm]
  have hpiadj : ∀ (h : G) (x y : H), ⟪π h⁻¹ x, y⟫_ℂ = ⟪x, π h y⟫_ℂ := by
    intro h x y
    rw [← inner_pi π hiso h (π h⁻¹ x) y, ← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply]
  have hshift : ∀ (h : G) v w v' w', B (π h v) w v' w' = B v w (π h⁻¹ v') w' := by
    intro h v w v' w'
    show ∫ g, cf π (π h v) w g * star (cf π v' w' g) ∂μ = ∫ g, cf π v w g * star (cf π (π h⁻¹ v') w' g) ∂μ
    conv_rhs => rw [← integral_mul_right_eq_self _ h]
    congr 1
    funext g
    simp only [cf]
    rw [pi_mul_inv, map_mul, ContinuousLinearMap.mul_apply]
  have hcomm : ∀ w w' (h : G), ((T w').adjoint ∘L T w) ∘L π h = π h ∘L ((T w').adjoint ∘L T w) := by
    intro w w' h
    refine ContinuousLinearMap.ext fun v => ?_
    apply ext_inner_left ℂ
    intro v'
    simp only [ContinuousLinearMap.comp_apply]
    rw [← hBT, hshift, hBT, hpiadj]
  choose c hc using fun w w' : H => hSchur G H π hiso hirr _ (hcomm w w')
  have hBc : ∀ v w v' w', B v w v' w' = c w w' * ⟪v', v⟫_ℂ := by
    intro v w v' w'
    rw [hBT]
    have e := congrArg (fun A : H →L[ℂ] H => A v) (hc w w')
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] at e
    rw [e, inner_smul_right]
  have hcfinv : ∀ v w g, cf π v w g = star (cf π w v g⁻¹) := by
    intro v w g
    have e := pi_inv π hiso g⁻¹ v w
    rw [inv_inv] at e
    exact e
  have hBsymm : ∀ v w v' w', B v w v' w' = conj (B w v w' v') := by
    intro v w v' w'
    show ∫ g, cf π v w g * star (cf π v' w' g) ∂μ = conj (∫ g, cf π w v g * star (cf π w' v' g) ∂μ)
    rw [← integral_conj]
    conv_rhs => rw [← integral_inv_eq_self _ μ]
    congr 1
    funext g
    rw [hcfinv v w g, hcfinv v' w' g]
    simp [RCLike.star_def, map_mul]
  have hrel : ∀ v w v' w', c w w' * ⟪v', v⟫_ℂ = conj (c v v') * ⟪w, w'⟫_ℂ := by
    intro v w v' w'
    rw [← hBc, hBsymm, hBc, map_mul, inner_conj_symm]
  obtain ⟨x0, hx0⟩ := exists_ne (0 : H)
  set e : H := ((‖x0‖ : ℂ))⁻¹ • x0 with he
  have hn : ‖e‖ = 1 := by
    rw [he]
    exact norm_smul_inv_norm hx0
  have hee : ⟪e, e⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hn]
    simp
  have hne : e ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  let φ : G → ℝ := fun g => Complex.normSq (cf π e e g)
  have hφc : Continuous φ := Complex.continuous_normSq.comp (continuous_const.inner (hcont e))
  have hBφ : B e e e e = ((∫ g, φ g ∂μ : ℝ) : ℂ) := by
    show ∫ g, cf π e e g * star (cf π e e g) ∂μ = _
    rw [← integral_complex_ofReal]
    congr 1
    funext g
    simp only [φ, RCLike.star_def, Complex.mul_conj]
  have hφi : Integrable φ μ := by
    have h2 := (memLp_two_iff_integrable_sq_norm (hL2 e e).1).mp (hL2 e e)
    refine h2.congr (Filter.Eventually.of_forall fun g => ?_)
    simp only [φ, cf, Complex.normSq_eq_norm_sq]
  have hφpos : 0 < ∫ g, φ g ∂μ := by
    rw [integral_pos_iff_support_of_nonneg (fun g => Complex.normSq_nonneg _) hφi]
    apply hφc.isOpen_support.measure_pos μ
    refine ⟨1, ?_⟩
    simp [φ, cf, hee, hne]
  refine ⟨(∫ g, φ g ∂μ)⁻¹, inv_pos.mpr hφpos, fun v w v' w' => ⟨integrable_cf π hL2 v w v' w', ?_⟩⟩
  have hκ : conj (c e e) = ((∫ g, φ g ∂μ : ℝ) : ℂ) := by
    have h1 := hBc e e e e
    rw [hee, mul_one] at h1
    have h2 := hrel e e e e
    rw [hee, mul_one, mul_one] at h2
    rw [← h2, ← h1, hBφ]
  have hcw : c w w' = conj (c e e) * ⟪w, w'⟫_ℂ := by
    have h3 := hrel e w e w'
    rwa [hee, mul_one] at h3
  show B v w v' w' = _
  rw [hBc, hcw, hκ, Complex.ofReal_inv, div_inv_eq_mul]
  ring

end PIW.HCFdeg
