import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FrameMeasStatementPfA

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FM

open NumberField Matrix MeasureTheory Topology ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open scoped ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

/- English proof (translation)
Introduce `a b hab`. Establish `h : b < a` using `hab`. Simplify using `[Umat, h]`.
-/
theorem Umat_upper (y : UpI X.Ψ r → ℂ) (τ : X.Ψ) : (Umat y τ).BlockTriangular id := by
  intro a b hab
  have h : b < a := hab
  simp [Umat, h]

/- English proof (translation)
Use `set x := rmul p (UF X y) with hxdef`. Use `set τ := i.1.1`. Establish `hxd : x ∈ X.dom` using `hCd hx`. Establish `h1 : gram τ.1 X.Gm (mat x τ) = gramT X (β0 X p τ * mat (UF X y) τ)` using `gram_rmul_eq X hp τ`. Set `one : Frame X.Ψ r` to `fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)`.

Establish `hone' : rmul x one = x`. Use function extensionality and compare the values at `τ'`. Use `show (mat x τ' * (1 : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = x τ'`. Rewrite using `[Matrix.mul_one]`. Both sides reduce to the same expression.

Establish `h2 : gram τ.1 X.Gm (mat x τ) = gramT X (β0 X x τ * mat one τ)`. Use `gram_rmul_eq X hxd τ (b := one)` as an intermediate fact. Rewrite `this` using `[hone']`. Then use the resulting hypothesis. Establish `hone : mat one τ = 1` using `rfl`. Rewrite `h2` using `[hone, Matrix.mul_one]`.

Establish `hU : mat (UF X y) τ = Umat y τ` using `rfl`. Rewrite `h1` using `[hU]`. Establish `hUd : (Umat y τ).det ≠ 0` using `((UF_mem X hy) τ).1`. Take `⟨D, hD, heq⟩` from `gram_upper_unique (ε := fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (fun a => sgn_mul_self X.p0 a) (β0_upper X hxd τ) ((β0_upper X hp τ).mul (Umat_upper X y τ)) (β0_det X hxd τ) (by rw [Matrix.det_mul]; exact mul_ne_zero (β0_det X hp τ) hUd) (by have := h1.symm.trans h2; simpa …`. Establish `hval : Lβ (β0 X p) y i = (β0 X p τ * Umat y τ) i.1.2.1 i.1.2.2` using `rfl`.

Rewrite using `[hval, heq, Matrix.diagonal_mul, norm_mul, hD, one_mul]`. Conclude with `hR0 x hx τ _ _`.
-/
theorem Lβ_bound {C : Set (Frame X.Ψ r)} (hCd : C ⊆ X.dom) {R0 : ℝ}
    (hR0 : ∀ x ∈ C, ∀ τ a b, ‖β0 X x τ a b‖ ≤ R0) {p : Frame X.Ψ r} (hp : p ∈ X.dom)
    {y : UpI X.Ψ r → ℂ} (hy : ∀ τ b, y (dI τ b) ≠ 0) (hx : rmul p (UF X y) ∈ C) (i : UpI X.Ψ r) :
    ‖Lβ (β0 X p) y i‖ ≤ R0 := by
  set x := rmul p (UF X y) with hxdef
  set τ := i.1.1
  have hxd : x ∈ X.dom := hCd hx
  have h1 : gram τ.1 X.Gm (mat x τ) = gramT X (β0 X p τ * mat (UF X y) τ) := gram_rmul_eq X hp τ
  let one : Frame X.Ψ r := fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)
  have hone' : rmul x one = x := by
    funext τ'
    show (mat x τ' * (1 : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = x τ'
    rw [Matrix.mul_one]; rfl
  have h2 : gram τ.1 X.Gm (mat x τ) = gramT X (β0 X x τ * mat one τ) := by
    have := gram_rmul_eq X hxd τ (b := one)
    rwa [hone'] at this
  have hone : mat one τ = 1 := rfl
  rw [hone, Matrix.mul_one] at h2
  have hU : mat (UF X y) τ = Umat y τ := rfl
  rw [hU] at h1
  have hUd : (Umat y τ).det ≠ 0 := ((UF_mem X hy) τ).1
  obtain ⟨D, hD, heq⟩ := gram_upper_unique (ε := fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))
    (fun a => sgn_mul_self X.p0 a) (β0_upper X hxd τ) ((β0_upper X hp τ).mul (Umat_upper X y τ))
    (β0_det X hxd τ) (by rw [Matrix.det_mul]; exact mul_ne_zero (β0_det X hp τ) hUd)
    (by have := h1.symm.trans h2; simpa only [gramT, Jd] using this)
  have hval : Lβ (β0 X p) y i = (β0 X p τ * Umat y τ) i.1.2.1 i.1.2.2 := rfl
  rw [hval, heq, Matrix.diagonal_mul, norm_mul, hD, one_mul]
  exact hR0 x hx τ _ _

def SR (R0 : ℝ) : Set (UpI X.Ψ r → ℂ) := {c | ∀ i, ‖c i‖ ≤ R0}

def KR (R0 : ℝ) : ℝ≥0∞ := ∫⁻ y in SR X R0, ENNReal.ofReal (Complex.normSq (jacU y))

/- English proof (translation)
Establish `h : SR X R0 = ⋂ i, {c : UpI X.Ψ r → ℂ | ‖c i‖ ≤ R0}`. Use extensionality with `c`. Simplify using `[SR]`. Rewrite using `[h]`. Conclude with `MeasurableSet.iInter fun i => measurableSet_le (measurable_pi_apply i).norm measurable_const`.
-/
theorem measurableSet_SR (R0 : ℝ) : MeasurableSet (SR X R0) := by
  have h : SR X R0 = ⋂ i, {c : UpI X.Ψ r → ℂ | ‖c i‖ ≤ R0} := by
    ext c
    simp [SR]
  rw [h]
  exact MeasurableSet.iInter fun i => measurableSet_le (measurable_pi_apply i).norm measurable_const

/- English proof (translation)
Establish `hc : IsCompact (SR X R0)`. Establish `h : SR X R0 = Set.pi Set.univ (fun _ => Metric.closedBall (0 : ℂ) R0)`. Use extensionality with `c`. Simplify using `[SR, Set.mem_pi]`. Rewrite using `[h]`.

Conclude with `isCompact_univ_pi fun _ => isCompact_closedBall 0 R0`. Take `⟨C, hC⟩` from `hc.exists_bound_of_continuousOn ((Complex.continuous_normSq.comp continuous_jacU).continuousOn)`. Combine the equalities or inequalities in the displayed calculation. Unfold `KR`. Use `setLIntegral_mono measurable_const fun y hy => ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations.

Use `hC y hy` as an intermediate fact. Rewrite `this` using `[Real.norm_eq_abs]`. Conclude with `le_trans (le_abs_self _) this`. Use `_ = ENNReal.ofReal C * volume (SR X R0) := setLIntegral_const _ _`. Use `_ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hc.measure_lt_top`.
-/
theorem KR_lt_top {R0 : ℝ} (hR0 : 0 ≤ R0) : KR X R0 < ⊤ := by
  have hc : IsCompact (SR X R0) := by
    have h : SR X R0 = Set.pi Set.univ (fun _ => Metric.closedBall (0 : ℂ) R0) := by
      ext c
      simp [SR, Set.mem_pi]
    rw [h]
    exact isCompact_univ_pi fun _ => isCompact_closedBall 0 R0
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn
    ((Complex.continuous_normSq.comp continuous_jacU).continuousOn)
  calc KR X R0 ≤ ∫⁻ _ in SR X R0, ENNReal.ofReal C := by
        unfold KR
        refine setLIntegral_mono measurable_const fun y hy => ENNReal.ofReal_le_ofReal ?_
        have := hC y hy
        rw [Real.norm_eq_abs] at this
        exact le_trans (le_abs_self _) this
    _ = ENNReal.ofReal C * volume (SR X R0) := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hc.measure_lt_top

/- English proof (translation)
Establish `hdet : LinearMap.det (Lβ β) ≠ 0` using `det_Lβ_ne β hβ hd`. Establish `hjac : jacβ β ≠ 0`. Unfold `jacβ`. Use `Finset.prod_ne_zero_iff.2 fun i _ => ?_` and prove the remaining obligations. Use `split_ifs`.

Conclude with `hd _ _`. Conclude with `one_ne_zero`. Establish `hnj : 0 < Complex.normSq (jacβ β)` using `Complex.normSq_pos.2 hjac`. Establish `hnd : 0 < Complex.normSq (LinearMap.det (Lβ β))` using `Complex.normSq_pos.2 hdet`. Set `Lr : (UpI X.Ψ r → ℂ) →ₗ[ℝ] (UpI X.Ψ r → ℂ)` to `(Lβ β).restrictScalars ℝ`.

Establish `hdetr : LinearMap.det Lr = Complex.normSq (LinearMap.det (Lβ β))`. Rewrite using `[LinearMap.det_restrictScalars, Algebra.norm_complex_apply]`. Establish `hdetr0 : LinearMap.det Lr ≠ 0` using `by rw [hdetr]; exact hnd.ne'`. Establish `hmap` using `MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (UpI X.Ψ r → ℂ)) hdetr0`. Establish `hSm : MeasurableSet (SR X R0)` using `measurableSet_SR X R0`.

Set `c : ℝ≥0∞` to `ENNReal.ofReal ((Complex.normSq (jacβ β))⁻¹)`. Set `G : (UpI X.Ψ r → ℂ) → ℝ≥0∞` to `fun u => ENNReal.ofReal (Complex.normSq (jacU u)) * c * (SR X R0).indicator 1 u`. Establish `hG : Measurable G` using `(measurable_normSq_jacU.mul_const c).mul (measurable_one.indicator hSm)`. Establish `hLm : Measurable Lr` using `Lr.continuous_of_finiteDimensional.measurable`. Establish `hpt : ∀ y, ENNReal.ofReal (Complex.normSq (jacU y)) * (SR X R0).indicator 1 (Lβ β y) = G (Lr y)`.

Introduce `y`. Establish `e : ENNReal.ofReal (Complex.normSq (jacβ β * jacU y)) * c = ENNReal.ofReal (Complex.normSq (jacU y))`. Rewrite using `[Complex.normSq_mul, ← ENNReal.ofReal_mul (mul_nonneg hnj.le (Complex.normSq_nonneg _))]`. Use `congr 1`. Rewrite using `[mul_right_comm, mul_inv_cancel₀ hnj.ne', one_mul]`.

Use `show _ = ENNReal.ofReal (Complex.normSq (jacU (Lβ β y))) * c * (SR X R0).indicator 1 (Lβ β y)`. Rewrite using `[jacU_Lβ β hβ y, e]`. Establish `hGi : ∫⁻ u, G u = KR X R0 * c`. Establish `h : G = (SR X R0).indicator (fun u => ENNReal.ofReal (Complex.normSq (jacU u)) * c)`. Use function extensionality and compare the values at `u`.

Simplify using `only [G, Set.indicator]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[h, lintegral_indicator hSm, lintegral_mul_const _ measurable_normSq_jacU]`. Both sides reduce to the same expression. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hmap, lintegral_smul_measure, smul_eq_mul]`. Use `_ = _ := by`. Rewrite using `[hGi, hdetr, abs_of_pos (inv_pos.2 hnd), mul_inv, ENNReal.ofReal_mul (inv_pos.2 hnd).le]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem upper_gen (β : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (hβ : ∀ τ, (β τ).BlockTriangular id)
    (hd : ∀ τ b, β τ b b ≠ 0) (R0 : ℝ) :
    ∫⁻ y, ENNReal.ofReal (Complex.normSq (jacU y)) * (SR X R0).indicator 1 (Lβ β y) =
      ENNReal.ofReal ((Complex.normSq (LinearMap.det (Lβ β)) * Complex.normSq (jacβ β))⁻¹) * KR X R0 := by
  have hdet : LinearMap.det (Lβ β) ≠ 0 := det_Lβ_ne β hβ hd
  have hjac : jacβ β ≠ 0 := by
    unfold jacβ
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    split_ifs
    · exact hd _ _
    · exact one_ne_zero
  have hnj : 0 < Complex.normSq (jacβ β) := Complex.normSq_pos.2 hjac
  have hnd : 0 < Complex.normSq (LinearMap.det (Lβ β)) := Complex.normSq_pos.2 hdet
  let Lr : (UpI X.Ψ r → ℂ) →ₗ[ℝ] (UpI X.Ψ r → ℂ) := (Lβ β).restrictScalars ℝ
  have hdetr : LinearMap.det Lr = Complex.normSq (LinearMap.det (Lβ β)) := by
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
  have hdetr0 : LinearMap.det Lr ≠ 0 := by rw [hdetr]; exact hnd.ne'
  have hmap := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (UpI X.Ψ r → ℂ)) hdetr0
  have hSm : MeasurableSet (SR X R0) := measurableSet_SR X R0
  let c : ℝ≥0∞ := ENNReal.ofReal ((Complex.normSq (jacβ β))⁻¹)
  let G : (UpI X.Ψ r → ℂ) → ℝ≥0∞ := fun u =>
    ENNReal.ofReal (Complex.normSq (jacU u)) * c * (SR X R0).indicator 1 u
  have hG : Measurable G :=
    (measurable_normSq_jacU.mul_const c).mul (measurable_one.indicator hSm)
  have hLm : Measurable Lr := Lr.continuous_of_finiteDimensional.measurable
  have hpt : ∀ y, ENNReal.ofReal (Complex.normSq (jacU y)) * (SR X R0).indicator 1 (Lβ β y) =
      G (Lr y) := by
    intro y
    have e : ENNReal.ofReal (Complex.normSq (jacβ β * jacU y)) * c =
        ENNReal.ofReal (Complex.normSq (jacU y)) := by
      rw [Complex.normSq_mul, ← ENNReal.ofReal_mul (mul_nonneg hnj.le (Complex.normSq_nonneg _))]
      congr 1
      rw [mul_right_comm, mul_inv_cancel₀ hnj.ne', one_mul]
    show _ = ENNReal.ofReal (Complex.normSq (jacU (Lβ β y))) * c * (SR X R0).indicator 1 (Lβ β y)
    rw [jacU_Lβ β hβ y, e]
  have hGi : ∫⁻ u, G u = KR X R0 * c := by
    have h : G = (SR X R0).indicator (fun u => ENNReal.ofReal (Complex.normSq (jacU u)) * c) := by
      funext u
      simp only [G, Set.indicator]
      split_ifs <;> simp
    rw [h, lintegral_indicator hSm, lintegral_mul_const _ measurable_normSq_jacU]
    rfl
  calc ∫⁻ y, ENNReal.ofReal (Complex.normSq (jacU y)) * (SR X R0).indicator 1 (Lβ β y)
      = ∫⁻ y, G (Lr y) := lintegral_congr fun y => hpt y
    _ = ∫⁻ u, G u ∂(Measure.map Lr volume) := (lintegral_map hG hLm).symm
    _ = ENNReal.ofReal |(LinearMap.det Lr)⁻¹| * ∫⁻ u, G u := by
        rw [hmap, lintegral_smul_measure, smul_eq_mul]
    _ = _ := by
        rw [hGi, hdetr, abs_of_pos (inv_pos.2 hnd), mul_inv, ENNReal.ofReal_mul (inv_pos.2 hnd).le]
        ring

def Jp (C : Set (Frame X.Ψ r)) (p : Frame X.Ψ r) : ℝ≥0∞ :=
  ∫⁻ y, (if ∀ τ b, y (dI τ b) ≠ 0 then
    ENNReal.ofReal (Complex.normSq (jacU y)) * C.indicator 1 (rmul p (UF X y)) else 0)

/- English proof (translation)
Establish `hdg : ∀ τ b, β0 X p τ b b ≠ 0`. Introduce `τ b`. Establish `h` using `β0_det X hp τ`. Rewrite `h` using `[Matrix.det_of_upperTriangular (β0_upper X hp τ)]`. Conclude with `Finset.prod_ne_zero_iff.1 h b (Finset.mem_univ b)`.

Establish `hle : Jp X C p ≤ ∫⁻ y, ENNReal.ofReal (Complex.normSq (jacU y)) * (SR X R0).indicator 1 (Lβ (β0 X p) y)`. Unfold `Jp`. Use `lintegral_mono fun y => ?_` and prove the remaining obligations. Use `split_ifs with hy`. Distinguish the cases in `hx : rmul p (UF X y) ∈ C`.

Establish `hS : Lβ (β0 X p) y ∈ SR X R0` using `fun i => Lβ_bound X hCd hR0 hp hy hx i`. Simplify using `[Set.indicator_of_mem hx, Set.indicator_of_mem hS]`. Simplify using `[Set.indicator, hx]`. Simplify using the standard rewrite rules. Rewrite `hle` using `[upper_gen X (β0 X p) (β0_upper X hp) hdg R0, exponent_identity X hp hlast, ← densY_eq X]`.

Conclude with `hle`.
-/
theorem Jp_le {C : Set (Frame X.Ψ r)} (hCd : C ⊆ X.dom) {R0 : ℝ}
    (hR0 : ∀ x ∈ C, ∀ τ a b, ‖β0 X x τ a b‖ ≤ R0) {p : Frame X.Ψ r} (hp : p ∈ X.dom)
    (hlast : ∀ τ, ‖dmin X.Gm p τ (Fin.last r)‖ = 1) :
    Jp X C p ≤ ENNReal.ofReal (densY X p) * KR X R0 := by
  have hdg : ∀ τ b, β0 X p τ b b ≠ 0 := by
    intro τ b
    have h := β0_det X hp τ
    rw [Matrix.det_of_upperTriangular (β0_upper X hp τ)] at h
    exact Finset.prod_ne_zero_iff.1 h b (Finset.mem_univ b)
  have hle : Jp X C p ≤ ∫⁻ y, ENNReal.ofReal (Complex.normSq (jacU y)) *
      (SR X R0).indicator 1 (Lβ (β0 X p) y) := by
    unfold Jp
    refine lintegral_mono fun y => ?_
    split_ifs with hy
    · by_cases hx : rmul p (UF X y) ∈ C
      · have hS : Lβ (β0 X p) y ∈ SR X R0 := fun i => Lβ_bound X hCd hR0 hp hy hx i
        simp [Set.indicator_of_mem hx, Set.indicator_of_mem hS]
      · simp [Set.indicator, hx]
    · simp
  rw [upper_gen X (β0 X p) (β0_upper X hp) hdg R0, exponent_identity X hp hlast, ← densY_eq X] at hle
  exact hle

end
end ReciprocityTheory.ChartRestriction.G.AR.Up.FM
