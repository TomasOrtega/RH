import Mathlib
import Formalism.PeriodIntegrals.UMultOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompactGelfandAverage.AvgStep

noncomputable section

namespace PI.UnitaryGroupMassFormula.GelfCpt

open MeasureTheory Matrix

/- English proof (translation)
The claim follows from `hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)`.
-/
theorem integrable_of_cont {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] {F : X → ℂ} (hF : Continuous F) :
    Integrable F ν :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `g`. Establish `e` using `Measure.isMulLeftInvariant_eq_smul (Measure.map (· * g) μ) μ`. Establish `hu : Measure.map (· * g) μ Set.univ = μ Set.univ`. Rewrite using `[Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ]`.

Establish `h0 : μ Set.univ ≠ 0` using `(Measure.measure_univ_pos.mpr (NeZero.ne μ)).ne'`. Establish `ht : μ Set.univ ≠ ⊤` using `measure_ne_top μ Set.univ`. Establish `h1 : ((Measure.haarScalarFactor (Measure.map (· * g) μ) μ : NNReal) : ENNReal) * μ Set.univ = 1 * μ Set.univ`. Rewrite using `[one_mul]`. Use `conv_rhs => rw [← hu, e]`.

Simplify using the standard rewrite rules. Establish `hc : ((Measure.haarScalarFactor (Measure.map (· * g) μ) μ : NNReal) : ENNReal) = 1` using `(ENNReal.mul_left_inj h0 ht).1 h1`. Rewrite using `[e, ENNReal.coe_eq_one.mp hc, one_smul]`.
-/
theorem haar_rightInv (μ : Measure G) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  constructor
  intro g
  have e := Measure.isMulLeftInvariant_eq_smul (Measure.map (· * g) μ) μ
  have hu : Measure.map (· * g) μ Set.univ = μ Set.univ := by
    rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ]
  have h0 : μ Set.univ ≠ 0 := (Measure.measure_univ_pos.mpr (NeZero.ne μ)).ne'
  have ht : μ Set.univ ≠ ⊤ := measure_ne_top μ Set.univ
  have h1 : ((Measure.haarScalarFactor (Measure.map (· * g) μ) μ : NNReal) : ENNReal) * μ Set.univ =
      1 * μ Set.univ := by
    rw [one_mul]
    conv_rhs => rw [← hu, e]
    simp
  have hc : ((Measure.haarScalarFactor (Measure.map (· * g) μ) μ : NNReal) : ENNReal) = 1 :=
    (ENNReal.mul_left_inj h0 ht).1 h1
  rw [e, ENNReal.coe_eq_one.mp hc, one_smul]

/- English proof (translation)
Use `haar_rightInv μ` as an intermediate fact. Establish `e1` using `integral_mul_left_eq_self (μ := μ) (fun y => F (y * h⁻¹)) h`. Establish `e2` using `integral_mul_right_eq_self (μ := μ) F h⁻¹`. Conclude with `e1.trans e2`.
-/
theorem integral_conj (μ : Measure G) [μ.IsHaarMeasure] (F : G → ℂ) (h : G) :
    ∫ g, F (h * g * h⁻¹) ∂μ = ∫ g, F g ∂μ := by
  have := haar_rightInv μ
  have e1 := integral_mul_left_eq_self (μ := μ) (fun y => F (y * h⁻¹)) h
  have e2 := integral_mul_right_eq_self (μ := μ) F h⁻¹
  exact e1.trans e2

/- English proof (translation)
Establish `hR : ∀ k l, Continuous fun g => ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) k l` using `fun k l => (continuous_apply l).comp ((continuous_apply k).comp hc)`. Simplify using `only [Matrix.mul_apply, intMat, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[integral_finsetSum]`. Use `Finset.sum_congr rfl (fun l _ => ?_)` and prove the remaining obligations. Rewrite using `[integral_finsetSum]`.

Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[← integral_const_mul, ← integral_mul_const]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Expand and normalize the polynomial expressions, which then agree.

Introduce `k _`. Conclude with `integrable_of_cont μ (hf.mul ((continuous_const.mul (hR k l)).mul continuous_const))`. Introduce `l _`. Conclude with `integrable_finsetSum _ (fun k _ => integrable_of_cont μ (hf.mul ((continuous_const.mul (hR k l)).mul continuous_const)))`.
-/
theorem mul_intMat_mul (μ : Measure G) [IsFiniteMeasure μ] {N : ℕ} (ρ : G →* GL (Fin N) ℂ)
    (hc : PI.UMultOne.Cont ρ) {f : G → ℂ} (hf : Continuous f) (M M' : Matrix (Fin N) (Fin N) ℂ)
    (i j : Fin N) :
    (M * intMat μ ρ f * M') i j =
      ∫ g, f g * (M * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * M') i j ∂μ := by
  have hR : ∀ k l, Continuous fun g => ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) k l :=
    fun k l => (continuous_apply l).comp ((continuous_apply k).comp hc)
  simp only [Matrix.mul_apply, intMat, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [← integral_const_mul, ← integral_mul_const]
      congr 1
      funext g
      ring
    · intro k _
      exact integrable_of_cont μ (hf.mul ((continuous_const.mul (hR k l)).mul continuous_const))
  · intro l _
    exact integrable_finsetSum _ (fun k _ =>
      integrable_of_cont μ (hf.mul ((continuous_const.mul (hR k l)).mul continuous_const)))

/- English proof (translation)
Establish `hRmul : ∀ x y, ((ρ (x * y) : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = ((ρ x : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * ((ρ y : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)` using `fun x y => by`. Rewrite using `[map_mul, Units.val_mul]`. Establish `e : ((ρ h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * intMat μ ρ f * ((ρ h⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = intMat μ ρ f`. Rewrite using `[hA, Matrix.mul_assoc, ← hRmul, mul_inv_cancel, map_one, Units.val_one, Matrix.mul_one]`. Rewrite using `[← e, mul_intMat_mul μ ρ hc hf]`.

Use `(integral_conj μ (fun x => f (h⁻¹ * x * h) * ((ρ x : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j) h).symm.trans ?_` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `g`. Establish `hg : h⁻¹ * (h * g * h⁻¹) * h = g` using `by group`. Simplify using `only [hg, hRmul]`.
-/
theorem intMat_conj (μ : Measure G) [μ.IsHaarMeasure] {N : ℕ} (ρ : G →* GL (Fin N) ℂ)
    (hc : PI.UMultOne.Cont ρ) {f : G → ℂ} (hf : Continuous f) (h : G)
    (hA : ((ρ h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * intMat μ ρ f =
      intMat μ ρ f * ((ρ h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) (i j : Fin N) :
    ∫ g, f (h⁻¹ * g * h) * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂μ =
      intMat μ ρ f i j := by
  have hRmul : ∀ x y, ((ρ (x * y) : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      ((ρ x : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *
        ((ρ y : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := fun x y => by
    rw [map_mul, Units.val_mul]
  have e : ((ρ h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * intMat μ ρ f *
      ((ρ h⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = intMat μ ρ f := by
    rw [hA, Matrix.mul_assoc, ← hRmul, mul_inv_cancel, map_one, Units.val_one, Matrix.mul_one]
  rw [← e, mul_intMat_mul μ ρ hc hf]
  refine (integral_conj μ (fun x => f (h⁻¹ * x * h) *
    ((ρ x : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j) h).symm.trans ?_
  congr 1
  funext g
  have hg : h⁻¹ * (h * g * h⁻¹) * h = g := by group
  simp only [hg, hRmul]

end

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ μ _ H hH N ρ hc f hf hA`. Use `haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact`. Use `letI : MeasurableSpace H := borel H`. Use `haveI : BorelSpace H := ⟨rfl⟩`. Set `ν : Measure H` to `Measure.haarMeasure ⊤`.

Use `haveI : IsProbabilityMeasure ν := ⟨by`. Use `Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts H))` as an intermediate fact. Rewrite using `[TopologicalSpace.PositiveCompacts.coe_top] at this⟩` and apply the resulting hypothesis. Establish `hF : Continuous (Function.uncurry fun (g : G) (h : H) => f ((h : G)⁻¹ * g * h))` using `hf.comp (((continuous_subtype_val.comp continuous_snd).inv.mul continuous_fst).mul (continuous_subtype_val.comp continuous_snd))`. Use `⟨fun g => ∫ h : H, f ((h : G)⁻¹ * g * h) ∂ν, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `continuous_parametric_integral_of_continuous (μ := ν) hF isCompact_univ` as an intermediate fact. Simplify `this` using `only [Measure.restrict_univ]`. Introduce `k hk x show ∫ h : H, f ((h : G)⁻¹ * (k * x * k⁻¹) * h) ∂ν = ∫ h : H, f ((h : G)⁻¹ * x * h) ∂ν`. Establish `e` using `integral_mul_left_eq_self (μ := ν) (fun h : H => f ((h : G)⁻¹ * x * h)) (⟨k, hk⟩⁻¹ : H)`. Rewrite using `[← e]`.

Use `congr 1`. Use function extensionality and compare the values at `h`. Use `show f ((h : G)⁻¹ * (k * x * k⁻¹) * h) = f (((⟨k, hk⟩⁻¹ * h : H) : G)⁻¹ * x * ((⟨k, hk⟩⁻¹ * h : H) : G))`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev, inv_inv, mul_assoc]`. Use extensionality with `i j`.

Establish `hR : Continuous fun g => ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j` using `(continuous_apply j).comp ((continuous_apply i).comp hc)`. Establish `hI : Integrable (Function.uncurry fun (g : G) (h : H) => f ((h : G)⁻¹ * g * h) * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j) (μ.prod ν)` using `integrable_of_cont _ (hF.mul (hR.comp continuous_fst))`. Simplify using `only [intMat, Matrix.of_apply]`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`.

Use function extensionality and compare the values at `g`. Rewrite using `[integral_mul_const]`. Use `_ = ∫ h : H, ∫ g, f ((h : G)⁻¹ * g * h) * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂μ ∂ν := integral_integral_swap hI`. Use `_ = ∫ _h : H, intMat μ ρ f i j ∂ν := by`. Use `congr 1`.

Use function extensionality and compare the values at `h`. Conclude with `intMat_conj μ ρ hc hf (h : G) (hA h h.2) i j`. Use `_ = ∫ g, f g * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂μ := by`. Simplify using `[intMat]`.
-/
theorem avgStep : AvgStep := by
  intro G _ _ _ _ _ _ _ _ μ _ H hH N ρ hc f hf hA
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  letI : MeasurableSpace H := borel H
  haveI : BorelSpace H := ⟨rfl⟩
  let ν : Measure H := Measure.haarMeasure ⊤
  haveI : IsProbabilityMeasure ν := ⟨by
    have := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts H))
    rwa [TopologicalSpace.PositiveCompacts.coe_top] at this⟩
  have hF : Continuous (Function.uncurry fun (g : G) (h : H) => f ((h : G)⁻¹ * g * h)) :=
    hf.comp (((continuous_subtype_val.comp continuous_snd).inv.mul continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd))
  refine ⟨fun g => ∫ h : H, f ((h : G)⁻¹ * g * h) ∂ν, ?_, ?_, ?_⟩
  · have := continuous_parametric_integral_of_continuous (μ := ν) hF isCompact_univ
    simpa only [Measure.restrict_univ] using this
  · intro k hk x
    show ∫ h : H, f ((h : G)⁻¹ * (k * x * k⁻¹) * h) ∂ν = ∫ h : H, f ((h : G)⁻¹ * x * h) ∂ν
    have e := integral_mul_left_eq_self (μ := ν) (fun h : H => f ((h : G)⁻¹ * x * h))
      (⟨k, hk⟩⁻¹ : H)
    rw [← e]
    congr 1
    funext h
    show f ((h : G)⁻¹ * (k * x * k⁻¹) * h) = f (((⟨k, hk⟩⁻¹ * h : H) : G)⁻¹ * x * ((⟨k, hk⟩⁻¹ * h : H) : G))
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev, inv_inv, mul_assoc]
  · ext i j
    have hR : Continuous fun g => ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j :=
      (continuous_apply j).comp ((continuous_apply i).comp hc)
    have hI : Integrable (Function.uncurry fun (g : G) (h : H) =>
        f ((h : G)⁻¹ * g * h) * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j)
        (μ.prod ν) :=
      integrable_of_cont _ (hF.mul (hR.comp continuous_fst))
    simp only [intMat, Matrix.of_apply]
    calc ∫ g, (∫ h : H, f ((h : G)⁻¹ * g * h) ∂ν) *
          ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂μ
        = ∫ g, ∫ h : H, f ((h : G)⁻¹ * g * h) *
            ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂ν ∂μ := by
          congr 1; funext g; rw [integral_mul_const]
      _ = ∫ h : H, ∫ g, f ((h : G)⁻¹ * g * h) *
            ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂μ ∂ν :=
          integral_integral_swap hI
      _ = ∫ _h : H, intMat μ ρ f i j ∂ν := by
          congr 1; funext h
          exact intMat_conj μ ρ hc hf (h : G) (hA h h.2) i j
      _ = ∫ g, f g * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂μ := by
          simp [intMat]

end PI.UnitaryGroupMassFormula.GelfCpt
