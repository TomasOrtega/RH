import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralLeOfDisjointTranslates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationDenominatorsAndHostFieldSizes
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open MeasureTheory

noncomputable section

namespace GlobalTheory.GenusOneSup

/- English proof (translation)
The claim follows from `csInf_le ⟨0, fun _ ha => ha.1.le⟩ ⟨h, w₁, h₁, w₂, h₂, rfl⟩`.
-/
theorem area_le (Λ : AddSubgroup ℂ) {w₁ w₂ : ℂ} (h₁ : w₁ ∈ Λ) (h₂ : w₂ ∈ Λ)
    (h : 0 < |((starRingEnd ℂ) w₁ * w₂).im|) : area Λ ≤ |((starRingEnd ℂ) w₁ * w₂).im| :=
  csInf_le ⟨0, fun _ ha => ha.1.le⟩ ⟨h, w₁, h₁, w₂, h₂, rfl⟩

/- English proof (translation)
Establish `h₁ : w₁ ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ)` using `AddSubgroup.subset_closure (by simp)`. Establish `h₂ : w₂ ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ)` using `AddSubgroup.subset_closure (by simp)`. Use `le_antisymm (area_le _ h₁ h₂ h) (le_csInf ⟨_, h, w₁, h₁, w₂, h₂, rfl⟩ ?_)` and prove the remaining obligations. Introduce and unpack `a ⟨ha, x, hx, y, hy, rfl⟩`. Take `⟨m, n, rfl⟩` from `AddSubgroup.mem_closure_pair.1 hx`.

Take `⟨m', n', rfl⟩` from `AddSubgroup.mem_closure_pair.1 hy`. Establish `e : ((starRingEnd ℂ) (m • w₁ + n • w₂) * (m' • w₁ + n' • w₂)).im = ((m * n' - n * m' : ℤ) : ℝ) * ((starRingEnd ℂ) w₁ * w₂).im`. Simplify using `[Complex.mul_im]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `ha`, the goal using `[e, abs_mul]`.

Establish `hk : (m * n' - n * m' : ℤ) ≠ 0`. Introduce `h0`. Rewrite `ha` using `[h0]`. Simplify using `at ha`. Establish `: (1 : ℝ) ≤ |((m * n' - n * m' : ℤ) : ℝ)|`.

Rewrite using `[← Int.cast_abs]`. Conclude with `Int.one_le_abs hk` after adjusting the coercions. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem area_closure {w₁ w₂ : ℂ} (h : 0 < |((starRingEnd ℂ) w₁ * w₂).im|) :
    area (AddSubgroup.closure {w₁, w₂}) = |((starRingEnd ℂ) w₁ * w₂).im| := by
  have h₁ : w₁ ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := AddSubgroup.subset_closure (by simp)
  have h₂ : w₂ ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := AddSubgroup.subset_closure (by simp)
  refine le_antisymm (area_le _ h₁ h₂ h) (le_csInf ⟨_, h, w₁, h₁, w₂, h₂, rfl⟩ ?_)
  rintro a ⟨ha, x, hx, y, hy, rfl⟩
  obtain ⟨m, n, rfl⟩ := AddSubgroup.mem_closure_pair.1 hx
  obtain ⟨m', n', rfl⟩ := AddSubgroup.mem_closure_pair.1 hy
  have e : ((starRingEnd ℂ) (m • w₁ + n • w₂) * (m' • w₁ + n' • w₂)).im =
      ((m * n' - n * m' : ℤ) : ℝ) * ((starRingEnd ℂ) w₁ * w₂).im := by
    simp [Complex.mul_im]
    ring
  rw [e, abs_mul] at ha ⊢
  have hk : (m * n' - n * m' : ℤ) ≠ 0 := by
    intro h0
    rw [h0] at ha
    simp at ha
  have : (1 : ℝ) ≤ |((m * n' - n * m' : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hk
  nlinarith

/- English proof (translation)
Set `b : Module.Basis (Fin 2) ℝ ℂ` to `basisOfLinearIndependentOfCardEqFinrank hli (by simp)`. Establish `hb : ⇑b = ![w₁, w₂]` using `coe_basisOfLinearIndependentOfCardEqFinrank _ _`. Establish `hdet : Complex.basisOneI.det b = ((starRingEnd ℂ) w₁ * w₂).im`. Rewrite using `[Module.Basis.det_apply, Matrix.det_fin_two]`. Simplify using `[Module.Basis.toMatrix_apply, hb, Complex.mul_im]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hspan : (Submodule.span ℤ (Set.range b)).toAddSubgroup = AddSubgroup.closure ({w₁, w₂} : Set ℂ)`. Rewrite using `[Submodule.span_int_eq_addSubgroupClosure, hb]`. Use `congr 1`. Simplify using `[Set.pair_comm]`.

Use `⟨ZSpan.fundamentalDomain b, ?_, ZSpan.fundamentalDomain_isBounded b, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hspan]`. Conclude with `ZSpan.isAddFundamentalDomain' b volume`. Rewrite using `[← hdet]`. Conclude with `abs_pos.2 (Complex.basisOneI.isUnit_det b).ne_zero`.

Rewrite using `[ZSpan.measure_fundamentalDomain b volume Complex.basisOneI, hdet, measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ _), ← Complex.toBasis_orthonormalBasisOneI]`. Use `Complex.orthonormalBasisOneI.volume_parallelepiped` as an intermediate fact. Simplify using `only [OrthonormalBasis.coe_toBasis, this, mul_one]`.
-/
theorem exists_domain {w₁ w₂ : ℂ} (hli : LinearIndependent ℝ ![w₁, w₂]) :
    ∃ F : Set ℂ, IsAddFundamentalDomain (AddSubgroup.closure ({w₁, w₂} : Set ℂ)) F volume ∧
      Bornology.IsBounded F ∧ 0 < |((starRingEnd ℂ) w₁ * w₂).im| ∧
      volume F = ENNReal.ofReal |((starRingEnd ℂ) w₁ * w₂).im| := by
  let b : Module.Basis (Fin 2) ℝ ℂ := basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hb : ⇑b = ![w₁, w₂] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hdet : Complex.basisOneI.det b = ((starRingEnd ℂ) w₁ * w₂).im := by
    rw [Module.Basis.det_apply, Matrix.det_fin_two]
    simp [Module.Basis.toMatrix_apply, hb, Complex.mul_im]
    ring
  have hspan : (Submodule.span ℤ (Set.range b)).toAddSubgroup = AddSubgroup.closure ({w₁, w₂} : Set ℂ) := by
    rw [Submodule.span_int_eq_addSubgroupClosure, hb]
    congr 1
    simp [Set.pair_comm]
  refine ⟨ZSpan.fundamentalDomain b, ?_, ZSpan.fundamentalDomain_isBounded b, ?_, ?_⟩
  · rw [← hspan]; exact ZSpan.isAddFundamentalDomain' b volume
  · rw [← hdet]; exact abs_pos.2 (Complex.basisOneI.isUnit_det b).ne_zero
  · rw [ZSpan.measure_fundamentalDomain b volume Complex.basisOneI, hdet,
      measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ _), ← Complex.toBasis_orthonormalBasisOneI]
    have := Complex.orthonormalBasisOneI.volume_parallelepiped
    simp only [OrthonormalBasis.coe_toBasis, this, mul_one]

def lineIso : EuclideanSpace ℂ Unit ≃ₗᵢ[ℝ] ℂ where
  toFun x := x ()
  invFun z := WithLp.toLp 2 (fun _ => z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  norm_map' x := by
    show ‖x ()‖ = ‖x‖
    simp [EuclideanSpace.norm_eq]

/- English proof (translation)
Use `set s : ℝ := Real.sqrt a with hs`. Establish `hs0 : 0 < s` using `Real.sqrt_pos.2 ha`. Establish `hs2 : s ^ 2 = a` using `Real.sq_sqrt ha.le`. Set `φ : EuclideanSpace ℂ Unit ≃L[ℝ] ℂ` to `lineIso.toContinuousLinearEquiv.trans (ContinuousLinearEquiv.smulLeft (Units.mk0 s hs0.ne'))`. Establish `hφ : ∀ x, φ x = s • lineIso x` using `fun _ => rfl`.

Establish `hn : ∀ x, ‖φ x‖ ^ 2 = a * ‖x‖ ^ 2` using `fun x => by`. Rewrite using `[hφ, norm_smul, lineIso.norm_map, mul_pow, Real.norm_eq_abs, sq_abs, hs2]`. Establish `hw : ∀ x, -Real.pi * ‖x‖ ^ 2 = -Real.pi * ‖φ x‖ ^ 2 / a` using `fun x => by`. Rewrite using `[hn]`. Clear the denominators using the available nonvanishing facts.

Establish `hmp : MeasurePreserving φ volume (ENNReal.ofReal a⁻¹ • (volume : Measure ℂ))`. Establish `h1 : MeasurePreserving (fun z : ℂ => s • z) volume (ENNReal.ofReal a⁻¹ • (volume : Measure ℂ))`. Use `⟨measurable_const_smul s, ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.map_addHaar_smul volume hs0.ne', Complex.finrank_real_complex, hs2, abs_of_pos (inv_pos.2 ha)]`. Conclude with `h1.comp lineIso.measurePreserving`.

Establish `hemb : MeasurableEmbedding φ` using `φ.toHomeomorph.measurableEmbedding`. Set `A : AddSubgroup (EuclideanSpace ℂ Unit)` to `Λ.comap (φ : EuclideanSpace ℂ Unit →+ ℂ)`. Establish `hA : ∀ x, x ∈ A ↔ φ x ∈ Λ` using `fun _ => Iff.rfl`. Establish `hF' : IsAddFundamentalDomain A (φ ⁻¹' F) volume`. Use `hF.preimage_of_equiv (f := φ) (e := fun y : Λ => (⟨φ.symm y, (hA _).2 (by simp)⟩ : A)) ⟨hmp.measurable, ?_⟩ ⟨?_, ?_⟩ ?_` and prove the remaining obligations.

Rewrite using `[hmp.map_eq]`. Conclude with `Measure.smul_absolutelyContinuous`. Introduce `x y h`. Conclude with `Subtype.ext (φ.symm.injective (congrArg Subtype.val h))`. Introduce `x`.

Conclude with `⟨⟨φ x, x.2⟩, Subtype.ext (by simp)⟩`. Introduce `y x show φ (φ.symm y + x) = (y : ℂ) + φ x`. Simplify using the standard rewrite rules. Establish `hvol' : volume (φ ⁻¹' F) = 1`. Rewrite using `[hmp.measure_preimage_emb hemb, Measure.smul_apply, hvol, smul_eq_mul, ← ENNReal.ofReal_mul (inv_pos.2 ha).le, inv_mul_cancel₀ ha.ne', ENNReal.ofReal_one]`.

Establish `hd : Differentiable ℂ (fun x : EuclideanSpace ℂ Unit => g (φ x))`. Establish `: Differentiable ℂ (fun x : EuclideanSpace ℂ Unit => (s : ℂ) * x ())` using `by fun_prop`. Conclude with `hg.comp this`. Establish `key` using `GlobalTheory.ThetaSupBall.sup_le_mean_square Unit A v (φ ⁻¹' F) (fun x => g (φ x)) hv ?_ hF' hvol' hd ?_ ?_ (φ.symm z)`. Simplify using `only [hw, Fintype.card_unit, Nat.cast_one, mul_one, pow_one, ContinuousLinearEquiv.apply_symm_apply] at key`.

Rewrite `key` using `[hmp.setIntegral_preimage_emb hemb (fun z => ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / a)), Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_ofReal (inv_pos.2 ha).le, smul_eq_mul]`. Conclude with `key`. Introduce `x hx hx0`. Use `hmin (φ x) hx (by simpa using hx0)` as an intermediate fact. Rewrite `this` using `[hn, div_eq_mul_one_div]`.

Conclude with `le_of_mul_le_mul_left this ha`. Introduce `x hx y`. Simplify using `only [hw, map_add]`. Conclude with `hper _ hx _`. Simplify using `only [hw]`.

Use `(hmp.integrableOn_comp_preimage hemb (f := fun z => ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / a))).2 ?_` and prove the remaining obligations. Unfold `IntegrableOn`. Rewrite using `[Measure.restrict_smul]`. Conclude with `Integrable.smul_measure hint ENNReal.ofReal_ne_top`.
-/
theorem sup_le_mean (Λ : AddSubgroup ℂ) (a v : ℝ) (F : Set ℂ) (g : ℂ → ℂ) (ha : 0 < a) (hv : 1 ≤ v)
    (hmin : ∀ x ∈ Λ, x ≠ 0 → a / v ≤ ‖x‖ ^ 2) (hF : IsAddFundamentalDomain Λ F volume)
    (hvol : volume F = ENNReal.ofReal a) (hg : Differentiable ℂ g)
    (hper : ∀ x ∈ Λ, ∀ z, ‖g (z + x)‖ ^ 2 * Real.exp (-Real.pi * ‖z + x‖ ^ 2 / a) =
      ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / a))
    (hint : IntegrableOn (fun z => ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / a)) F) (z : ℂ) :
    ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / a) ≤
      3 * (2 * v + 1) * (a⁻¹ * ∫ z in F, ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / a)) := by
  set s : ℝ := Real.sqrt a with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 ha
  have hs2 : s ^ 2 = a := Real.sq_sqrt ha.le
  let φ : EuclideanSpace ℂ Unit ≃L[ℝ] ℂ :=
    lineIso.toContinuousLinearEquiv.trans (ContinuousLinearEquiv.smulLeft (Units.mk0 s hs0.ne'))
  have hφ : ∀ x, φ x = s • lineIso x := fun _ => rfl
  have hn : ∀ x, ‖φ x‖ ^ 2 = a * ‖x‖ ^ 2 := fun x => by
    rw [hφ, norm_smul, lineIso.norm_map, mul_pow, Real.norm_eq_abs, sq_abs, hs2]
  have hw : ∀ x, -Real.pi * ‖x‖ ^ 2 = -Real.pi * ‖φ x‖ ^ 2 / a := fun x => by
    rw [hn]; field_simp
  have hmp : MeasurePreserving φ volume (ENNReal.ofReal a⁻¹ • (volume : Measure ℂ)) := by
    have h1 : MeasurePreserving (fun z : ℂ => s • z) volume (ENNReal.ofReal a⁻¹ • (volume : Measure ℂ)) := by
      refine ⟨measurable_const_smul s, ?_⟩
      rw [Measure.map_addHaar_smul volume hs0.ne', Complex.finrank_real_complex, hs2,
        abs_of_pos (inv_pos.2 ha)]
    exact h1.comp lineIso.measurePreserving
  have hemb : MeasurableEmbedding φ := φ.toHomeomorph.measurableEmbedding
  let A : AddSubgroup (EuclideanSpace ℂ Unit) := Λ.comap (φ : EuclideanSpace ℂ Unit →+ ℂ)
  have hA : ∀ x, x ∈ A ↔ φ x ∈ Λ := fun _ => Iff.rfl
  have hF' : IsAddFundamentalDomain A (φ ⁻¹' F) volume := by
    refine hF.preimage_of_equiv (f := φ) (e := fun y : Λ => (⟨φ.symm y, (hA _).2 (by simp)⟩ : A))
      ⟨hmp.measurable, ?_⟩ ⟨?_, ?_⟩ ?_
    · rw [hmp.map_eq]; exact Measure.smul_absolutelyContinuous
    · intro x y h
      exact Subtype.ext (φ.symm.injective (congrArg Subtype.val h))
    · intro x
      exact ⟨⟨φ x, x.2⟩, Subtype.ext (by simp)⟩
    · intro y x
      show φ (φ.symm y + x) = (y : ℂ) + φ x
      simp
  have hvol' : volume (φ ⁻¹' F) = 1 := by
    rw [hmp.measure_preimage_emb hemb, Measure.smul_apply, hvol, smul_eq_mul,
      ← ENNReal.ofReal_mul (inv_pos.2 ha).le, inv_mul_cancel₀ ha.ne', ENNReal.ofReal_one]
  have hd : Differentiable ℂ (fun x : EuclideanSpace ℂ Unit => g (φ x)) := by
    have : Differentiable ℂ (fun x : EuclideanSpace ℂ Unit => (s : ℂ) * x ()) := by fun_prop
    exact hg.comp this
  have key := GlobalTheory.ThetaSupBall.sup_le_mean_square Unit A v (φ ⁻¹' F) (fun x => g (φ x)) hv ?_ hF' hvol' hd ?_ ?_ (φ.symm z)
  · simp only [hw, Fintype.card_unit, Nat.cast_one, mul_one, pow_one, ContinuousLinearEquiv.apply_symm_apply] at key
    rw [hmp.setIntegral_preimage_emb hemb (fun z => ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / a)),
      Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_ofReal (inv_pos.2 ha).le, smul_eq_mul] at key
    exact key
  · intro x hx hx0
    have := hmin (φ x) hx (by simpa using hx0)
    rw [hn, div_eq_mul_one_div] at this
    exact le_of_mul_le_mul_left this ha
  · intro x hx y
    simp only [hw, map_add]
    exact hper _ hx _
  · simp only [hw]
    refine (hmp.integrableOn_comp_preimage hemb
      (f := fun z => ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / a))).2 ?_
    unfold IntegrableOn
    rw [Measure.restrict_smul]
    exact Integrable.smul_measure hint ENNReal.ofReal_ne_top

/- English proof (translation)
Unfold `U1`. Rewrite using `[norm_mul, mul_pow, Complex.norm_exp, mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]`. Use `congr 2`. Establish `e : (2 * (area Λ : ℂ)) = ((2 * area Λ : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite using `[e, Complex.sub_re, Complex.div_ofReal_re, Complex.div_ofReal_re, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]`.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem thetaTranslation_weighted_normSq (Λ : AddSubgroup ℂ) (t z : ℂ) (g : ℂ → ℂ) :
    ‖U1 Λ t g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ) =
      ‖g (z + t)‖ ^ 2 * Real.exp (-Real.pi * ‖z + t‖ ^ 2 / area Λ) := by
  unfold U1
  rw [norm_mul, mul_pow, Complex.norm_exp, mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 2
  have e : (2 * (area Λ : ℂ)) = ((2 * area Λ : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.sub_re, Complex.div_ofReal_re, Complex.div_ofReal_re, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
  simp
  ring

/- English proof (translation)
Take `⟨⟨hd, -, -, hU⟩, -⟩` from `GlobalTheory.OddTheta.sgStar_laws Λ hΛ`. Take `⟨w₁, w₂, hli, rfl⟩` from `hΛ`. Take `⟨F, hF, hb, hpos, hvol⟩` from `exists_domain hli`. Establish `har` using `area_closure hpos`. Rewrite `hpos`, `hvol` using `[← har]`.

Use `set Λ : AddSubgroup ℂ := AddSubgroup.closure {w₁, w₂} with hΛ`. Establish `hper : ∀ x ∈ Λ, ∀ z, ‖sgStar Λ (z + x)‖ ^ 2 * Real.exp (-Real.pi * ‖z + x‖ ^ 2 / area Λ) = ‖sgStar Λ z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ)`. Introduce `x hx z`. Rewrite using `[← thetaTranslation_weighted_normSq, hU x hx, norm_mul]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hc : Continuous fun z => ‖sgStar Λ z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ)`. Use `hd.continuous` as an intermediate fact. Use `fun_prop`. Establish `hint : IntegrableOn (fun z => ‖sgStar Λ z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ)) F` using `(hc.continuousOn.integrableOn_compact hb.isCompact_closure).mono_set subset_closure`. Establish `key` using `sup_le_mean Λ (area Λ) v F (sgStar Λ) hpos hv hmin hF hvol hd hper hint t`.

Establish `h0` using `thetaTranslation_weighted_normSq Λ t 0 (sgStar Λ)`. Simplify using `only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div, Real.exp_zero, mul_one, zero_add] at h0`. Rewrite using `[h0]`. Use `key.trans (le_of_eq ?_)` and prove the remaining obligations. Use `congr 1`.

Establish `hF'` using `Classical.epsilon_spec (p := fun Fd : Set ℂ => IsAddFundamentalDomain Λ Fd volume) ⟨F, hF⟩`. Establish `: Countable Λ`. Establish `: (Λ : Set ℂ) ⊆ Set.range (fun p : ℤ × ℤ => p.1 • w₁ + p.2 • w₂)`. Introduce `x hx`. Take `⟨m, n, rfl⟩` from `AddSubgroup.mem_closure_pair.1 hx`.

Conclude with `⟨(m, n), rfl⟩`. Conclude with `((Set.countable_range _).mono this).to_subtype`. Establish `: VAddInvariantMeasure Λ ℂ volume` using `⟨fun γ s _ => measure_preimage_add volume (γ : ℂ) s⟩`. Unfold `nrm1Sq`. Simplify using `only`.

Rewrite using `[setAverage_eq, measureReal_def, hF'.measure_eq hF, hF'.setIntegral_eq hF, hvol, ENNReal.toReal_ofReal hpos.le, smul_eq_mul]`. Introduce `γ z`. Use `hper γ γ.2 z` as an intermediate fact. Rewrite `this` using `[add_comm]`. Conclude with `this`.
-/
theorem lattice_sup (Λ : AddSubgroup ℂ)
    (hΛ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂})
    (v : ℝ) (hv : 1 ≤ v) (hmin : ∀ x ∈ Λ, x ≠ 0 → area Λ / v ≤ ‖x‖ ^ 2) (t : ℂ) :
    ‖U1 Λ t (sgStar Λ) 0‖ ^ 2 ≤ 3 * (2 * v + 1) * nrm1Sq Λ (sgStar Λ) := by
  obtain ⟨⟨hd, -, -, hU⟩, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ hΛ
  obtain ⟨w₁, w₂, hli, rfl⟩ := hΛ
  obtain ⟨F, hF, hb, hpos, hvol⟩ := exists_domain hli
  have har := area_closure hpos
  rw [← har] at hpos hvol
  set Λ : AddSubgroup ℂ := AddSubgroup.closure {w₁, w₂} with hΛ
  have hper : ∀ x ∈ Λ, ∀ z, ‖sgStar Λ (z + x)‖ ^ 2 * Real.exp (-Real.pi * ‖z + x‖ ^ 2 / area Λ) =
      ‖sgStar Λ z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ) := by
    intro x hx z
    rw [← thetaTranslation_weighted_normSq, hU x hx, norm_mul]
    split_ifs <;> simp
  have hc : Continuous fun z => ‖sgStar Λ z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ) := by
    have := hd.continuous
    fun_prop
  have hint : IntegrableOn (fun z => ‖sgStar Λ z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ)) F :=
    (hc.continuousOn.integrableOn_compact hb.isCompact_closure).mono_set subset_closure
  have key := sup_le_mean Λ (area Λ) v F (sgStar Λ) hpos hv hmin hF hvol hd hper hint t
  have h0 := thetaTranslation_weighted_normSq Λ t 0 (sgStar Λ)
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    Real.exp_zero, mul_one, zero_add] at h0
  rw [h0]
  refine key.trans (le_of_eq ?_)
  congr 1
  have hF' := Classical.epsilon_spec (p := fun Fd : Set ℂ => IsAddFundamentalDomain Λ Fd volume) ⟨F, hF⟩
  have : Countable Λ := by
    have : (Λ : Set ℂ) ⊆ Set.range (fun p : ℤ × ℤ => p.1 • w₁ + p.2 • w₂) := by
      intro x hx
      obtain ⟨m, n, rfl⟩ := AddSubgroup.mem_closure_pair.1 hx
      exact ⟨(m, n), rfl⟩
    exact ((Set.countable_range _).mono this).to_subtype
  have : VAddInvariantMeasure Λ ℂ volume := ⟨fun γ s _ => measure_preimage_add volume (γ : ℂ) s⟩
  unfold nrm1Sq
  simp only
  rw [setAverage_eq, measureReal_def, hF'.measure_eq hF, hF'.setIntegral_eq hF, hvol,
    ENNReal.toReal_ofReal hpos.le, smul_eq_mul]
  intro γ z
  have := hper γ γ.2 z
  rw [add_comm] at this
  exact this

/- English proof (translation)
Introduce `D hD cc δ hc t`. Take `⟨hΛ, -, -, -, hst⟩` from `GlobalTheory.CurveLattice.lattice_of_curve D hD cc δ hc`. Take `⟨-, hlog, hrd, -⟩` from `GlobalTheory.NormSum.letters_and_sizes D hD`. Use `lattice_sup _ hΛ _ hrd ?_ t` and prove the remaining obligations. Introduce `x hx hx0`.

Establish `hd : (0 : ℝ) < D.host.d` using `by exact_mod_cast D.host.hyp.2.1.pos`. Establish `hsq` using `D.host.sqd_sq`. Set `β : D.host.K` to `⟨D.host.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩`. Establish `hβ : β ^ 2 = -(D.host.d : D.host.K)` using `Subtype.ext (by simpa [β] using hsq)`. Establish `hi : IsIntegral ℤ β`.

Use `IsIntegral.of_pow (n := 2) two_pos ?_` and prove the remaining obligations. Rewrite using `[hβ]`. Conclude with `(isIntegral_natCast _).neg`. Establish `hm` using `hst ⟨β, hi⟩ x hx`. Use `set c : ℂ := D.host.φ₀ (D.host.sqd) with hcdef`.

Establish `hm' : c * x ∈ lamOf D cc δ` using `hm`. Establish `hc2 : c ^ 2 = -(D.host.d : ℂ)`. Rewrite using `[hcdef, ← map_pow, hsq]`. Simplify using the standard rewrite rules. Establish `hre : c.re * c.re - c.im * c.im = -(D.host.d : ℝ)`.

Use `congrArg Complex.re hc2` as an intermediate fact. Simplify `this` using `[pow_two]`. Establish `him : c.re * c.im = 0`. Use `congrArg Complex.im hc2` as an intermediate fact. Simplify using `[pow_two] at this`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hre0 : c.re = 0`. Break down `mul_eq_zero.1 him with h | h` into its components or cases. Conclude with `h`. Rewrite `hre` using `[h]`.

Use polynomial arithmetic with `[mul_self_nonneg c.re]`. Establish `him2 : c.im ^ 2 = D.host.d` using `by rw [hre0] at hre; linarith`. Establish `e : |((starRingEnd ℂ) x * (c * x)).im| = |c.im| * ‖x‖ ^ 2`. Establish `: ((starRingEnd ℂ) x * (c * x)).im = c.im * ‖x‖ ^ 2`. Rewrite using `[← Complex.normSq_eq_norm_sq, Complex.normSq_apply]`.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, abs_mul, abs_of_nonneg (sq_nonneg ‖x‖)]`. Establish `hx2 : 0 < ‖x‖ ^ 2` using `by positivity`. Establish `hci : 0 < |c.im|` using `abs_pos.2 (by intro h; rw [h] at him2; linarith)`.

Establish `hle` using `area_le _ hx hm' (by rw [e]; positivity)`. Establish `hrd0 : 0 < D.host.rdE` using `by linarith`. Establish `hdle : (D.host.d : ℝ) ≤ D.host.rdE ^ 2`. Rewrite using `[← Real.log_le_log_iff hd (by positivity), Real.log_pow]`. Conclude with `hlog` after adjusting the coercions.

Establish `hcle : |c.im| ≤ D.host.rdE` using `abs_le_of_sq_le_sq' (by rw [him2]; exact hdle) hrd0.le |> abs_le.2`. Rewrite using `[div_le_iff₀ hrd0]`. Rewrite `hle` using `[e]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem value_le_mean_square : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t, ‖U1 (lamOf D cc δ) t (sgStar (lamOf D cc δ)) 0‖ ^ 2 ≤ 3 * (2 * D.host.rdE + 1) * nrm1Sq (lamOf D cc δ) (sgStar (lamOf D cc δ)) := by
  intro D hD cc δ hc t
  obtain ⟨hΛ, -, -, -, hst⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hD cc δ hc
  obtain ⟨-, hlog, hrd, -⟩ := GlobalTheory.NormSum.letters_and_sizes D hD
  refine lattice_sup _ hΛ _ hrd ?_ t
  intro x hx hx0
  have hd : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
  have hsq := D.host.sqd_sq
  let β : D.host.K := ⟨D.host.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have hβ : β ^ 2 = -(D.host.d : D.host.K) := Subtype.ext (by simpa [β] using hsq)
  have hi : IsIntegral ℤ β := by
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [hβ]
    exact (isIntegral_natCast _).neg
  have hm := hst ⟨β, hi⟩ x hx
  set c : ℂ := D.host.φ₀ (D.host.sqd) with hcdef
  have hm' : c * x ∈ lamOf D cc δ := hm
  have hc2 : c ^ 2 = -(D.host.d : ℂ) := by
    rw [hcdef, ← map_pow, hsq]; simp
  have hre : c.re * c.re - c.im * c.im = -(D.host.d : ℝ) := by
    have := congrArg Complex.re hc2
    simpa [pow_two] using this
  have him : c.re * c.im = 0 := by
    have := congrArg Complex.im hc2
    simp [pow_two] at this
    linarith
  have hre0 : c.re = 0 := by
    rcases mul_eq_zero.1 him with h | h
    · exact h
    · rw [h] at hre; nlinarith [mul_self_nonneg c.re]
  have him2 : c.im ^ 2 = D.host.d := by rw [hre0] at hre; linarith
  have e : |((starRingEnd ℂ) x * (c * x)).im| = |c.im| * ‖x‖ ^ 2 := by
    have : ((starRingEnd ℂ) x * (c * x)).im = c.im * ‖x‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp
      ring
    rw [this, abs_mul, abs_of_nonneg (sq_nonneg ‖x‖)]
  have hx2 : 0 < ‖x‖ ^ 2 := by positivity
  have hci : 0 < |c.im| := abs_pos.2 (by intro h; rw [h] at him2; linarith)
  have hle := area_le _ hx hm' (by rw [e]; positivity)
  have hrd0 : 0 < D.host.rdE := by linarith
  have hdle : (D.host.d : ℝ) ≤ D.host.rdE ^ 2 := by
    rw [← Real.log_le_log_iff hd (by positivity), Real.log_pow]
    exact_mod_cast hlog
  have hcle : |c.im| ≤ D.host.rdE := abs_le_of_sq_le_sq' (by rw [him2]; exact hdle) hrd0.le |> abs_le.2
  rw [div_le_iff₀ hrd0]
  rw [e] at hle
  nlinarith

end GlobalTheory.GenusOneSup
