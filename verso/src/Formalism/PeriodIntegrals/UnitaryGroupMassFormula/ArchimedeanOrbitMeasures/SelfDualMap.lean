import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FibInvT

noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

/- English proof (translation)
Simplify using `only [HSMul.hSMul, SMul.smul]`. Use function extensionality and compare the values at `a`. Simplify using `only [actTup, Pi.add_apply, mulVec_add]`.
-/
theorem smul_add_tup {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (x y : TupI X) :
    g • (x + y) = g • x + g • y := by
  simp only [HSMul.hSMul, SMul.smul]
  funext a
  simp only [actTup, Pi.add_apply, mulVec_add]

/- English proof (translation)
Establish `h0 : g • (0 : TupI X) = 0`. Simplify using `using smul_add_tup X g 0 0`. Establish `h` using `smul_add_tup X g (-y) y`. Rewrite `h` using `[neg_add_cancel, h0]`. Conclude with `eq_neg_of_add_eq_zero_left h.symm`.
-/
theorem smul_neg_tup {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (y : TupI X) :
    g • (-y) = -(g • y) := by
  have h0 : g • (0 : TupI X) = 0 := by
    simpa using smul_add_tup X g 0 0
  have h := smul_add_tup X g (-y) y
  rw [neg_add_cancel, h0] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/- English proof (translation)
Establish `key : ∀ u v : n → A, Formalism.UG.hform σ J u v = (σ ∘ u) ⬝ᵥ (J *ᵥ v)`. Introduce `u v`. Use `first`. Consider the case `simp only [Formalism.UG.hform, dotProduct, mulVec, Function.comp, Finset.mul_sum, mul_assoc]`. Consider the case `simp only [Formalism.UG.hform, Matrix.dotProduct, mulVec, Function.comp, Finset.mul_sum, mul_assoc]`.

Consider the case `simp [Formalism.UG.hform, mulVec, Finset.mul_sum, mul_assoc]`. Establish `hσ : σ ∘ (g *ᵥ x) = (g.map σ) *ᵥ (σ ∘ x)`. Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec σ g x i`. Establish `e1 : (g.map σ) *ᵥ (σ ∘ x) = (σ ∘ x) ᵥ* (g.map σ)ᵀ` using `(vecMul_transpose _ _).symm`.

Establish `hg' : (g.map σ)ᵀ * J * g = J` using `hg`. Rewrite using `[key, key, hσ, e1, ← dotProduct_mulVec]`. Simplify using `only [mulVec_mulVec, ← Matrix.mul_assoc]`. Rewrite using `[hg']`.
-/
private theorem hform_mulVec_eq_of_cT_mul_mul_eq {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (σ : A →+* A) (J g : Matrix n n A) (hg : Formalism.UG.cT σ g * J * g = J) (x y : n → A) :
    Formalism.UG.hform σ J (g *ᵥ x) (g *ᵥ y) = Formalism.UG.hform σ J x y := by
  have key : ∀ u v : n → A, Formalism.UG.hform σ J u v = (σ ∘ u) ⬝ᵥ (J *ᵥ v) := by
    intro u v
    first
    | simp only [Formalism.UG.hform, dotProduct, mulVec, Function.comp, Finset.mul_sum, mul_assoc]
    | simp only [Formalism.UG.hform, Matrix.dotProduct, mulVec, Function.comp, Finset.mul_sum, mul_assoc]
    | simp [Formalism.UG.hform, mulVec, Finset.mul_sum, mul_assoc]
  have hσ : σ ∘ (g *ᵥ x) = (g.map σ) *ᵥ (σ ∘ x) := by
    funext i
    exact RingHom.map_mulVec σ g x i
  have e1 : (g.map σ) *ᵥ (σ ∘ x) = (σ ∘ x) ᵥ* (g.map σ)ᵀ := (vecMul_transpose _ _).symm
  have hg' : (g.map σ)ᵀ * J * g = J := hg
  rw [key, key, hσ, e1, ← dotProduct_mulVec]
  simp only [mulVec_mulVec, ← Matrix.mul_assoc]
  rw [hg']

/- English proof (translation)
Simplify using `only [HSMul.hSMul, SMul.smul]`. Unfold `BR`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `congr 1`. Establish `hg : Formalism.UG.cT (sigR (Ainf X.B.I.F) X.B.I.cm.sig) (↑(HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g) : Matrix _ _ _) * JR (Ainf X.B.I.F) X.B.I.J * (↑(HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g) : Matrix _ _ _) = JR (Ainf X.B.I.F) X.B.I.J` using `(show HR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J from g).2`.

Conclude with `hform_mulVec_eq_of_cT_mul_mul_eq _ _ _ hg _ _`.
-/
theorem BR_smul {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (x y : TupI X) :
    BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (g • x) (g • y) = BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y := by
  simp only [HSMul.hSMul, SMul.smul]
  unfold BR
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have hg : Formalism.UG.cT (sigR (Ainf X.B.I.F) X.B.I.cm.sig)
      (↑(HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g) : Matrix _ _ _) * JR (Ainf X.B.I.F) X.B.I.J *
      (↑(HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g) : Matrix _ _ _) = JR (Ainf X.B.I.F) X.B.I.J :=
    (show HR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J from g).2
  exact hform_mulVec_eq_of_cT_mul_mul_eq _ _ _ hg _ _

def smulAE {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) : TupI X ≃+ TupI X where
  toFun y := g • y
  invFun y := g⁻¹ • y
  left_inv y := inv_smul_smul g y
  right_inv y := smul_inv_smul g y
  map_add' x y := smul_add_tup X g x y

/- English proof (translation)
Use `⟨hH, fun Φ hΦc hΦs hint z => ?_⟩` and prove the remaining obligations. Take `⟨hc', hs'⟩` from `hcont Φ hΦc hΦs`. Establish `hinner : ∀ y, ∫ x, Φ x * χ x (em y) ∂(μ.map em) = ∫ x, (Φ ∘ em) x * χ x y ∂μ`. Introduce `y`. Rewrite using `[integral_map_equiv]`.

Use `integral_congr_ae (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp_apply, hχ]`. Establish `hint' : Integrable (fun y => ∫ x, (Φ ∘ em) x * χ x y ∂μ) μ`. Establish `h1` using `(integrable_map_equiv em _).mp hint`. Use `h1.congr (ae_of_all _ fun y => ?_)` and prove the remaining obligations.

Simplify using `only [Function.comp_apply]`. Conclude with `hinner y`. Establish `hz : ∀ y, χ (em y) z = χ y (em.symm z)`. Introduce `y`. Use `conv_lhs => rw [← em.apply_symm_apply z]`.

Conclude with `hχ y (em.symm z)`. Combine the equalities or inequalities in the displayed calculation. Use `integral_congr_ae (ae_of_all _ fun y => ?_)` and prove the remaining obligations. Use `show (∫ x, Φ x * χ x (em y) ∂(μ.map em)) * χ (em y) z = (∫ x, (Φ ∘ em) x * χ x y ∂μ) * χ y (em.symm z)`. Rewrite using `[hinner y, hz y]`.

Use `_ = (Φ ∘ em) (-(em.symm z)) := hμ.2 (Φ ∘ em) hc' hs' hint' (em.symm z)`. Use `_ = Φ (-z) := by simp only [Function.comp_apply, hneg, MeasurableEquiv.apply_symm_apply]`.
-/
private theorem selfDual_map_of_isAddHaarMeasure {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
    (μ : Measure V) (χ : V → V → ℂ) (em : V ≃ᵐ V) (hH : (μ.map em).IsAddHaarMeasure)
    (hχ : ∀ a b, χ (em a) (em b) = χ a b) (hneg : ∀ a, em (-a) = -(em a))
    (hcont : ∀ Φ : V → ℂ, Continuous Φ → HasCompactSupport Φ →
      Continuous (Φ ∘ em) ∧ HasCompactSupport (Φ ∘ em))
    (hμ : SelfDual μ χ) : SelfDual (μ.map em) χ := by
  refine ⟨hH, fun Φ hΦc hΦs hint z => ?_⟩
  obtain ⟨hc', hs'⟩ := hcont Φ hΦc hΦs
  have hinner : ∀ y, ∫ x, Φ x * χ x (em y) ∂(μ.map em) = ∫ x, (Φ ∘ em) x * χ x y ∂μ := by
    intro y
    rw [integral_map_equiv]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [Function.comp_apply, hχ]
  have hint' : Integrable (fun y => ∫ x, (Φ ∘ em) x * χ x y ∂μ) μ := by
    have h1 := (integrable_map_equiv em _).mp hint
    refine h1.congr (ae_of_all _ fun y => ?_)
    simp only [Function.comp_apply]
    exact hinner y
  have hz : ∀ y, χ (em y) z = χ y (em.symm z) := by
    intro y
    conv_lhs => rw [← em.apply_symm_apply z]
    exact hχ y (em.symm z)
  calc ∫ y, (∫ x, Φ x * χ x y ∂(μ.map em)) * χ y z ∂(μ.map em)
      = ∫ y, (∫ x, Φ x * χ x (em y) ∂(μ.map em)) * χ (em y) z ∂μ := integral_map_equiv em _
    _ = ∫ y, (∫ x, (Φ ∘ em) x * χ x y ∂μ) * χ y (em.symm z) ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        show (∫ x, Φ x * χ x (em y) ∂(μ.map em)) * χ (em y) z =
          (∫ x, (Φ ∘ em) x * χ x y ∂μ) * χ y (em.symm z)
        rw [hinner y, hz y]
    _ = (Φ ∘ em) (-(em.symm z)) := hμ.2 (Φ ∘ em) hc' hs' hint' (em.symm z)
    _ = Φ (-z) := by simp only [Function.comp_apply, hneg, MeasurableEquiv.apply_symm_apply]

/- English proof (translation)
Establish `hc : ∀ h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J, Continuous (fun y : TupI X => h • y)`. Introduce `h`. Use `first`. Consider the case `fun_prop`. Consider the case `(simp only [HSMul.hSMul, SMul.smul]; unfold actTup; fun_prop)`.

Consider the case `(simp only [HSMul.hSMul, SMul.smul]; unfold actTup;`. Conclude with `continuous_pi fun a => Continuous.matrix_mulVec continuous_const (continuous_apply a))`. Set `e : TupI X ≃ₜ TupI X` to `{ toEquiv := (smulAE X g).toEquiv continuous_toFun := hc g continuous_invFun := hc g⁻¹ }`. Establish `hH : (μ.map e.toMeasurableEquiv).IsAddHaarMeasure` using `by haveI := hμ.1 first`. Consider the case `exact (smulAE X g).isAddHaarMeasure_map μ (hc g) (hc g⁻¹)`.

Consider the case `exact (smulAE X g).isAddHaarMeasure_map (hc g) (hc g⁻¹)`. Conclude with `selfDual_map_of_isAddHaarMeasure μ (fun X' Y' : TupI X => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J X' Y')) e.toMeasurableEquiv hH (fun a b => by show psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (g • a) (g • b)) = psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X. …`. Rewrite using `[BR_smul])`. Use the proof step `(fun a => smul_neg_tup X g a)`. Use the proof step `(fun Φ hΦc hΦs => ⟨hΦc.comp e.continuous, hΦs.comp_homeomorph e⟩) hμ`.
-/
theorem selfDual_map {D : D7} (X : HidaSetting D) (ψ : AddChar (AF X.B.I.F) ℂ) (μ : Measure (TupI X))
    (hμ : SelfDual μ (fun X' Y' : TupI X => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J X' Y'))) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :
    SelfDual (μ.map (fun y => g • y)) (fun X' Y' : TupI X => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J X' Y')) := by
  have hc : ∀ h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J, Continuous (fun y : TupI X => h • y) := by
    intro h
    first
    | fun_prop
    | (simp only [HSMul.hSMul, SMul.smul]; unfold actTup; fun_prop)
    | (simp only [HSMul.hSMul, SMul.smul]; unfold actTup;
        exact continuous_pi fun a => Continuous.matrix_mulVec continuous_const (continuous_apply a))
  let e : TupI X ≃ₜ TupI X :=
    { toEquiv := (smulAE X g).toEquiv
      continuous_toFun := hc g
      continuous_invFun := hc g⁻¹ }
  have hH : (μ.map e.toMeasurableEquiv).IsAddHaarMeasure := by
    haveI := hμ.1
    first
    | exact (smulAE X g).isAddHaarMeasure_map μ (hc g) (hc g⁻¹)
    | exact (smulAE X g).isAddHaarMeasure_map (hc g) (hc g⁻¹)
  exact selfDual_map_of_isAddHaarMeasure μ
    (fun X' Y' : TupI X => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J X' Y'))
    e.toMeasurableEquiv hH
    (fun a b => by
      show psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (g • a) (g • b)) =
        psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J a b)
      rw [BR_smul])
    (fun a => smul_neg_tup X g a)
    (fun Φ hΦc hΦs => ⟨hΦc.comp e.continuous, hΦs.comp_homeomorph e⟩) hμ

def SdTestI : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    ∃ Φ : TupI X → ℂ, Continuous Φ ∧ HasCompactSupport Φ ∧
      Integrable (fun y => ∫ x, Φ x * psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y) ∂μinf) μinf ∧
      ∃ z, Φ (-z) ≠ 0

/- English proof (translation)
Establish `hin : ∀ y, ∫ x, Φ x * χ x y ∂(c • μ) = (c.toReal : ℂ) * ∫ x, Φ x * χ x y ∂μ`. Introduce `y`. Rewrite using `[integral_smul_measure, Complex.real_smul]`. Establish `hi' : Integrable (fun y => ∫ x, Φ x * χ x y ∂(c • μ)) (c • μ)`. Simplify using `only [hin]`.

Conclude with `(hi.const_mul _).smul_measure hctop`. Establish `key` using `hν.2 Φ hc hs hi' z`. Simplify using `only [hin] at key`. Rewrite `key` using `[integral_smul_measure, Complex.real_smul]`. Simplify using `only [mul_assoc] at key`.

Rewrite `key` using `[integral_const_mul, hμ.2 Φ hc hs hi z]`. Establish `h2 : ((c.toReal : ℂ) * c.toReal - 1) * Φ (-z) = 0` using `by linear_combination key`. Establish `h3 : (c.toReal : ℂ) * c.toReal = 1`. Establish `h3'` using `(mul_eq_zero.mp h2).resolve_right hz`. Take the linear combination `h3'`.

Establish `h4 : c.toReal * c.toReal = 1` using `by exact_mod_cast h3`. Establish `h5 : c.toReal = 1`. Break down `mul_self_eq_one_iff.mp h4 with h | h` into its components or cases. Conclude with `h`. Combine the linear relations using `[ENNReal.toReal_nonneg (a := c)]`.

Use `first`. Consider the case `exact (ENNReal.toReal_eq_one_iff c).mp h5`. Consider the case `rw [← ENNReal.ofReal_toReal hctop, h5, ENNReal.ofReal_one]`.
-/
private theorem eq_one_of_selfDual_smul {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
    (μ : Measure V) (c : ENNReal) (hctop : c ≠ ⊤) (χ : V → V → ℂ) (hμ : SelfDual μ χ)
    (hν : SelfDual (c • μ) χ) (Φ : V → ℂ) (hc : Continuous Φ) (hs : HasCompactSupport Φ)
    (hi : Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ) (z : V) (hz : Φ (-z) ≠ 0) : c = 1 := by
  have hin : ∀ y, ∫ x, Φ x * χ x y ∂(c • μ) = (c.toReal : ℂ) * ∫ x, Φ x * χ x y ∂μ := by
    intro y
    rw [integral_smul_measure, Complex.real_smul]
  have hi' : Integrable (fun y => ∫ x, Φ x * χ x y ∂(c • μ)) (c • μ) := by
    simp only [hin]
    exact (hi.const_mul _).smul_measure hctop
  have key := hν.2 Φ hc hs hi' z
  simp only [hin] at key
  rw [integral_smul_measure, Complex.real_smul] at key
  simp only [mul_assoc] at key
  rw [integral_const_mul, hμ.2 Φ hc hs hi z] at key
  have h2 : ((c.toReal : ℂ) * c.toReal - 1) * Φ (-z) = 0 := by linear_combination key
  have h3 : (c.toReal : ℂ) * c.toReal = 1 := by
    have h3' := (mul_eq_zero.mp h2).resolve_right hz
    linear_combination h3'
  have h4 : c.toReal * c.toReal = 1 := by exact_mod_cast h3
  have h5 : c.toReal = 1 := by
    rcases mul_self_eq_one_iff.mp h4 with h | h
    · exact h
    · linarith [ENNReal.toReal_nonneg (a := c)]
  first
  | exact (ENNReal.toReal_eq_one_iff c).mp h5
  | rw [← ENNReal.ofReal_toReal hctop, h5, ENNReal.ofReal_one]

/- English proof (translation)
Unfold `SdInvG`. Introduce `D X u' ψ hT' μinf νinf fibInf hP g`. Establish `hμ : SelfDual μinf (fun X' Y' : TupI X => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J X' Y'))` using `hP.2.2.2.2.1`. Take `⟨Φ, hΦc, hΦs, hΦi, z, hz⟩` from `hT X u' ψ hT' μinf νinf fibInf hP`. Establish `hν` using `selfDual_map X ψ μinf hμ g`.

Use `haveI := hμ.1`. Use `haveI := hν.1`. Choose the witnesses or unpack the hypotheses as in `⟨c, hctop, hc⟩ : ∃ c : ENNReal, c ≠ ⊤ ∧ μinf.map (fun y => g • y) = c • μinf := by`. Use `⟨(Measure.addHaarScalarFactor (μinf.map fun y => g • y) μinf : ENNReal), ENNReal.coe_ne_top, (Measure.isAddLeftInvariant_eq_smul (μinf.map fun y => g • y) μinf).trans ?_⟩` and prove the remaining obligations. Use extensionality with `s _`.

Simplify using `[Measure.smul_apply]`. Rewrite `hν` using `[hc]`. Rewrite using `[hc]`. Establish `hc1 : c = 1` using `eq_one_of_selfDual_smul μinf c hctop _ hμ hν Φ hΦc hΦs hΦi z hz`. Rewrite using `[hc1, one_smul]`.
-/
theorem sdInvG_of (hT : SdTestI) : SdInvG := by
  unfold SdInvG
  intro D X u' ψ hT' μinf νinf fibInf hP g
  have hμ : SelfDual μinf
      (fun X' Y' : TupI X => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J X' Y')) :=
    hP.2.2.2.2.1
  obtain ⟨Φ, hΦc, hΦs, hΦi, z, hz⟩ := hT X u' ψ hT' μinf νinf fibInf hP
  have hν := selfDual_map X ψ μinf hμ g
  haveI := hμ.1
  haveI := hν.1
  obtain ⟨c, hctop, hc⟩ : ∃ c : ENNReal, c ≠ ⊤ ∧ μinf.map (fun y => g • y) = c • μinf := by
    refine ⟨(Measure.addHaarScalarFactor (μinf.map fun y => g • y) μinf : ENNReal), ENNReal.coe_ne_top,
      (Measure.isAddLeftInvariant_eq_smul (μinf.map fun y => g • y) μinf).trans ?_⟩
    ext s _
    simp [Measure.smul_apply]
  rw [hc] at hν
  rw [hc]
  have hc1 : c = 1 :=
    eq_one_of_selfDual_smul μinf c hctop _ hμ hν Φ hΦc hΦs hΦi z hz
  rw [hc1, one_smul]

end PI.AprimeInfW
