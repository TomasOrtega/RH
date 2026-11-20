import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.GlobalFields.TateThesis.AdeleScaling
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.CdMeas

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem diag_val (F : Type) [Field F] [NumberField F] (t : Fˣ) :
    ((IdeleGroup.diagonal F t : (A F)ˣ) : A F) = rt (t : F) := rfl

/- English proof (translation)
Rewrite using `[← map_inv, ← Units.val_inv_eq_inv_val]`. Both sides reduce to the same expression.
-/
private theorem diag_inv_val (F : Type) [Field F] [NumberField F] (t : Fˣ) :
    (((IdeleGroup.diagonal F t : (A F)ˣ)⁻¹ : (A F)ˣ) : A F) = rt ((t : F)⁻¹) := by
  rw [← map_inv, ← Units.val_inv_eq_inv_val]
  rfl

private def cR {F : Type} [Field F] (t : Fˣ) (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![g 0 0, g 0 1 * (t : F)⁻¹; (t : F) * g 1 0, g 1 1], by
    have h := g.det_coe
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_two_of]
    have ht : (t : F) ≠ 0 := t.ne_zero
    have : g 0 1 * (t : F)⁻¹ * ((t : F) * g 1 0) = g 0 1 * g 1 0 := by field_simp
    rw [this]
    exact h⟩

/- English proof (translation)
Use `Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[M.val_ratS]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `[cD, cR, M.val_ratS, diag_inv_val, diag_val, rt, map_mul]`.
-/
private theorem cD_ratS {F : Type} [Field F] [NumberField F] (t : Fˣ)
    (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    cD (IdeleGroup.diagonal F t) (ratS F g) = ratS F (cR t g) := by
  refine Subtype.ext ?_
  rw [M.val_ratS]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cD, cR, M.val_ratS, diag_inv_val, diag_val, rt, map_mul]

/- English proof (translation)
Take `⟨g, rfl⟩` from `hx`. Conclude with `⟨cR t g, (cD_ratS t g).symm⟩`.
-/
private theorem cD_mem {F : Type} [Field F] [NumberField F] (t : Fˣ) {x : G1 F} (hx : x ∈ Gam F) :
    cD (IdeleGroup.diagonal F t) x ∈ Gam F := by
  obtain ⟨g, rfl⟩ := hx
  exact ⟨cR t g, (cD_ratS t g).symm⟩

/- English proof (translation)
Introduce `F _ _ M₀ u hu t`. Use `haveI := M₀.haar`. Use `set T : (A F)ˣ := IdeleGroup.diagonal F t with hT`. Establish `hTi : T⁻¹ = IdeleGroup.diagonal F t⁻¹` using `by rw [hT, map_inv]`. Set `e : G1 F ≃ₜ G1 F` to `{ toFun := cD T invFun := cD T⁻¹ left_inv := fun g => by rw [M.cD_cD, inv_mul_cancel, M.cD_one] right_inv := fun g => by rw [M.cD_cD, mul_inv_cancel, M.cD_one] continuous_toFun := M.continuous_cD T continuous_invFun := M.continuous_cD T⁻¹ }`.

Set `eG : Gam F ≃ Gam F` to `{ toFun := fun γ => ⟨cD T⁻¹ γ.1, by rw [hTi]; exact cD_mem t⁻¹ γ.2⟩ invFun := fun γ => ⟨cD T γ.1, cD_mem t γ.2⟩ left_inv := fun γ => Subtype.ext (by show cD T (cD T⁻¹ γ.1) = γ.1`. Rewrite using `[M.cD_cD, mul_inv_cancel, M.cD_one])`. Use `right_inv := fun γ => Subtype.ext (by show cD T⁻¹ (cD T γ.1) = γ.1`. Rewrite using `[M.cD_cD, inv_mul_cancel, M.cD_one]) }`. Establish `hmp : MeasurePreserving (cD T) M₀.μ M₀.μ` using `M.cdMeas F M₀ T`.

Establish `hmpi : MeasurePreserving (cD T⁻¹) M₀.μ M₀.μ` using `M.cdMeas F M₀ T⁻¹`. Establish `hemb : MeasurableEmbedding (cD T : G1 F → G1 F)` using `e.measurableEmbedding`. Establish `hD' : IsFundamentalDomain (Gam F) (cD T '' M₀.D) M₀.μ` using `M₀.fund.image_of_equiv e.toEquiv hmpi.quasiMeasurePreserving eG (fun γ x => by show cD T (cD T⁻¹ γ.1 * x) = γ.1 * cD T x`. Rewrite using `[M.cD_mul, M.cD_cD, mul_inv_cancel, M.cD_one])`. Establish `hpre : cD T ⁻¹' (cD T '' M₀.D) = M₀.D` using `Set.preimage_image_eq _ e.injective`.

Establish `hinv : ∀ (γ : Gam F) (x : G1 F), u (γ • x) = u x`. Introduce and unpack `⟨_, γ, rfl⟩ x`. Conclude with `hu γ x`. Prove the components needed by the constructor for the conclusion. Establish `h1` using `hmp.integrableOn_comp_preimage hemb (f := u) (s := cD T '' M₀.D)`.

Rewrite `h1` using `[hpre]`. Conclude with `h1.trans (hD'.integrableOn_iff M₀.fund hinv)`. Establish `h1` using `hmp.setIntegral_preimage_emb hemb u (cD T '' M₀.D)`. Rewrite `h1` using `[hpre]`. Conclude with `h1.trans (hD'.setIntegral_eq M₀.fund hinv)`.
-/
theorem UpperTheory.ConvolutionTheory.R2.M.dConj :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (u : G1 F → ℂ), (∀ γ g, u (ratS F γ * g) = u g) → ∀ t : Fˣ, (IntegrableOn (fun g => u (cD (IdeleGroup.diagonal F t) g)) M₀.D M₀.μ ↔ IntegrableOn u M₀.D M₀.μ) ∧ ∫ g in M₀.D, u (cD (IdeleGroup.diagonal F t) g) ∂M₀.μ = ∫ g in M₀.D, u g ∂M₀.μ := by
  intro F _ _ M₀ u hu t
  haveI := M₀.haar
  set T : (A F)ˣ := IdeleGroup.diagonal F t with hT
  have hTi : T⁻¹ = IdeleGroup.diagonal F t⁻¹ := by rw [hT, map_inv]
  let e : G1 F ≃ₜ G1 F :=
    { toFun := cD T
      invFun := cD T⁻¹
      left_inv := fun g => by rw [M.cD_cD, inv_mul_cancel, M.cD_one]
      right_inv := fun g => by rw [M.cD_cD, mul_inv_cancel, M.cD_one]
      continuous_toFun := M.continuous_cD T
      continuous_invFun := M.continuous_cD T⁻¹ }
  let eG : Gam F ≃ Gam F :=
    { toFun := fun γ => ⟨cD T⁻¹ γ.1, by rw [hTi]; exact cD_mem t⁻¹ γ.2⟩
      invFun := fun γ => ⟨cD T γ.1, cD_mem t γ.2⟩
      left_inv := fun γ => Subtype.ext (by
        show cD T (cD T⁻¹ γ.1) = γ.1
        rw [M.cD_cD, mul_inv_cancel, M.cD_one])
      right_inv := fun γ => Subtype.ext (by
        show cD T⁻¹ (cD T γ.1) = γ.1
        rw [M.cD_cD, inv_mul_cancel, M.cD_one]) }
  have hmp : MeasurePreserving (cD T) M₀.μ M₀.μ := M.cdMeas F M₀ T
  have hmpi : MeasurePreserving (cD T⁻¹) M₀.μ M₀.μ := M.cdMeas F M₀ T⁻¹
  have hemb : MeasurableEmbedding (cD T : G1 F → G1 F) := e.measurableEmbedding
  have hD' : IsFundamentalDomain (Gam F) (cD T '' M₀.D) M₀.μ :=
    M₀.fund.image_of_equiv e.toEquiv hmpi.quasiMeasurePreserving eG (fun γ x => by
      show cD T (cD T⁻¹ γ.1 * x) = γ.1 * cD T x
      rw [M.cD_mul, M.cD_cD, mul_inv_cancel, M.cD_one])
  have hpre : cD T ⁻¹' (cD T '' M₀.D) = M₀.D := Set.preimage_image_eq _ e.injective
  have hinv : ∀ (γ : Gam F) (x : G1 F), u (γ • x) = u x := by
    rintro ⟨_, γ, rfl⟩ x
    exact hu γ x
  constructor
  · have h1 := hmp.integrableOn_comp_preimage hemb (f := u) (s := cD T '' M₀.D)
    rw [hpre] at h1
    exact h1.trans (hD'.integrableOn_iff M₀.fund hinv)
  · have h1 := hmp.setIntegral_preimage_emb hemb u (cD T '' M₀.D)
    rw [hpre] at h1
    exact h1.trans (hD'.setIntegral_eq M₀.fund hinv)
