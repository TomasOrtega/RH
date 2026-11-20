import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralArchimedeanInvariant
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaKernelFundamentalProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralArchimedeanInvariantStatement

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
noncomputable section
namespace GlobalTheory.ThetaRightTranslate
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp g _ h Φ hΦ y`. Establish `hTB` using `_root_.GlobalTheory.T.theta_kernel_fundamental_properties hP F E σ B n d X W M χX χW om r s r' s' hp`. Establish `hinv : ∀ γ ∈ ratU σ X.J, ∀ x, theta om Φ (γ * x) (y * h) = theta om Φ x (y * h)`. Introduce `γ hγ x`. Use `(hTB.1 Φ hΦ).2.1 γ hγ 1 (one_mem _) x (y * h)` as an intermediate fact.

Rewrite `this` using `[one_mul]`. Then use the resulting hypothesis. Use `haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _`. Use `haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩`. Use `haveI := hp.good.haar`. Use `haveI : M.μ.IsMulRightInvariant := isMulRightInvariant σ hp.base.cm X.J hp.herm.herm (GlobalTheory.isUnit_det_of_isHerm F E σ B n X r s hp.herm) M.μ`.

Use `haveI := countable_ratU σ X.J`. Use `haveI : MeasurableConstSMul (ratU σ X.J) (UA σ X.J) := ⟨fun c => measurable_const_mul (c : UA σ X.J)⟩`. Use `haveI : SMulInvariantMeasure (ratU σ X.J) (UA σ X.J) M.μ := ⟨fun c s _ => measure_preimage_mul M.μ (c : UA σ X.J) s⟩`. Establish `hL : M.I om (om (g, h) Φ) y = ∫ x in M.dom, theta om Φ (x * g) (y * h) ∂M.μ`. Unfold `Model.I theta`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Both sides reduce to the same expression. Establish `hmp` using `measurePreserving_mul_right M.μ g`.

Establish `h1` using `hmp.setIntegral_preimage_emb (measurableEmbedding_mulRight g) (fun x => theta om Φ x (y * h)) ((fun x : UA σ X.J => x * g⁻¹) ⁻¹' M.dom)`. Establish `hpre : (fun x : UA σ X.J => x * g) ⁻¹' ((fun x : UA σ X.J => x * g⁻¹) ⁻¹' M.dom) = M.dom`. Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite `h1` using `[hpre]`.

Establish `hfd' : IsFundamentalDomain (ratU σ X.J) ((fun x : UA σ X.J => x * g⁻¹) ⁻¹' M.dom) M.μ` using `hp.good.dom.preimage_of_equiv (measurePreserving_mul_right M.μ g⁻¹).quasiMeasurePreserving (e := id) Function.bijective_id (fun γ x => by show (γ.1 * x) * g⁻¹ = γ.1 * (x * g⁻¹)`. Conclude with `mul_assoc _ _ _)`. Establish `h2` using `hfd'.setIntegral_eq hp.good.dom (f := fun x => theta om Φ x (y * h)) (fun γ x => hinv γ.1 γ.2 x)`. Rewrite using `[hL, h1, h2]`. Both sides reduce to the same expression.
-/
theorem thetaIntegral_rightTranslate_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ g ∈ UAt σ X (evI F), ∀ (h : UA σ W.J) (Φ : (Fin n × Fin d → AF F) → ℂ),
      Φ ∈ schA F (Fin n × Fin d) → ∀ y, M.I om (om (g, h) Φ) y = M.I om Φ (y * h) := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp g _ h Φ hΦ y
  have hTB := _root_.GlobalTheory.T.theta_kernel_fundamental_properties hP F E σ B n d X W M χX χW om r s r' s' hp
  have hinv : ∀ γ ∈ ratU σ X.J, ∀ x, theta om Φ (γ * x) (y * h) = theta om Φ x (y * h) := by
    intro γ hγ x
    have := (hTB.1 Φ hΦ).2.1 γ hγ 1 (one_mem _) x (y * h)
    rwa [one_mul] at this
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI := hp.good.haar
  haveI : M.μ.IsMulRightInvariant := isMulRightInvariant σ hp.base.cm X.J hp.herm.herm
    (GlobalTheory.isUnit_det_of_isHerm F E σ B n X r s hp.herm) M.μ
  haveI := countable_ratU σ X.J
  haveI : MeasurableConstSMul (ratU σ X.J) (UA σ X.J) := ⟨fun c => measurable_const_mul (c : UA σ X.J)⟩
  haveI : SMulInvariantMeasure (ratU σ X.J) (UA σ X.J) M.μ :=
    ⟨fun c s _ => measure_preimage_mul M.μ (c : UA σ X.J) s⟩
  have hL : M.I om (om (g, h) Φ) y = ∫ x in M.dom, theta om Φ (x * g) (y * h) ∂M.μ := by
    unfold Model.I theta
    congr 1
    funext x
    rw [← Module.End.mul_apply, ← map_mul]
    rfl
  have hmp := measurePreserving_mul_right M.μ g
  have h1 := hmp.setIntegral_preimage_emb (measurableEmbedding_mulRight g) (fun x => theta om Φ x (y * h))
    ((fun x : UA σ X.J => x * g⁻¹) ⁻¹' M.dom)
  have hpre : (fun x : UA σ X.J => x * g) ⁻¹' ((fun x : UA σ X.J => x * g⁻¹) ⁻¹' M.dom) = M.dom := by
    ext x; simp
  rw [hpre] at h1
  have hfd' : IsFundamentalDomain (ratU σ X.J) ((fun x : UA σ X.J => x * g⁻¹) ⁻¹' M.dom) M.μ :=
    hp.good.dom.preimage_of_equiv (measurePreserving_mul_right M.μ g⁻¹).quasiMeasurePreserving
      (e := id) Function.bijective_id (fun γ x => by
        show (γ.1 * x) * g⁻¹ = γ.1 * (x * g⁻¹)
        exact mul_assoc _ _ _)
  have h2 := hfd'.setIntegral_eq hp.good.dom (f := fun x => theta om Φ x (y * h)) (fun γ x => hinv γ.1 γ.2 x)
  rw [hL, h1, h2]
  rfl
end GlobalTheory.ThetaRightTranslate
end
end

section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.ThetaRightTranslate.thetaIntegral_rightTranslate_eq | exact _root_.GlobalTheory.ThetaRightTranslate.thetaIntegral_rightTranslate_eq | (intros; apply _root_.GlobalTheory.ThetaRightTranslate.thetaIntegral_rightTranslate_eq <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.thetaIntegral_comp_rightTranslate : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ g ∈ UAt σ X (evI F), ∀ (h : UA σ W.J) (Φ : (Fin n × Fin d → AF F) → ℂ),
      Φ ∈ schA F (Fin n × Fin d) → ∀ y, M.I om (om (g, h) Φ) y = M.I om Φ (y * h) := by
  first | exact @_root_.GlobalTheory.ThetaRightTranslate.thetaIntegral_rightTranslate_eq | exact _root_.GlobalTheory.ThetaRightTranslate.thetaIntegral_rightTranslate_eq | (intros; apply _root_.GlobalTheory.ThetaRightTranslate.thetaIntegral_rightTranslate_eq <;> assumption)
end
