import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaPairCompactLineAction
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MemPolarizationStabilizerOfDualPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaPairCompactLineActionStatement

section
open NumberField IsDedekindDomain
noncomputable section
namespace GlobalTheory.KExpLineW
section Abstract
variable {α : Type}
end Abstract
end GlobalTheory.KExpLineW
namespace GlobalTheory.KExpLineW
section Orbit
variable {α : Type}
end Orbit
end GlobalTheory.KExpLineW
namespace GlobalTheory.KExpLineW
open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
end GlobalTheory.KExpLineW
namespace GlobalTheory.KExpLineW
open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
/- English proof (translation)
Introduce `hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP γ hγL hγK N hN Φ hΦN hΦ`. Take `⟨-, -, hDer, hOp⟩` from `_root_.GlobalTheory.T.dualPair_preserves_polarization hPr F E σ B n d X W M χX χW om r s r' s' hP`. Take `⟨Dg, hDgP, hDg⟩` from `hDer γ hγL`. Use `choose D hDP hD using fun t : ℝ => hOp (γ (Multiplicative.ofAdd t)) (hγK _)`. Set `U : Multiplicative ℝ →* Module.End ℂ (Fn F n d)` to `om.comp ((MonoidHom.inr (UA σ X.J) (UA σ W.J)).comp γ)`.

Establish `hdiff : ∀ Ψ ∈ PolData B M, ∀ x (t : ℝ), DifferentiableAt ℝ (fun s : ℝ => U (Multiplicative.ofAdd s) Ψ x) t`. Introduce `Ψ hΨ x`. Proceed by induction on `hΨ using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨f, hf, φ, hφ, hvac, rfl⟩` from `hy`.

Introduce `t`. Establish `hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1` using `(hvac.and hP.good.std).mono fun _ h => h.1.trans h.2`. Establish `hpt : ∀ u : ℝ, U (Multiplicative.ofAdd u) (pure f φ) = pure (D u f) φ` using `fun u => map_pure M B.ψ hP.good _ f (D u f) ((hD u f hf (D u f)).2 rfl) φ hφ hvac`. Establish `hshift : ∀ s', U (Multiplicative.ofAdd (s' + t)) (pure f φ) = U (Multiplicative.ofAdd s') (pure (D t f) φ)`. Introduce `s'`.

Rewrite using `[ofAdd_add, map_mul, Module.End.mul_apply, hpt t]`. Establish `h0` using `(hDg (D t f) (hDP t f hf) (Dg (D t f))).2 rfl _ (GlobalTheory.ThK.EvUniqInf.rest_pure (D t f) φ hφ hstd) x`. Establish `h0' : DifferentiableAt ℝ (fun s' : ℝ => U (Multiplicative.ofAdd s') (pure (D t f) φ) x) 0` using `h0.differentiableAt`. Establish `e : (fun s : ℝ => U (Multiplicative.ofAdd s) (pure f φ) x) = (fun s' : ℝ => U (Multiplicative.ofAdd s') (pure (D t f) φ) x) ∘ fun s => s - t`. Use function extensionality and compare the values at `s`.

Use `show _ = U (Multiplicative.ofAdd (s - t)) (pure (D t f) φ) x`. Rewrite using `[← hshift, sub_add_cancel]`. Establish `h4 : DifferentiableAt ℝ (fun s' : ℝ => U (Multiplicative.ofAdd s') (pure (D t f) φ) x) ((fun s : ℝ => s - t) t)`. Simplify using `only [sub_self]`. Conclude with `h0'`.

Rewrite using `[e]`. Conclude with `DifferentiableAt.comp (f := fun s : ℝ => s - t) t h4 (differentiableAt_id.sub_const t)`. Consider the case `zero`. Introduce `t`. Simplify using `only [map_zero, Pi.zero_apply]`.

Conclude with `differentiableAt_const _`. Consider the case `add y z _ _ hy hz`. Introduce `t`. Simplify using `only [map_add, Pi.add_apply]`. Conclude with `(hy t).add (hz t)`.

Consider the case `smul a y _ hy`. Introduce `t`. Simplify using `only [map_smul, Pi.smul_apply, smul_eq_mul]`. Conclude with `(hy t).const_mul a`. Take `⟨C, hCfin, hCP, hCk⟩` from `polData_kfin F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ`.

Use `haveI := hCfin`. Conclude with `orbit_mem U (PolData B M) N C hCP (fun Ψ h Ψ₁ h₁ hd => hN Ψ h Ψ₁ h₁ hd) Φ hΦN (fun t => hCk _ (hγK _)) (hdiff Φ hΦ) 1`.
-/
theorem KExpLine_stabilizes_line : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W, (∀ t, γ t ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W B.emb) →
    ∀ N : Submodule ℂ (GlobalTheory.ThK.Fn F n d),
      (∀ Ψ ∈ N, ∀ Ψ₁ ∈ GlobalTheory.ThK.PolData B M,
        (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Ψ x) (Ψ₁ x) 0) → Ψ₁ ∈ N) →
      ∀ Φ ∈ N, Φ ∈ GlobalTheory.ThK.PolData B M → om (1, γ (Multiplicative.ofAdd (1 : ℝ))) Φ ∈ N := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP γ hγL hγK N hN Φ hΦN hΦ
  obtain ⟨-, -, hDer, hOp⟩ := _root_.GlobalTheory.T.dualPair_preserves_polarization hPr F E σ B n d X W M χX χW om r s r' s' hP
  obtain ⟨Dg, hDgP, hDg⟩ := hDer γ hγL
  choose D hDP hD using fun t : ℝ => hOp (γ (Multiplicative.ofAdd t)) (hγK _)
  let U : Multiplicative ℝ →* Module.End ℂ (Fn F n d) := om.comp ((MonoidHom.inr (UA σ X.J) (UA σ W.J)).comp γ)
  have hdiff : ∀ Ψ ∈ PolData B M, ∀ x (t : ℝ),
      DifferentiableAt ℝ (fun s : ℝ => U (Multiplicative.ofAdd s) Ψ x) t := by
    intro Ψ hΨ x
    induction hΨ using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, φ, hφ, hvac, rfl⟩ := hy
      intro t
      have hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
        (hvac.and hP.good.std).mono fun _ h => h.1.trans h.2
      have hpt : ∀ u : ℝ, U (Multiplicative.ofAdd u) (pure f φ) = pure (D u f) φ := fun u =>
        map_pure M B.ψ hP.good _ f (D u f) ((hD u f hf (D u f)).2 rfl) φ hφ hvac
      have hshift : ∀ s', U (Multiplicative.ofAdd (s' + t)) (pure f φ) =
          U (Multiplicative.ofAdd s') (pure (D t f) φ) := by
        intro s'
        rw [ofAdd_add, map_mul, Module.End.mul_apply, hpt t]
      have h0 := (hDg (D t f) (hDP t f hf) (Dg (D t f))).2 rfl _
        (GlobalTheory.ThK.EvUniqInf.rest_pure (D t f) φ hφ hstd) x
      have h0' : DifferentiableAt ℝ (fun s' : ℝ => U (Multiplicative.ofAdd s') (pure (D t f) φ) x) 0 :=
        h0.differentiableAt
      have e : (fun s : ℝ => U (Multiplicative.ofAdd s) (pure f φ) x) =
          (fun s' : ℝ => U (Multiplicative.ofAdd s') (pure (D t f) φ) x) ∘ fun s => s - t := by
        funext s
        show _ = U (Multiplicative.ofAdd (s - t)) (pure (D t f) φ) x
        rw [← hshift, sub_add_cancel]
      have h4 : DifferentiableAt ℝ (fun s' : ℝ => U (Multiplicative.ofAdd s') (pure (D t f) φ) x)
          ((fun s : ℝ => s - t) t) := by
        simp only [sub_self]
        exact h0'
      rw [e]
      exact DifferentiableAt.comp (f := fun s : ℝ => s - t) t h4 (differentiableAt_id.sub_const t)
    | zero =>
      intro t
      simp only [map_zero, Pi.zero_apply]
      exact differentiableAt_const _
    | add y z _ _ hy hz =>
      intro t
      simp only [map_add, Pi.add_apply]
      exact (hy t).add (hz t)
    | smul a y _ hy =>
      intro t
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      exact (hy t).const_mul a
  obtain ⟨C, hCfin, hCP, hCk⟩ := polData_kfin F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  haveI := hCfin
  exact orbit_mem U (PolData B M) N C hCP (fun Ψ h Ψ₁ h₁ hd => hN Ψ h Ψ₁ h₁ hd) Φ hΦN
    (fun t => hCk _ (hγK _)) (hdiff Φ hΦ) 1
end GlobalTheory.KExpLineW
end
end

section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.KExpLineW.KExpLine_stabilizes_line | exact _root_.GlobalTheory.KExpLineW.KExpLine_stabilizes_line | (intros; apply _root_.GlobalTheory.KExpLineW.KExpLine_stabilizes_line <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.stabilizer_of_K_exponential_line : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W, (∀ t, γ t ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W B.emb) →
    ∀ N : Submodule ℂ (GlobalTheory.ThK.Fn F n d),
      (∀ Ψ ∈ N, ∀ Ψ₁ ∈ GlobalTheory.ThK.PolData B M,
        (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Ψ x) (Ψ₁ x) 0) → Ψ₁ ∈ N) →
      ∀ Φ ∈ N, Φ ∈ GlobalTheory.ThK.PolData B M → om (1, γ (Multiplicative.ofAdd (1 : ℝ))) Φ ∈ N := by
  first | exact @_root_.GlobalTheory.KExpLineW.KExpLine_stabilizes_line | exact _root_.GlobalTheory.KExpLineW.KExpLine_stabilizes_line | (intros; apply _root_.GlobalTheory.KExpLineW.KExpLine_stabilizes_line <;> assumption)
end
