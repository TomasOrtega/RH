import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedSpaceVecPairAsAdeles
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivedActionIntertwinesOfGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfLieIntertwineL2Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharArchimedeanExpRealLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealTraceArchimedeanEmbeddingsNondegenerateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSqCompContinuousLinearEquivMixedSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearModelArchimedeanSchroedingerStandardStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilAdm

/- English proof (translation)
Introduce `D ps hψ κ _ L A C hC hA hI`. Take `⟨θ, hθ⟩` from `hψ.2.1`. Take `⟨β, hβ1, hβ2⟩` from `GlobalTheory.T.standardAddChar_archimedean_exp_realLinear D ps θ hψ hθ`. Establish `hnd : ∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0`. Introduce `a ha`.

Establish `ha' : (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm a ≠ 0`. Simplify using `using ha`. Take `⟨b, hb⟩` from `GlobalTheory.T.realTrace_archimedeanEmbeddings_nondegenerate D θ hθ _ ha'`. Use `⟨InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F b, ?_⟩` and prove the remaining obligations. Rewrite using `[hβ2, map_mul, RingEquiv.symm_apply_apply]`.

Simplify using `using hb`. Take `⟨n, Q, P, hQP⟩` from `GlobalTheory.T.exists_linear_model_archimedean_schroedinger_standard D.host.F ps β hβ1 hnd κ`. Take `⟨c, hc⟩` from `GlobalTheory.T.lintegral_sq_comp_continuousLinearEquiv_mixedSpace D.host.F κ n Q`. Set `CQ` to `SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) Q`. Set `CQi` to `SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) Q.symm`.

Establish `hCQ : ∀ f, ⇑(CQ f) = ⇑f ∘ ⇑Q` using `fun f => SchwartzMap.compCLMOfContinuousLinearEquiv_apply ℂ Q f`. Establish `hCQi : ∀ g, ⇑(CQi g) = ⇑g ∘ ⇑Q.symm` using `fun g => SchwartzMap.compCLMOfContinuousLinearEquiv_apply ℂ Q.symm g`. Establish `hQQ : ∀ f, CQi (CQ f) = f` using `fun f => by`. Use extensionality with `z`. Rewrite using `[hCQi, hCQ]`.

Simplify using the standard rewrite rules. Establish `hQQ' : ∀ g, CQ (CQi g) = g` using `fun g => by`. Use extensionality with `z`. Rewrite using `[hCQ, hCQi]`. Simplify using the standard rewrite rules.

Set `A' : GlobalTheory.RealWeil.Sch (Fin n) →ₗ[ℂ] GlobalTheory.RealWeil.Sch (Fin n)` to `CQ.toLinearMap ∘ₗ A ∘ₗ CQi.toLinearMap`. Establish `hA'apply : ∀ g, A' g = CQ (A (CQi g))` using `fun g => rfl`. Set `L' : (Fin n ⊕ Fin n → ℝ) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)` to `P.trans (L.trans P.symm)`. Establish `hbound : ∀ g, ∫⁻ x, ‖A' g x‖ₑ ^ 2 ≤ C * ∫⁻ x, ‖g x‖ₑ ^ 2`. Introduce `g`.

Establish `e1 : ∫⁻ x, ‖A' g x‖ₑ ^ 2 = c * ∫⁻ z, ‖A (CQi g) z‖ₑ ^ 2`. Rewrite using `[← hc]`. Simplify using `only [hA'apply, hCQ, Function.comp_apply]`. Establish `e2 : ∫⁻ x, ‖g x‖ₑ ^ 2 = c * ∫⁻ z, ‖CQi g z‖ₑ ^ 2`. Rewrite using `[← hc]`.

Simplify using `only [hCQi, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]`. Rewrite using `[e1, e2, ← mul_assoc, mul_comm C c, mul_assoc]`. Conclude with `mul_le_mul' le_rfl (hA _)`. Establish `hint : ∀ w (g g' : GlobalTheory.RealWeil.Sch (Fin n)), ⇑g' = GlobalTheory.RealWeil.rhoFun w ⇑g → ⇑(A' g') = GlobalTheory.RealWeil.rhoFun (L' w) ⇑(A' g)`. Introduce `w g g' hg`.

Establish `h1 : ⇑(CQi g') = schrInf D.host.F ps (P w) ⇑(CQi g)`. Use `congrArg (fun u => u ∘ ⇑Q.symm) (hQP w ⇑(CQi g))` as an intermediate fact. Simplify using `only [Function.comp_assoc, ContinuousLinearEquiv.self_comp_symm, Function.comp_id] at this`. Rewrite using `[this, hCQi, hg, ← hCQ, hQQ']`. Establish `h2` using `hI (P w) (CQi g) (CQi g') h1`.

Establish `hL' : P (L' w) = L (P w)` using `P.apply_symm_apply _`. Establish `h3 : ⇑(A (CQi g')) = schrInf D.host.F ps (P (L' w)) ⇑(A (CQi g))`. Rewrite using `[h2]`. Conclude with `congrArg (fun v => schrInf D.host.F ps v ⇑(A (CQi g))) hL'.symm`. Combine the equalities or inequalities in the displayed calculation.

Establish `hcont : Continuous A'` using `GlobalTheory.T.continuous_of_lie_intertwine_l2 (Fin n) L' A' C hC hbound (GlobalTheory.T.derived_action_intertwines_of_group (Fin n) L'.toLinearMap A' C hC hbound hint)`. Establish `hAeq : ⇑A = fun f => CQi (A' (CQ f))`. Use function extensionality and compare the values at `f`. Rewrite using `[hA'apply, hQQ, hQQ]`. Rewrite using `[hAeq]`.

Conclude with `CQi.continuous.comp (hcont.comp CQ.continuous)`.
-/
theorem realcont : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ]
    (L : ((κ → mixedEmbedding.mixedSpace D.host.F) × (κ → mixedEmbedding.mixedSpace D.host.F)) ≃ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace D.host.F) × (κ → mixedEmbedding.mixedSpace D.host.F)))
    (A : SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ →ₗ[ℂ] SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ) (C : ℝ≥0∞), C ≠ ⊤ →
      (∀ f, ∫⁻ z, ‖A f z‖ₑ ^ 2 ≤ C * ∫⁻ z, ‖f z‖ₑ ^ 2) →
      (∀ v (f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ), ⇑f' = GlobalTheory.WeilAdm.schrInf D.host.F ψ v ⇑f →
        ⇑(A f') = GlobalTheory.WeilAdm.schrInf D.host.F ψ (L v) ⇑(A f)) →
      Continuous A := by
  intro D ps hψ κ _ L A C hC hA hI
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨β, hβ1, hβ2⟩ := GlobalTheory.T.standardAddChar_archimedean_exp_realLinear D ps θ hψ hθ
  have hnd : ∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0 := by
    intro a ha
    have ha' : (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm a ≠ 0 := by
      simpa using ha
    obtain ⟨b, hb⟩ := GlobalTheory.T.realTrace_archimedeanEmbeddings_nondegenerate D θ hθ _ ha'
    refine ⟨InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F b, ?_⟩
    rw [hβ2, map_mul, RingEquiv.symm_apply_apply]
    simpa using hb
  obtain ⟨n, Q, P, hQP⟩ := GlobalTheory.T.exists_linear_model_archimedean_schroedinger_standard D.host.F ps β hβ1 hnd κ
  obtain ⟨c, hc⟩ := GlobalTheory.T.lintegral_sq_comp_continuousLinearEquiv_mixedSpace D.host.F κ n Q
  let CQ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) Q
  let CQi := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) Q.symm
  have hCQ : ∀ f, ⇑(CQ f) = ⇑f ∘ ⇑Q := fun f => SchwartzMap.compCLMOfContinuousLinearEquiv_apply ℂ Q f
  have hCQi : ∀ g, ⇑(CQi g) = ⇑g ∘ ⇑Q.symm := fun g => SchwartzMap.compCLMOfContinuousLinearEquiv_apply ℂ Q.symm g
  have hQQ : ∀ f, CQi (CQ f) = f := fun f => by
    ext z; rw [hCQi, hCQ]; simp
  have hQQ' : ∀ g, CQ (CQi g) = g := fun g => by
    ext z; rw [hCQ, hCQi]; simp
  let A' : GlobalTheory.RealWeil.Sch (Fin n) →ₗ[ℂ] GlobalTheory.RealWeil.Sch (Fin n) := CQ.toLinearMap ∘ₗ A ∘ₗ CQi.toLinearMap
  have hA'apply : ∀ g, A' g = CQ (A (CQi g)) := fun g => rfl
  let L' : (Fin n ⊕ Fin n → ℝ) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) := P.trans (L.trans P.symm)
  have hbound : ∀ g, ∫⁻ x, ‖A' g x‖ₑ ^ 2 ≤ C * ∫⁻ x, ‖g x‖ₑ ^ 2 := by
    intro g
    have e1 : ∫⁻ x, ‖A' g x‖ₑ ^ 2 = c * ∫⁻ z, ‖A (CQi g) z‖ₑ ^ 2 := by
      rw [← hc]
      simp only [hA'apply, hCQ, Function.comp_apply]
    have e2 : ∫⁻ x, ‖g x‖ₑ ^ 2 = c * ∫⁻ z, ‖CQi g z‖ₑ ^ 2 := by
      rw [← hc]
      simp only [hCQi, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
    rw [e1, e2, ← mul_assoc, mul_comm C c, mul_assoc]
    exact mul_le_mul' le_rfl (hA _)
  have hint : ∀ w (g g' : GlobalTheory.RealWeil.Sch (Fin n)), ⇑g' = GlobalTheory.RealWeil.rhoFun w ⇑g →
      ⇑(A' g') = GlobalTheory.RealWeil.rhoFun (L' w) ⇑(A' g) := by
    intro w g g' hg
    have h1 : ⇑(CQi g') = schrInf D.host.F ps (P w) ⇑(CQi g) := by
      have := congrArg (fun u => u ∘ ⇑Q.symm) (hQP w ⇑(CQi g))
      simp only [Function.comp_assoc, ContinuousLinearEquiv.self_comp_symm, Function.comp_id] at this
      rw [this, hCQi, hg, ← hCQ, hQQ']
    have h2 := hI (P w) (CQi g) (CQi g') h1
    have hL' : P (L' w) = L (P w) := P.apply_symm_apply _
    have h3 : ⇑(A (CQi g')) = schrInf D.host.F ps (P (L' w)) ⇑(A (CQi g)) := by
      rw [h2]
      exact congrArg (fun v => schrInf D.host.F ps v ⇑(A (CQi g))) hL'.symm
    calc ⇑(A' g') = ⇑(A (CQi g')) ∘ ⇑Q := hCQ _
      _ = schrInf D.host.F ps (P (L' w)) ⇑(A (CQi g)) ∘ ⇑Q := congrArg (· ∘ ⇑Q) h3
      _ = GlobalTheory.RealWeil.rhoFun (L' w) (⇑(A (CQi g)) ∘ ⇑Q) := hQP _ _
      _ = GlobalTheory.RealWeil.rhoFun (L' w) ⇑(A' g) := congrArg (GlobalTheory.RealWeil.rhoFun (L' w)) (hCQ _).symm
  have hcont : Continuous A' :=
    GlobalTheory.T.continuous_of_lie_intertwine_l2 (Fin n) L' A' C hC hbound (GlobalTheory.T.derived_action_intertwines_of_group (Fin n) L'.toLinearMap A' C hC hbound hint)
  have hAeq : ⇑A = fun f => CQi (A' (CQ f)) := by
    funext f
    rw [hA'apply, hQQ, hQQ]
  rw [hAeq]
  exact CQi.continuous.comp (hcont.comp CQ.continuous)

end GlobalTheory.WeilAdm
