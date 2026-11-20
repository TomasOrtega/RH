import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPairApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin

open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn

namespace GlobalTheory.SDUnique

/- English proof (translation)
Introduce `g _`. Use `⟨g (fun i => (x₀ i).2) • ((BoundedContinuousFunction.evalCLM ℂ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x₀ i).1)).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f => ?_⟩` and prove the remaining obligations. Simplify using `[pureA, mul_comm]`.
-/
theorem proj_mem_adm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (x₀ : κ → AF F) :
    (LinearMap.proj x₀ : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x₀ i).2) • ((BoundedContinuousFunction.evalCLM ℂ
    (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x₀ i).1)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f => ?_⟩
  simp [pureA, mul_comm]

/- English proof (translation)
Introduce `F _ _ κ _ T f f₁ f₂ h₁ h₂`. Establish `hg` using `GlobalTheory.SchANonzero.indicator_intPts_mem_SB F κ`. Use `SchwartzMap.ext fun x => ?_` and prove the remaining obligations. Set `x₀ : κ → AF F` to `fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), 0)`. Establish `h` using `(h₁ _ hg _ (proj_mem_adm x₀)).unique (h₂ _ hg _ (proj_mem_adm x₀))`.

Establish `h0 : (fun _ : κ => (0 : Af F)) ∈ GlobalTheory.SchANonzero.intPts F κ` using `fun i _ v => zero_mem (v.adicCompletionIntegers F)`. Establish `e : ∀ φ : SInf F κ, pureA F φ ((GlobalTheory.SchANonzero.intPts F κ).indicator 1) x₀ = φ x` using `fun φ => by`. Establish `hx : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x₀ i).1) = x`. Use function extensionality and compare the values at `fun i => RingEquiv.apply_symm_apply _ _`. Establish `h1 : (GlobalTheory.SchANonzero.intPts F κ).indicator (1 : (κ → Af F) → ℂ) (fun i => (x₀ i).2) = 1` using `Set.indicator_of_mem h0 _`.

Unfold `pureA`. Rewrite using `[hx]`. Conclude with `(congrArg (φ x * ·) h1).trans (mul_one _)`. Conclude with `(e f₁).symm.trans (h.trans (e f₂))`.
-/
theorem sd_unique : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ f₂ : SInf F κ}, SD T f f₁ → SD T f f₂ → f₁ = f₂ := by
  intro F _ _ κ _ T f f₁ f₂ h₁ h₂
  have hg := GlobalTheory.SchANonzero.indicator_intPts_mem_SB F κ
  refine SchwartzMap.ext fun x => ?_
  let x₀ : κ → AF F := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), 0)
  have h := (h₁ _ hg _ (proj_mem_adm x₀)).unique (h₂ _ hg _ (proj_mem_adm x₀))
  have h0 : (fun _ : κ => (0 : Af F)) ∈ GlobalTheory.SchANonzero.intPts F κ := fun i _ v =>
    zero_mem (v.adicCompletionIntegers F)
  have e : ∀ φ : SInf F κ, pureA F φ ((GlobalTheory.SchANonzero.intPts F κ).indicator 1) x₀ = φ x := fun φ => by
    have hx : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x₀ i).1) = x :=
      funext fun i => RingEquiv.apply_symm_apply _ _
    have h1 : (GlobalTheory.SchANonzero.intPts F κ).indicator (1 : (κ → Af F) → ℂ) (fun i => (x₀ i).2) = 1 :=
      Set.indicator_of_mem h0 _
    unfold pureA
    rw [hx]
    exact (congrArg (φ x * ·) h1).trans (mul_one _)
  exact (e f₁).symm.trans (h.trans (e f₂))

end GlobalTheory.SDUnique
