import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StInjectiveHolomorphicJacobianNeZero
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicDerivNeZero
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolomorphicKernelFibre
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCriticalFlatNotInjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology

namespace InjectiveHolomorphicJacobianNeZero

/- English proof (translation)
Rewrite using `[← LinearMap.det_toMatrix (Pi.basisFun ℂ (Fin 1)), Matrix.det_unique, LinearMap.toMatrix_apply]`. Simplify using `only [Pi.basisFun_apply, Pi.basisFun_repr]`. Establish `h1 : (Pi.single (default : Fin 1) (1 : ℂ) : Fin 1 → ℂ) = 1`. Use function extensionality and compare the values at `i`. Use `fin_cases i`.

Both sides reduce to the same expression. Rewrite using `[h1]`. Both sides reduce to the same expression.
-/
theorem det_fin_one (A : (Fin 1 → ℂ) →ₗ[ℂ] Fin 1 → ℂ) : LinearMap.det A = A 1 0 := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (Fin 1)), Matrix.det_unique, LinearMap.toMatrix_apply]
  simp only [Pi.basisFun_apply, Pi.basisFun_repr]
  have h1 : (Pi.single (default : Fin 1) (1 : ℂ) : Fin 1 → ℂ) = 1 := by
    funext i
    fin_cases i
    rfl
  rw [h1]
  rfl

/- English proof (translation)
Use `set e : (Fin 1 → ℂ) ≃L[ℂ] ℂ := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ with he`. Use `set φ : ℂ → ℂ := fun z => e (f (e.symm z)) with hφ`. Establish `hD : IsOpen (e.symm ⁻¹' U)` using `hU.preimage e.symm.continuous`. Establish `hφd : DifferentiableOn ℂ φ (e.symm ⁻¹' U)` using `e.differentiable.comp_differentiableOn (hf.comp e.symm.differentiable.differentiableOn fun _ h => h)`. Establish `hφi : Set.InjOn φ (e.symm ⁻¹' U)` using `fun s hs t ht h => e.symm.injective (hinj hs ht (e.injective h))`.

Establish `hxD : e x ∈ e.symm ⁻¹' U` using `by simpa using hx`. Establish `hne` using `InjectiveHolomorphicDerivNeZero.proof _ φ hD hφd hφi (e x) hxD`. Establish `hfx : HasFDerivAt f (fderiv ℂ f x) x` using `(hf.differentiableAt (hU.mem_nhds hx)).hasFDerivAt`. Establish `hφx : HasFDerivAt φ ((e : (Fin 1 → ℂ) →L[ℂ] ℂ).comp ((fderiv ℂ f x).comp (e.symm : ℂ →L[ℂ] Fin 1 → ℂ))) (e x)`. Establish `h1 : HasFDerivAt f (fderiv ℂ f x) (e.symm (e x))` using `by simpa using hfx`.

Conclude with `e.hasFDerivAt.comp (e x) (h1.comp (e x) e.symm.hasFDerivAt)`. Rewrite `hne` using `[hφx.hasDerivAt.deriv]`. Rewrite using `[det_fin_one]`. Simplify `hne` using `[he]`.
-/
theorem one {U : Set (Fin 1 → ℂ)} {f : (Fin 1 → ℂ) → Fin 1 → ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hinj : Set.InjOn f U) {x : Fin 1 → ℂ} (hx : x ∈ U) :
    LinearMap.det (fderiv ℂ f x : (Fin 1 → ℂ) →ₗ[ℂ] Fin 1 → ℂ) ≠ 0 := by
  set e : (Fin 1 → ℂ) ≃L[ℂ] ℂ := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ with he
  set φ : ℂ → ℂ := fun z => e (f (e.symm z)) with hφ
  have hD : IsOpen (e.symm ⁻¹' U) := hU.preimage e.symm.continuous
  have hφd : DifferentiableOn ℂ φ (e.symm ⁻¹' U) :=
    e.differentiable.comp_differentiableOn (hf.comp e.symm.differentiable.differentiableOn fun _ h => h)
  have hφi : Set.InjOn φ (e.symm ⁻¹' U) := fun s hs t ht h =>
    e.symm.injective (hinj hs ht (e.injective h))
  have hxD : e x ∈ e.symm ⁻¹' U := by simpa using hx
  have hne := InjectiveHolomorphicDerivNeZero.proof _ φ hD hφd hφi (e x) hxD
  have hfx : HasFDerivAt f (fderiv ℂ f x) x := (hf.differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hφx : HasFDerivAt φ ((e : (Fin 1 → ℂ) →L[ℂ] ℂ).comp ((fderiv ℂ f x).comp
      (e.symm : ℂ →L[ℂ] Fin 1 → ℂ))) (e x) := by
    have h1 : HasFDerivAt f (fderiv ℂ f x) (e.symm (e x)) := by simpa using hfx
    exact e.hasFDerivAt.comp (e x) (h1.comp (e x) e.symm.hasFDerivAt)
  rw [hφx.hasDerivAt.deriv] at hne
  rw [det_fin_one]
  simpa [he] using hne

end InjectiveHolomorphicJacobianNeZero

/- English proof (translation)
Introduce `k`. Proceed by induction on `k using Nat.strong_induction_on with`. Consider the case `_ k ih`. Introduce `U f hU hf hinj x hx hdet`. Break down `Nat.lt_or_ge k 2 with hk | hk` into its components or cases.

Use `interval_cases k`. Rewrite `hdet` using `[LinearMap.det_eq_one_of_subsingleton]`. Conclude with `one_ne_zero hdet`. Conclude with `InjectiveHolomorphicJacobianNeZero.one hU hf hinj hx hdet`. Distinguish the cases in `hall : ∀ b ∈ U, LinearMap.det (fderiv ℂ f b : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) = 0 → fderiv ℂ f b = 0`.

Conclude with `hC k U f x hk hU hf hx hdet hall hinj`. Use `push Not at hall`. Take `⟨b, hb, hdb, hne⟩` from `hall`. Use `set d := Module.finrank ℂ (LinearMap.ker (fderiv ℂ f b : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)) with hd`. Establish `hd0 : 0 < d`.

Rewrite using `[hd, Module.finrank_pos_iff_exists_ne_zero]`. Take `⟨v, hv, hv0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.bot_lt_ker_of_det_eq_zero hdb).ne'`. Conclude with `⟨⟨v, hv⟩, by simpa using hv0⟩`. Establish `hdk : d < k`. Establish `hker : LinearMap.ker (fderiv ℂ f b : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) ≠ ⊤`.

Rewrite using `[Ne, LinearMap.ker_eq_top]`. Introduce `h0`. Conclude with `hne (ContinuousLinearMap.coe_injective (by simpa using h0))`. Simplify `Submodule.finrank_lt hker` using `[Module.finrank_fin_fun]`. Take `⟨V, y, γ, ℓ, hV, hy, hγ, hmaps, hγinj, hfib, hzero⟩` from `hF k U f b hU hf hb d rfl`.

Establish `hhd : DifferentiableOn ℂ (fun t => ℓ (f (γ t))) V` using `ℓ.differentiable.comp_differentiableOn (hf.comp hγ hmaps)`. Establish `hhinj : Set.InjOn (fun t => ℓ (f (γ t))) V` using `fun s hs t ht h => hγinj hs ht (hinj (hmaps hs) (hmaps ht) (hfib s hs t ht h))`. Apply `ih d hdk V _ hV hhd hhinj y hy` to reduce the goal to its premises. Rewrite using `[hzero, ContinuousLinearMap.toLinearMap_zero, LinearMap.det_zero, Module.finrank_fin_fun]`. Conclude with `zero_pow hd0.ne'`.
-/
theorem InjectiveHolomorphicJacobianNeZero.proof (hF : HolomorphicKernelFibre.Statement)
    (hC : CriticalFlatNotInjective.Statement) : InjectiveHolomorphicJacobianNeZero.Statement := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro U f hU hf hinj x hx hdet
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · rw [LinearMap.det_eq_one_of_subsingleton] at hdet
      exact one_ne_zero hdet
    · exact InjectiveHolomorphicJacobianNeZero.one hU hf hinj hx hdet
  · by_cases hall : ∀ b ∈ U, LinearMap.det (fderiv ℂ f b : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) = 0 →
        fderiv ℂ f b = 0
    · exact hC k U f x hk hU hf hx hdet hall hinj
    push Not at hall
    obtain ⟨b, hb, hdb, hne⟩ := hall
    set d := Module.finrank ℂ (LinearMap.ker (fderiv ℂ f b : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)) with hd
    have hd0 : 0 < d := by
      rw [hd, Module.finrank_pos_iff_exists_ne_zero]
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
        (LinearMap.bot_lt_ker_of_det_eq_zero hdb).ne'
      exact ⟨⟨v, hv⟩, by simpa using hv0⟩
    have hdk : d < k := by
      have hker : LinearMap.ker (fderiv ℂ f b : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) ≠ ⊤ := by
        rw [Ne, LinearMap.ker_eq_top]
        intro h0
        exact hne (ContinuousLinearMap.coe_injective (by simpa using h0))
      simpa [Module.finrank_fin_fun] using Submodule.finrank_lt hker
    obtain ⟨V, y, γ, ℓ, hV, hy, hγ, hmaps, hγinj, hfib, hzero⟩ := hF k U f b hU hf hb d rfl
    have hhd : DifferentiableOn ℂ (fun t => ℓ (f (γ t))) V :=
      ℓ.differentiable.comp_differentiableOn (hf.comp hγ hmaps)
    have hhinj : Set.InjOn (fun t => ℓ (f (γ t))) V := fun s hs t ht h =>
      hγinj hs ht (hinj (hmaps hs) (hmaps ht) (hfib s hs t ht h))
    apply ih d hdk V _ hV hhd hhinj y hy
    rw [hzero, ContinuousLinearMap.toLinearMap_zero, LinearMap.det_zero, Module.finrank_fin_fun]
    exact zero_pow hd0.ne'

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
