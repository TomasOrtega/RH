import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TensorProductVectors

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
open scoped TensorProduct

namespace UpperTheory.TNZ

/- English proof (translation)
Introduce `k _ _ _ _ n G V _ _ π hπ`. Take `⟨X, instA, instM, σ, -, -, hdet, ⟨e⟩⟩` from `hπ`. Set `_` to `instA`. Set `_` to `instM`. Take `⟨v, hv0, hv⟩` from `e1 k G.s G.d X σ G.μ hdet`.

Use `choose F hF using fun φ : ↥G.V0sp => e5 e2 e3 k n G X σ v hv φ.1 φ.2`. Establish `hadd : ∀ φ ψ, F (φ + ψ) = F φ + F ψ` using `fun φ ψ => e4 k G.s n G.d G.hd _ (piTensor σ) _ _ fun κ hκ => by`. Establish `h1` using `hF (φ + ψ) ⟨κ, hκ⟩`. Establish `h2` using `hF φ ⟨κ, hκ⟩`. Establish `h3` using `hF ψ ⟨κ, hκ⟩`.

Express the relevant statement in the definitionally equal form `_ = (F φ).1.1 κ + (F ψ).1.1 κ`. Rewrite using `[h1, h2, h3, ← add_smul]`. Both sides reduce to the same expression. Establish `hsmul : ∀ (c : ℂ) φ, F (c • φ) = c • F φ` using `fun c φ => e4 k G.s n G.d G.hd _ (piTensor σ) _ _ fun κ hκ => by`. Establish `h1` using `hF (c • φ) ⟨κ, hκ⟩`.

Establish `h2` using `hF φ ⟨κ, hκ⟩`. Express the relevant statement in the definitionally equal form `_ = c • (F φ).1.1 κ`. Rewrite using `[h1, h2, smul_smul]`. Both sides reduce to the same expression. Set `f0 : ↥G.V0sp →ₗ[ℂ] IndSp G.e (piTensor σ)` to `{ toFun := F, map_add' := hadd, map_smul' := hsmul }`.

Use `⟨e.symm.toLinearEquiv.toLinearMap ∘ₗ f0, fun φ ψ h => ?_, fun κ φ φ' hφ' => ?_⟩` and prove the remaining obligations. Establish `h' : F φ = F ψ` using `e.symm.toLinearEquiv.injective h`. Use `Subtype.ext (funext fun κ => ?_)` and prove the remaining obligations. Establish `h2` using `congrArg (fun F : IndSp G.e (piTensor σ) => F.1.1 (κ : GL (Fin n) k)) h'`. Simplify using `only [hF] at h2`.

Conclude with `smul_left_injective ℂ hv0 h2`. Establish `key : F φ' = parInd G.e (piTensor σ) (κ : GL (Fin n) k) (F φ)` using `e4 k G.s n G.d G.hd _ (piTensor σ) _ _ fun x hx => by`. Rewrite using `[hF φ' ⟨x, hx⟩, parInd_apply, hF φ ⟨x * κ, mul_mem hx κ.2⟩, hφ']`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `e.symm.toLinearEquiv (F φ') = π κ (e.symm.toLinearEquiv (F φ))`.

Rewrite using `[key, Representation.Equiv.toLinearEquiv_apply, Representation.Equiv.toLinearEquiv_apply]`. Conclude with `Representation.IntertwiningMap.isIntertwining _ _ e.symm.toIntertwiningMap (κ : GL (Fin n) k) (F φ)`.
-/
theorem gEmb (e1 : TensorProductVectors) (e2 : LeviSubgroupRestriction) (e3 : ParabolicInductionKernel) (e4 : InducedDeterminantTwist)
    (e5 : InductionExtension) : GEmb := by
  intro k _ _ _ _ n G V _ _ π hπ
  obtain ⟨X, instA, instM, σ, -, -, hdet, ⟨e⟩⟩ := hπ
  let _ := instA
  let _ := instM
  obtain ⟨v, hv0, hv⟩ := e1 k G.s G.d X σ G.μ hdet
  choose F hF using fun φ : ↥G.V0sp => e5 e2 e3 k n G X σ v hv φ.1 φ.2
  have hadd : ∀ φ ψ, F (φ + ψ) = F φ + F ψ := fun φ ψ =>
    e4 k G.s n G.d G.hd _ (piTensor σ) _ _ fun κ hκ => by
      have h1 := hF (φ + ψ) ⟨κ, hκ⟩
      have h2 := hF φ ⟨κ, hκ⟩
      have h3 := hF ψ ⟨κ, hκ⟩
      change _ = (F φ).1.1 κ + (F ψ).1.1 κ
      rw [h1, h2, h3, ← add_smul]
      rfl
  have hsmul : ∀ (c : ℂ) φ, F (c • φ) = c • F φ := fun c φ =>
    e4 k G.s n G.d G.hd _ (piTensor σ) _ _ fun κ hκ => by
      have h1 := hF (c • φ) ⟨κ, hκ⟩
      have h2 := hF φ ⟨κ, hκ⟩
      change _ = c • (F φ).1.1 κ
      rw [h1, h2, smul_smul]
      rfl
  let f0 : ↥G.V0sp →ₗ[ℂ] IndSp G.e (piTensor σ) :=
    { toFun := F, map_add' := hadd, map_smul' := hsmul }
  refine ⟨e.symm.toLinearEquiv.toLinearMap ∘ₗ f0, fun φ ψ h => ?_, fun κ φ φ' hφ' => ?_⟩
  · have h' : F φ = F ψ := e.symm.toLinearEquiv.injective h
    refine Subtype.ext (funext fun κ => ?_)
    have h2 := congrArg (fun F : IndSp G.e (piTensor σ) => F.1.1 (κ : GL (Fin n) k)) h'
    simp only [hF] at h2
    exact smul_left_injective ℂ hv0 h2
  · have key : F φ' = parInd G.e (piTensor σ) (κ : GL (Fin n) k) (F φ) :=
      e4 k G.s n G.d G.hd _ (piTensor σ) _ _ fun x hx => by
        rw [hF φ' ⟨x, hx⟩, parInd_apply, hF φ ⟨x * κ, mul_mem hx κ.2⟩, hφ']
        rfl
    change e.symm.toLinearEquiv (F φ') = π κ (e.symm.toLinearEquiv (F φ))
    rw [key, Representation.Equiv.toLinearEquiv_apply, Representation.Equiv.toLinearEquiv_apply]
    exact Representation.IntertwiningMap.isIntertwining _ _ e.symm.toIntertwiningMap (κ : GL (Fin n) k) (F φ)

end UpperTheory.TNZ
