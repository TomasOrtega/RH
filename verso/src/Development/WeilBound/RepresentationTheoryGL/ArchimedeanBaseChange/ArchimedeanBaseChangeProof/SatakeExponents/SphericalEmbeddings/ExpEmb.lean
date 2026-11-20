import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.ExtremeSph
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.Rg.BcB.N3.Pee

/- English proof (translation)
Introduce `n V _ _ π ξ hπ ⟨ℓ, hℓ0, hℓ⟩`. Set `χ : (Fin n → kˣ) →* ℂˣ` to `torusChar fun i => unrChar k (ξ i)`. Set `ρ` to `(ofChar χ).comp (leviTorus k (Fin n)).symm.toMonoidHom`. Set `φ : (jac (points (Fin n)) π).IntertwiningMap ρ` to `⟨ℓ, fun g => LinearMap.ext fun v => by`. Establish `h` using `hℓ ((leviTorus k (Fin n)).symm g) v`.

Establish `e : jacB π ((leviTorus k (Fin n)).symm g) = jac (points (Fin n)) π g` using `by show (jac (points (Fin n)) π) ((leviTorus k (Fin n)) ((leviTorus k (Fin n)).symm g)) = _`. Rewrite using `[MulEquiv.apply_symm_apply]`. Rewrite `h` using `[e]`. Use `h.trans ?_` and prove the remaining obligations. Conclude with `(ofChar_apply χ ((leviTorus k (Fin n)).symm g) (ℓ v)).symm⟩`.

Take `⟨f, hf⟩` from `(GlobalTheory.SmGL.Model.evalOne_bijective (points (Fin n)) hπ ρ).2 φ`. Use `⟨f, fun h0 => hℓ0 ?_⟩` and prove the remaining obligations. Establish `: φ = GlobalTheory.SmGL.Model.evalOne (points (Fin n)) (0 : π.IntertwiningMap (iP (k` using `k) ξ)) := by`. Rewrite using `[← hf, h0]`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations.

Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Establish `h1` using `congrArg (fun F => F (Submodule.Quotient.mk v)) this`. Conclude with `h1`.
-/
theorem expEmb (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PositivityTheory.Rg.BcB.N3.ExpEmb k := by
  intro n V _ _ π ξ hπ ⟨ℓ, hℓ0, hℓ⟩
  let χ : (Fin n → kˣ) →* ℂˣ := torusChar fun i => unrChar k (ξ i)
  let ρ := (ofChar χ).comp (leviTorus k (Fin n)).symm.toMonoidHom
  let φ : (jac (points (Fin n)) π).IntertwiningMap ρ :=
    ⟨ℓ, fun g => LinearMap.ext fun v => by
      have h := hℓ ((leviTorus k (Fin n)).symm g) v
      have e : jacB π ((leviTorus k (Fin n)).symm g) = jac (points (Fin n)) π g := by
        show (jac (points (Fin n)) π) ((leviTorus k (Fin n)) ((leviTorus k (Fin n)).symm g)) = _
        rw [MulEquiv.apply_symm_apply]
      rw [e] at h
      refine h.trans ?_
      exact (ofChar_apply χ ((leviTorus k (Fin n)).symm g) (ℓ v)).symm⟩
  obtain ⟨f, hf⟩ := (GlobalTheory.SmGL.Model.evalOne_bijective (points (Fin n)) hπ ρ).2 φ
  refine ⟨f, fun h0 => hℓ0 ?_⟩
  have : φ = GlobalTheory.SmGL.Model.evalOne (points (Fin n)) (0 : π.IntertwiningMap (iP (k := k) ξ)) := by
    rw [← hf, h0]
  refine LinearMap.ext fun x => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h1 := congrArg (fun F => F (Submodule.Quotient.mk v)) this
  exact h1

end PositivityTheory.Rg.BcB.N3.Pee
