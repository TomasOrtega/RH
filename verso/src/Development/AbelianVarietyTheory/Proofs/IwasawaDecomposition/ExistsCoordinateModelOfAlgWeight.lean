import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfOfNodupAlg

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutQuot.Model

/- English proof (translation)
Set `E : Subrepresentation ρ ≃o Subrepresentation σ` to `{ toFun := fun S => ⟨S.toSubmodule.comap κ.symm.toLinearMap, fun g w hw => by`. Take `⟨v, rfl⟩` from `κ.surjective w`. Establish `hv : v ∈ S.toSubmodule` using `κ.symm_apply_apply v ▸ hw`. Simplify `S.apply_mem_toSubmodule g hv⟩` using `[← h]`. Use `invFun := fun T => ⟨T.toSubmodule.comap κ.toLinearMap, fun g v hv => by show κ (ρ g v) ∈ T.toSubmodule`.

Rewrite using `[h]`. Conclude with `T.apply_mem_toSubmodule _ hv⟩`. Use `left_inv := fun S => Subrepresentation.toSubmodule_injective (by ext v; simp)`. Use `right_inv := fun T => Subrepresentation.toSubmodule_injective (by ext v; simp)`. Use the proof step `map_rel_iff' := fun {S T} => ⟨fun hh v hv => by`.

Establish `: κ.symm (κ v) ∈ S.toSubmodule` using `(κ.symm_apply_apply v).symm ▸ hv`. Establish `h2 : κ.symm (κ v) ∈ T.toSubmodule` using `hh this`. Conclude with `κ.symm_apply_apply v ▸ h2, fun hh v hv => hh hv⟩ }`. Conclude with `E.isSimpleOrder_iff.1 hρ`.
-/
theorem isIrreducible_of_linearEquiv {F G V W : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] {ρ : Representation F G V} {σ : Representation F G W} (κ : V ≃ₗ[F] W)
    (h : ∀ g v, κ (ρ g v) = σ g (κ v)) (hρ : ρ.IsIrreducible) : σ.IsIrreducible := by
  let E : Subrepresentation ρ ≃o Subrepresentation σ :=
    { toFun := fun S => ⟨S.toSubmodule.comap κ.symm.toLinearMap, fun g w hw => by
        obtain ⟨v, rfl⟩ := κ.surjective w
        have hv : v ∈ S.toSubmodule := κ.symm_apply_apply v ▸ hw
        simpa [← h] using S.apply_mem_toSubmodule g hv⟩
      invFun := fun T => ⟨T.toSubmodule.comap κ.toLinearMap, fun g v hv => by
        show κ (ρ g v) ∈ T.toSubmodule
        rw [h]
        exact T.apply_mem_toSubmodule _ hv⟩
      left_inv := fun S => Subrepresentation.toSubmodule_injective (by ext v; simp)
      right_inv := fun T => Subrepresentation.toSubmodule_injective (by ext v; simp)
      map_rel_iff' := fun {S T} => ⟨fun hh v hv => by
        have : κ.symm (κ v) ∈ S.toSubmodule := (κ.symm_apply_apply v).symm ▸ hv
        have h2 : κ.symm (κ v) ∈ T.toSubmodule := hh this
        exact κ.symm_apply_apply v ▸ h2, fun hh v hv => hh hv⟩ }
  exact E.isSimpleOrder_iff.1 hρ

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def conjRep {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (e : W ≃ₗ[ℂ] W')
    (ρ : Representation ℂ (GQ L n) W) : Representation ℂ (GQ L n) W' where
  toFun γ := e.toLinearMap ∘ₗ ρ γ ∘ₗ e.symm.toLinearMap
  map_one' := by ext x; simp
  map_mul' γ δ := by ext x; simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conjRep_apply {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (e : W ≃ₗ[ℂ] W')
    (ρ : Representation ℂ (GQ L n) W) (γ : GQ L n) (x : W') : conjRep e ρ γ x = e (ρ γ (e.symm x)) := rfl

/- English proof (translation)
Take `⟨hfd, ι, i1, i2, b, P, hP⟩` from `h`. Use `⟨LinearEquiv.finiteDimensional e, ι, i1, i2, b.map e, P, fun γ γ₀ hγ => ?_⟩` and prove the remaining obligations. Rewrite using `[← hP γ γ₀ hγ]`. Use extensionality with `i j`. Simplify using `[LinearMap.toMatrix_apply, conjRep_apply]`.
-/
theorem isAlgWeight_conjRep {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (e : W ≃ₗ[ℂ] W')
    (ρ : Representation ℂ (GQ L n) W) (h : IsAlgWeight L n ρ) : IsAlgWeight L n (conjRep e ρ) := by
  obtain ⟨hfd, ι, i1, i2, b, P, hP⟩ := h
  refine ⟨LinearEquiv.finiteDimensional e, ι, i1, i2, b.map e, P, fun γ γ₀ hγ => ?_⟩
  rw [← hP γ γ₀ hγ]
  ext i j
  simp [LinearMap.toMatrix_apply, conjRep_apply]

/- English proof (translation)
Introduce `L _ _ _ n a`. Use `haveI : FiniteDimensional ℂ a.W := a.alg.1`. Set `e : a.W ≃ₗ[ℂ] (Fin (Module.finrank ℂ a.W) → ℂ)` to `(Module.finBasis ℂ a.W).equivFun`. Use `⟨⟨Module.finrank ℂ a.W, conjRep e a.ρ, isAlgWeight_conjRep e a.ρ a.alg, isIrreducible_of_linearEquiv e (fun γ x => by simp [conjRep_apply]) a.irr⟩, e, fun γ x => ?_⟩` and prove the remaining obligations. Use `show e (a.ρ γ x) = conjRep e a.ρ γ (e x)`.

Simplify using `[conjRep_apply]`.
-/
theorem exists_model : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n),
    ∃ m : GlobalTheory.AutQuot.AlgWtM L n, a.Iso m.toAlgWt := by
  intro L _ _ _ n a
  haveI : FiniteDimensional ℂ a.W := a.alg.1
  let e : a.W ≃ₗ[ℂ] (Fin (Module.finrank ℂ a.W) → ℂ) := (Module.finBasis ℂ a.W).equivFun
  refine ⟨⟨Module.finrank ℂ a.W, conjRep e a.ρ, isAlgWeight_conjRep e a.ρ a.alg,
    isIrreducible_of_linearEquiv e (fun γ x => by simp [conjRep_apply]) a.irr⟩, e, fun γ x => ?_⟩
  show e (a.ρ γ x) = conjRep e a.ρ γ (e x)
  simp [conjRep_apply]

end GlobalTheory.AutQuot.Model

end
