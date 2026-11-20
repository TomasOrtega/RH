import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocSplitGraph

/- English proof (translation)
Introduce `L _ _ _ n a S₁ S₂ s σ₁ σ₂ h₁ h₂ hE`. Take `⟨E⟩` from `hE`. Take `⟨i₁, T₁, hi₁, hiL₁, hT₁inj, hT₁S, hT₁eq⟩` from `h₁`. Take `⟨i₂, T₂, hi₂, hiL₂, hT₂inj, hT₂S, hT₂eq⟩` from `h₂`. Establish `hci : i₁ = i₂`.

Establish `hd` using `IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (K := maximalRealSubfield L) s.v`. Establish `hfun : (i₁ : s.v.adicCompletion (maximalRealSubfield L) → s.w.adicCompletion L) = i₂`. Use `hd.equalizer hi₁ hi₂ (funext fun y => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Rewrite using `[← s.i.commutes y, hiL₁, hiL₂]`.

Conclude with `RingEquiv.ext (congrFun hfun)`. Substitute `hci` using the available equality. Set `F : σ₁.V →ₗ[ℂ] (GAf L n → a.W) × (GAf L n → a.W)` to `T₁.prod (T₂ ∘ₗ E.toLinearEquiv.toLinearMap)`. Establish `hF : ∀ u, F u = (T₁ u, T₂ (E u))` using `fun u => rfl`. Establish `hEint : ∀ g u, E (σ₁.ρ g u) = σ₂.ρ g (E u)` using `fun g u => LinearMap.congr_fun (E.isIntertwining' g) u`.

Establish `hnt : Nontrivial σ₁.V` using `by haveI := σ₁.irr`. Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[not_nontrivial_iff_subsingleton]`. Apply `(bot_ne_top : (⊥ : Subrepresentation σ₁.ρ) ≠ ⊤)` to reduce the goal to its premises. Establish `: ∀ W : Subrepresentation σ₁.ρ, W = ⊥`.

Introduce `W`. Use extensionality with `x`. Simplify using `[Subsingleton.elim x 0]`. Rewrite using `[this ⊤]`. Use `⟨LinearMap.range F, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Take `⟨u, hu⟩` from `exists_ne (0 : σ₁.V)`. Introduce `h`. Establish `hm : F u ∈ LinearMap.range F` using `⟨u, rfl⟩`. Rewrite `hm` using `[h, Submodule.mem_bot, hF, Prod.mk_eq_zero]`. Conclude with `hu (hT₁inj (hm.1.trans (map_zero T₁).symm))`.

Introduce and unpack `_ ⟨u, rfl⟩`. Conclude with `⟨hT₁S u, hT₂S (E u)⟩`. Introduce and unpack `x hx _ ⟨u, rfl⟩`. Use `⟨σ₁.ρ (Matrix.GeneralLinearGroup.map i₁.toRingHom (s.loc n x)) u, ?_⟩` and prove the remaining obligations. Rewrite using `[hF, hF, hT₁eq x hx u, hEint, hT₂eq x hx (E u)]`.

Introduce and unpack `u ⟨v, hv⟩`. Rewrite `hv` using `[hF, Prod.mk.injEq]`. Establish `hv0 : v = 0` using `hT₁inj (hv.1.trans (map_zero T₁).symm)`. Rewrite using `[← hv.2, hv0, map_zero, map_zero]`. Introduce and unpack `u ⟨v, hv⟩`.

Rewrite `hv` using `[hF, Prod.mk.injEq]`. Establish `hv0 : E v = 0` using `hT₂inj (hv.2.trans (map_zero T₂).symm)`. Establish `: v = 0` using `by simpa using hv0`. Rewrite using `[← hv.1, this, map_zero]`.
-/
theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S₁ S₂ : Submodule ℂ (GAf L n → a.W)) (s : SplitPlace L) (σ₁ σ₂ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S₁ s σ₁ → IsLocS S₂ s σ₂ → Nonempty (σ₁.ρ.Equiv σ₂.ρ) → ∃ X : Submodule ℂ ((GAf L n → a.W) × (GAf L n → a.W)), X ≠ ⊥ ∧ (∀ z ∈ X, z.1 ∈ S₁ ∧ z.2 ∈ S₂) ∧ (∀ x : GAf L n, TrivOutside {s.v} x → ∀ z ∈ X, (NG.rt L n x z.1, NG.rt L n x z.2) ∈ X) ∧ (∀ u, ((0 : GAf L n → a.W), u) ∈ X → u = 0) ∧ (∀ u, (u, (0 : GAf L n → a.W)) ∈ X → u = 0) := by
  intro L _ _ _ n a S₁ S₂ s σ₁ σ₂ h₁ h₂ hE
  obtain ⟨E⟩ := hE
  obtain ⟨i₁, T₁, hi₁, hiL₁, hT₁inj, hT₁S, hT₁eq⟩ := h₁
  obtain ⟨i₂, T₂, hi₂, hiL₂, hT₂inj, hT₂S, hT₂eq⟩ := h₂

  have hci : i₁ = i₂ := by
    have hd := IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (K := maximalRealSubfield L) s.v
    have hfun : (i₁ : s.v.adicCompletion (maximalRealSubfield L) → s.w.adicCompletion L) = i₂ := by
      refine hd.equalizer hi₁ hi₂ (funext fun y => ?_)
      simp only [Function.comp_apply]
      rw [← s.i.commutes y, hiL₁, hiL₂]
    exact RingEquiv.ext (congrFun hfun)
  subst hci
  let F : σ₁.V →ₗ[ℂ] (GAf L n → a.W) × (GAf L n → a.W) := T₁.prod (T₂ ∘ₗ E.toLinearEquiv.toLinearMap)
  have hF : ∀ u, F u = (T₁ u, T₂ (E u)) := fun u => rfl
  have hEint : ∀ g u, E (σ₁.ρ g u) = σ₂.ρ g (E u) := fun g u => LinearMap.congr_fun (E.isIntertwining' g) u
  have hnt : Nontrivial σ₁.V := by
    haveI := σ₁.irr
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    apply (bot_ne_top : (⊥ : Subrepresentation σ₁.ρ) ≠ ⊤)
    have : ∀ W : Subrepresentation σ₁.ρ, W = ⊥ := by
      intro W
      ext x
      simp [Subsingleton.elim x 0]
    rw [this ⊤]
  refine ⟨LinearMap.range F, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨u, hu⟩ := exists_ne (0 : σ₁.V)
    intro h
    have hm : F u ∈ LinearMap.range F := ⟨u, rfl⟩
    rw [h, Submodule.mem_bot, hF, Prod.mk_eq_zero] at hm
    exact hu (hT₁inj (hm.1.trans (map_zero T₁).symm))
  · rintro _ ⟨u, rfl⟩
    exact ⟨hT₁S u, hT₂S (E u)⟩
  · rintro x hx _ ⟨u, rfl⟩
    refine ⟨σ₁.ρ (Matrix.GeneralLinearGroup.map i₁.toRingHom (s.loc n x)) u, ?_⟩
    rw [hF, hF, hT₁eq x hx u, hEint, hT₂eq x hx (E u)]
  · rintro u ⟨v, hv⟩
    rw [hF, Prod.mk.injEq] at hv
    have hv0 : v = 0 := hT₁inj (hv.1.trans (map_zero T₁).symm)
    rw [← hv.2, hv0, map_zero, map_zero]
  · rintro u ⟨v, hv⟩
    rw [hF, Prod.mk.injEq] at hv
    have hv0 : E v = 0 := hT₂inj (hv.2.trans (map_zero T₂).symm)
    have : v = 0 := by simpa using hv0
    rw [← hv.1, this, map_zero]

end GlobalTheory.LocSplitGraph
