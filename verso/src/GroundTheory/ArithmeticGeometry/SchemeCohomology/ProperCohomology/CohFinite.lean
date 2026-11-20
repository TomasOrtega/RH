import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ExistsGeneratingSectionsTwist
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits Abelian

universe w' u

noncomputable section

variable {X : Scheme.{u}} [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
  (A : Type*) [CommRing A] [Algebra A Γ(X, ⊤)]

def FiniteH (F : X.Modules) : Prop :=
  ∀ p : ℕ, Module.Finite A (Sheaf.H.{w'} (modulesAb F) p)

variable {A}

/- English proof (translation)
Introduce `p` and use `have := hF p Module.Finite.equiv (H.linearEquivOfIso.{w'} A e p)`.
-/
theorem FiniteH.of_iso {F G : X.Modules} (e : F ≅ G) (hF : FiniteH.{w'} A F) :
    FiniteH.{w'} A G := fun p =>
  have := hF p
  Module.Finite.equiv (H.linearEquivOfIso.{w'} A e p)

/- English proof (translation)
Introduce `x y hxy`. Take `⟨x, rfl⟩` from `(Ext.mk₀_bijective _ _).2 x`. Take `⟨y, rfl⟩` from `(Ext.mk₀_bijective _ _).2 y`. Rewrite `hxy` using `[Sheaf.H.map_apply, Sheaf.H.map_apply, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀]`. Rewrite using `[(cancel_mono f).1 ((Ext.mk₀_bijective _ _).1 hxy)]`.
-/
lemma H.map_zero_injective {C : Type*} [Category C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{u})]
    {F G : Sheaf J AddCommGrpCat.{u}} (f : F ⟶ G) [Mono f] :
    Function.Injective (Sheaf.H.map.{w'} f 0) := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := (Ext.mk₀_bijective _ _).2 x
  obtain ⟨y, rfl⟩ := (Ext.mk₀_bijective _ _).2 y
  rw [Sheaf.H.map_apply, Sheaf.H.map_apply, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀] at hxy
  rw [(cancel_mono f).1 ((Ext.mk₀_bijective _ _).1 hxy)]

variable [IsNoetherianRing A]

/- English proof (translation)
Introduce `p` and use `have := h₁ p have := h₃ p finite_of_exact_noetherian (H.linearMap A S.f p) (H.linearMap A S.g p) fun y hy => H.exact₂ (shortExact_abSC hS) y hy`.
-/
theorem FiniteH.of_shortExact₂ {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : FiniteH.{w'} A S.X₁) (h₃ : FiniteH.{w'} A S.X₃) : FiniteH.{w'} A S.X₂ := fun p =>
  have := h₁ p
  have := h₃ p
  finite_of_exact_noetherian (H.linearMap A S.f p) (H.linearMap A S.g p)
    fun y hy => H.exact₂ (shortExact_abSC hS) y hy

/- English proof (translation)
Introduce `p`. Use `h₂ p` as an intermediate fact. Establish `hS'` using `shortExact_abSC hS`. Consider the cases of `p with`. Consider the case `zero`.

Establish `: Mono (abSC S).f` using `hS'.mono_f`. Use `finite_of_exact_noetherian (0 : (Fin 0 → A) →ₗ[A] _) (H.linearMap A S.f 0) ?_` and prove the remaining obligations. Introduce `y hy`. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.zero_apply]`.

Conclude with `(H.map_zero_injective.{w'} (abSC S).f (hy.trans (map_zero _).symm)).symm`. Consider the case `succ p`. Use `h₃ p` as an intermediate fact. Conclude with `finite_of_exact_noetherian (H.δLinear A hS' p) (H.linearMap A S.f (p + 1)) fun x hx => H.exact₁ hS' rfl x hx`.
-/
theorem FiniteH.of_shortExact₁ {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₂ : FiniteH.{w'} A S.X₂) (h₃ : FiniteH.{w'} A S.X₃) : FiniteH.{w'} A S.X₁ := by
  intro p
  have := h₂ p
  have hS' := shortExact_abSC hS
  cases p with
  | zero =>
    have : Mono (abSC S).f := hS'.mono_f
    refine finite_of_exact_noetherian (0 : (Fin 0 → A) →ₗ[A] _) (H.linearMap A S.f 0) ?_
    intro y hy
    refine ⟨0, ?_⟩
    rw [LinearMap.zero_apply]
    exact (H.map_zero_injective.{w'} (abSC S).f (hy.trans (map_zero _).symm)).symm
  | succ p =>
    have := h₃ p
    exact finite_of_exact_noetherian (H.δLinear A hS' p) (H.linearMap A S.f (p + 1))
      fun x hx => H.exact₁ hS' rfl x hx

/- English proof (translation)
Introduce `p` and use `have := h₂ p have := h₁ (p + 1) finite_H_X₃ A hS p`.
-/
theorem FiniteH.of_shortExact₃ {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : FiniteH.{w'} A S.X₁) (h₂ : FiniteH.{w'} A S.X₂) : FiniteH.{w'} A S.X₃ := fun p =>
  have := h₂ p
  have := h₁ (p + 1)
  finite_H_X₃ A hS p

end

end GroundTheory.Arith.SchemeCoh
