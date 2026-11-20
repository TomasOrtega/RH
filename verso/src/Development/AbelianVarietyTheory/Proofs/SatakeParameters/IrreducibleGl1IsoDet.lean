import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.GLOneChar

open GlobalTheory.SmGL

/- English proof (translation)
Introduce `k _ _ _ _ d V _ _ σ ω hd hirr hω`. Establish `hact : ∀ (g : GL (Fin d) k) (v : V), σ g v = (ω (Matrix.GeneralLinearGroup.det g) : ℂ) • v`. Introduce `g v`. Use `conv_lhs => rw [GlobalTheory.ProdSupport.eq_scalar_det hd g]`. Conclude with `hω _ v`.

Use `haveI : Nontrivial V := by`. Assume the negation of the conclusion as `hV`. Rewrite `hV` using `[not_nontrivial_iff_subsingleton]`. Establish `: (⊥ : Subrepresentation σ) = ⊤` using `Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _)`. Conclude with `bot_ne_top this`.

Take `⟨v, hv⟩` from `exists_ne (0 : V)`. Set `S : Subrepresentation σ` to `⟨ℂ ∙ v, fun g w hw => by`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hw`. Rewrite using `[hact, smul_smul]`. Conclude with `Submodule.mem_span_singleton.2 ⟨_, rfl⟩⟩`.

Establish `hS : S = ⊤`. Break down `eq_bot_or_eq_top S with h | h` into its components or cases. It suffices to derive a contradiction. Establish `: v ∈ S.toSubmodule` using `Submodule.mem_span_singleton_self v`. Rewrite `this` using `[h]`.

Conclude with `hv this`. Conclude with `h`. Establish `hsurj : Function.Surjective (LinearMap.toSpanSingleton ℂ V v)`. Introduce `w`. Establish `hw : w ∈ S.toSubmodule` using `by rw [hS]; trivial`.

Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hw`. Conclude with `⟨c, rfl⟩`. Establish `hinj : Function.Injective (LinearMap.toSpanSingleton ℂ V v)`. Introduce `a b hab`. Simplify using `only [LinearMap.toSpanSingleton_apply] at hab`.

Conclude with `smul_left_injective ℂ hv hab`. Set `e : ℂ ≃ₗ[ℂ] V` to `LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩`. Use `⟨(Representation.Equiv.mk e fun g => ?_).symm⟩` and prove the remaining obligations. Use extensionality with `c`. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, e, LinearEquiv.ofBijective_apply, LinearMap.toSpanSingleton_apply, detRep, ofChar_apply, detChar_apply, hact, smul_smul, smul_eq_mul]`.

Rewrite using `[mul_one, ← LinearEquiv.map_smul, smul_eq_mul, mul_one]`.
-/
theorem equiv_detRep_of_isIrreducible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin d) k) V) (ω : kˣ →* ℂˣ), d = 1 → σ.IsIrreducible → GlobalTheory.SmGL.HasCentralChar σ ω → Nonempty (σ.Equiv (GlobalTheory.SmGL.detRep (Fin d) ω)) := by
  intro k _ _ _ _ d V _ _ σ ω hd hirr hω
  have hact : ∀ (g : GL (Fin d) k) (v : V), σ g v = (ω (Matrix.GeneralLinearGroup.det g) : ℂ) • v := by
    intro g v
    conv_lhs => rw [GlobalTheory.ProdSupport.eq_scalar_det hd g]
    exact hω _ v
  haveI : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    have : (⊥ : Subrepresentation σ) = ⊤ :=
      Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _)
    exact bot_ne_top this
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let S : Subrepresentation σ := ⟨ℂ ∙ v, fun g w hw => by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    rw [hact, smul_smul]
    exact Submodule.mem_span_singleton.2 ⟨_, rfl⟩⟩
  have hS : S = ⊤ := by
    rcases eq_bot_or_eq_top S with h | h
    · exfalso
      have : v ∈ S.toSubmodule := Submodule.mem_span_singleton_self v
      rw [h] at this
      exact hv this
    · exact h
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton ℂ V v) := by
    intro w
    have hw : w ∈ S.toSubmodule := by rw [hS]; trivial
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    exact ⟨c, rfl⟩
  have hinj : Function.Injective (LinearMap.toSpanSingleton ℂ V v) := by
    intro a b hab
    simp only [LinearMap.toSpanSingleton_apply] at hab
    exact smul_left_injective ℂ hv hab
  let e : ℂ ≃ₗ[ℂ] V := LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩
  refine ⟨(Representation.Equiv.mk e fun g => ?_).symm⟩
  ext c
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, e,
    LinearEquiv.ofBijective_apply, LinearMap.toSpanSingleton_apply, detRep, ofChar_apply,
    detChar_apply, hact, smul_smul, smul_eq_mul]
  rw [mul_one, ← LinearEquiv.map_smul, smul_eq_mul, mul_one]

end GlobalTheory.GLOneChar
