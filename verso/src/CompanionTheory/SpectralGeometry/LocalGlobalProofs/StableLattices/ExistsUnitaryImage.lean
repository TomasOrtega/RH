import Mathlib
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import Formalism.RealPlaceAnalysis.StatementA

noncomputable section

open ReciprocityTheory.ChartRestriction.DS

namespace GlobalTheory.CompanionTheory.Unitarize

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {X : Type*} [AddCommGroup X] [Module ℂ X]

/- English proof (translation)
Establish `hst : ∀ a b, ∀ x ∈ LinearMap.ker c, E a b x ∈ LinearMap.ker c`. Introduce `a b x hx`. Rewrite `hx`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[hc, hx, map_zero]`. Break down `hS _ hst with h | h` into its components or cases.

Conclude with `LinearMap.ker_eq_bot.1 h`. Conclude with `absurd (LinearMap.ker_eq_top.1 h) h0`.
-/
theorem injective_of_simple {M : Type*} [AddCommGroup M] [Module ℂ M]
    {E : Fin n → Fin n → Module.End ℂ X} {F : Fin n → Fin n → Module.End ℂ M}
    (hS : ∀ W : Submodule ℂ X, (∀ a b, ∀ x ∈ W, E a b x ∈ W) → W = ⊥ ∨ W = ⊤)
    (c : X →ₗ[ℂ] M) (hc : ∀ a b x, c (E a b x) = F a b (c x)) (h0 : c ≠ 0) :
    Function.Injective c := by
  have hst : ∀ a b, ∀ x ∈ LinearMap.ker c, E a b x ∈ LinearMap.ker c := by
    intro a b x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hc, hx, map_zero]
  rcases hS _ hst with h | h
  · exact LinearMap.ker_eq_bot.1 h
  · exact absurd (LinearMap.ker_eq_top.1 h) h0

/- English proof (translation)
Unfold `adjSign Formalism.REAL.sgn`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem adjSign_eq_sgn (ε : Fin n → Bool) (a b : Fin n) :
    adjSign ε a b = ((Formalism.REAL.sgn ε a b : ℝ) : ℂ) := by
  unfold adjSign Formalism.REAL.sgn
  split_ifs <;> simp

/- English proof (translation)
Establish `hinj : Function.Injective c` using `injective_of_simple hS c hc h0`. Use `set d : X →ₗ[ℂ] H := (smD ε σ).subtype ∘ₗ c with hd`. Establish `hdinj : Function.Injective d` using `Subtype.val_injective.comp hinj`. Set `e : X ≃ₗ[ℂ] LinearMap.range d` to `LinearEquiv.ofInjective d hdinj`. Establish `he : ∀ x, ((e x : LinearMap.range d) : H) = ((c x : smD ε σ) : H)` using `fun x => rfl`.

Set `E' : Fin n → Fin n → Module.End ℂ (LinearMap.range d)` to `fun a b => e.toLinearMap ∘ₗ E a b ∘ₗ e.symm.toLinearMap`. Establish `hE' : ∀ a b x, E' a b (e x) = e (E a b x)`. Introduce `a b x`. Simplify using `[E']`. Establish `hcoe : ∀ a b x, ((E' a b (e x) : LinearMap.range d) : H) = ((smE ε σ a b (c x) : smD ε σ) : H)`.

Introduce `a b x`. Rewrite using `[hE', he, hc]`. Establish `hgl : IsGlRep (smE ε σ)` using `(isDerivedOn_smE hσ).glRep`. Establish `hU : IsInfUnitary ε (smE ε σ)` using `isInfUnitary_of_isDerivedOn hσ (isDerivedOn_smE hσ)`. Use `⟨LinearMap.range d, E', e, he, ?_, ?_, fun a b x => (hE' a b x).symm⟩` and prove the remaining obligations.

Introduce `a b c' d'`. Use `LinearMap.ext fun y => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `e.surjective y`. Establish `h` using `LinearMap.congr_fun (hgl a b c' d') (c x)`. Establish `h'` using `congrArg (Subtype.val) h`.

Apply `Subtype.ext` to reduce the goal to its premises. Establish `hEE : ∀ a b c' d', ((E' a b (E' c' d' (e x)) : LinearMap.range d) : H) = ((smE ε σ a b (smE ε σ c' d' (c x)) : smD ε σ) : H)`. Introduce `a b c' d'`. Rewrite using `[hE', hcoe, hc]`. Simplify using `only [Module.End.mul_apply, LinearMap.sub_apply, Submodule.coe_sub] at h' ⊢`.

Rewrite using `[hEE, hEE, h']`. Apply the tactic sequence `split_ifs <;> simp [hcoe]`. Introduce `a b y z`. Take `⟨u, rfl⟩` from `e.surjective y`. Take `⟨v, rfl⟩` from `e.surjective z`.

Establish `h` using `hU a b (c u) (c v)`. Rewrite using `[← adjSign_eq_sgn]`. Rewrite using `[Submodule.coe_inner, Submodule.coe_inner, hcoe, hcoe, he, he]`. Simplify `h` using `[Submodule.coe_inner]`.
-/
theorem exists_unitary_image {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {E : Fin n → Fin n → Module.End ℂ X}
    (hS : ∀ W : Submodule ℂ X, (∀ a b, ∀ x ∈ W, E a b x ∈ W) → W = ⊥ ∨ W = ⊤)
    (c : X →ₗ[ℂ] smD ε σ) (hc : ∀ a b x, c (E a b x) = smE ε σ a b (c x)) (h0 : c ≠ 0) :
    ∃ (V : Submodule ℂ H) (E' : Fin n → Fin n → Module.End ℂ V) (e : X ≃ₗ[ℂ] V),
      (∀ x, ((e x : V) : H) = ((c x : smD ε σ) : H)) ∧
      Formalism.REAL.GlRel E' ∧ Formalism.REAL.IsUnitary ε E' ∧
      ∀ a b x, e (E a b x) = E' a b (e x) := by
  have hinj : Function.Injective c := injective_of_simple hS c hc h0
  set d : X →ₗ[ℂ] H := (smD ε σ).subtype ∘ₗ c with hd
  have hdinj : Function.Injective d := Subtype.val_injective.comp hinj
  let e : X ≃ₗ[ℂ] LinearMap.range d := LinearEquiv.ofInjective d hdinj
  have he : ∀ x, ((e x : LinearMap.range d) : H) = ((c x : smD ε σ) : H) := fun x => rfl
  let E' : Fin n → Fin n → Module.End ℂ (LinearMap.range d) := fun a b =>
    e.toLinearMap ∘ₗ E a b ∘ₗ e.symm.toLinearMap
  have hE' : ∀ a b x, E' a b (e x) = e (E a b x) := by
    intro a b x
    simp [E']
  have hcoe : ∀ a b x, ((E' a b (e x) : LinearMap.range d) : H) =
      ((smE ε σ a b (c x) : smD ε σ) : H) := by
    intro a b x
    rw [hE', he, hc]
  have hgl : IsGlRep (smE ε σ) := (isDerivedOn_smE hσ).glRep
  have hU : IsInfUnitary ε (smE ε σ) := isInfUnitary_of_isDerivedOn hσ (isDerivedOn_smE hσ)
  refine ⟨LinearMap.range d, E', e, he, ?_, ?_, fun a b x => (hE' a b x).symm⟩
  · intro a b c' d'
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := e.surjective y
    have h := LinearMap.congr_fun (hgl a b c' d') (c x)
    have h' := congrArg (Subtype.val) h
    apply Subtype.ext
    have hEE : ∀ a b c' d', ((E' a b (E' c' d' (e x)) : LinearMap.range d) : H) =
        ((smE ε σ a b (smE ε σ c' d' (c x)) : smD ε σ) : H) := by
      intro a b c' d'
      rw [hE', hcoe, hc]
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Submodule.coe_sub] at h' ⊢
    rw [hEE, hEE, h']
    split_ifs <;> simp [hcoe]
  · intro a b y z
    obtain ⟨u, rfl⟩ := e.surjective y
    obtain ⟨v, rfl⟩ := e.surjective z
    have h := hU a b (c u) (c v)
    rw [← adjSign_eq_sgn]
    rw [Submodule.coe_inner, Submodule.coe_inner, hcoe, hcoe, he, he]
    simpa [Submodule.coe_inner] using h

end GlobalTheory.CompanionTheory.Unitarize
