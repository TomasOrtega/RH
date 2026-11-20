import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll

open CategoryTheory ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

omit [Fintype K] [DecidableEq K] in

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[glReindex_val]`.
-/
theorem glReindex_glReindex (e₁ : α ≃ β) (e₂ : β ≃ γ) (g : GL α K) :
    glReindex K e₂ (glReindex K e₁ g) = glReindex K (e₁.trans e₂) g := by
  ext i j
  simp [glReindex_val]

omit [Fintype K] [DecidableEq K] in

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[glReindex_val]`.
-/
theorem glReindex_refl (g : GL α K) : glReindex K (Equiv.refl α) g = g := by
  ext i j
  simp [glReindex_val]

omit [Fintype K] [DecidableEq K] in

/- English proof (translation)
Rewrite using `[glReindex_glReindex, Equiv.symm_trans_self, glReindex_refl]`.
-/
theorem glReindex_symm_apply (e : α ≃ β) (g : GL β K) :
    glReindex K e (glReindex K e.symm g) = g := by
  rw [glReindex_glReindex, Equiv.symm_trans_self, glReindex_refl]

omit [Fintype K] [DecidableEq K] in

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem reRep_ρ_apply (e : α ≃ β) (τ : FDRep ℂ (GL α K)) (g : GL β K) :
    (reRep e τ).ρ g = τ.ρ ((glEquiv K e).symm g) := by
  rfl

/- English proof (translation)
Introduce `K _ _ _ α β γ _ _ _ _ _ _ lam lam' mu nu e`. Use `⟨?_, ?_, ?_, ?_, fun g => glReindex_symm_apply e g⟩` and prove the remaining obligations. Introduce and unpack `⟨e, φ, h⟩`. Use `⟨e.symm, φ.symm, fun g x => φ.injective ?_⟩` and prove the remaining obligations. Rewrite using `[φ.apply_symm_apply, h, φ.apply_symm_apply, glReindex_symm_apply]`.

Introduce and unpack `⟨e₁, φ₁, h₁⟩ ⟨e₂, φ₂, h₂⟩`. Use `⟨e₁.trans e₂, φ₁.trans φ₂, fun g x => ?_⟩` and prove the remaining obligations. Simplify using `only [LinearEquiv.trans_apply, h₁, h₂, glReindex_glReindex]`. Introduce and unpack `⟨i⟩`. Use `⟨Equiv.refl α, FDRep.isoToLinearEquiv i, fun g x => ?_⟩` and prove the remaining obligations.

Rewrite using `[glReindex_refl]`. Use `FDRep.Iso.conj_ρ i g` as an intermediate fact. Rewrite using `[this]`. Simplify using `[LinearEquiv.conj_apply]`. Use `⟨e, LinearEquiv.refl ℂ _, fun g x => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `lam.ρ g x = lam.ρ ((glEquiv K e).symm (glEquiv K e g)) x`. Rewrite using `[MulEquiv.symm_apply_apply]`.
-/
theorem cuspIsoFacts : ReciprocityTheory.Ty.Fin.St.CuspIsoFacts := by
  intro K _ _ _ α β γ _ _ _ _ _ _ lam lam' mu nu e
  refine ⟨?_, ?_, ?_, ?_, fun g => glReindex_symm_apply e g⟩
  · rintro ⟨e, φ, h⟩
    refine ⟨e.symm, φ.symm, fun g x => φ.injective ?_⟩
    rw [φ.apply_symm_apply, h, φ.apply_symm_apply, glReindex_symm_apply]
  · rintro ⟨e₁, φ₁, h₁⟩ ⟨e₂, φ₂, h₂⟩
    refine ⟨e₁.trans e₂, φ₁.trans φ₂, fun g x => ?_⟩
    simp only [LinearEquiv.trans_apply, h₁, h₂, glReindex_glReindex]
  · rintro ⟨i⟩
    refine ⟨Equiv.refl α, FDRep.isoToLinearEquiv i, fun g x => ?_⟩
    rw [glReindex_refl]
    have := FDRep.Iso.conj_ρ i g
    rw [this]
    simp [LinearEquiv.conj_apply]
  · refine ⟨e, LinearEquiv.refl ℂ _, fun g x => ?_⟩
    change lam.ρ g x = lam.ρ ((glEquiv K e).symm (glEquiv K e g)) x
    rw [MulEquiv.symm_apply_apply]

end GlobalTheory.CompanionTheory.TyFin
