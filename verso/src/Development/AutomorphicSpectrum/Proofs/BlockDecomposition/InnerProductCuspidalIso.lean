import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelSurjective.Transp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PermutationMatrixPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleIffIrreducibleStatement

open Polynomial CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open ReciprocityTheory.Ty.Fin

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.IpIso

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Rewrite using `[PI.GreenLabelSurjWork.glEquiv_symm_val, PI.GreenLabelSurjWork.glEquiv_val]`. Simplify using the standard rewrite rules.
-/
theorem glEquiv_symm_symm (e : α ≃ β) (g : GL α K) :
    (glEquiv K e.symm).symm g = glEquiv K e g := by
  apply Units.ext
  ext i j
  rw [PI.GreenLabelSurjWork.glEquiv_symm_val, PI.GreenLabelSurjWork.glEquiv_val]
  simp

/- English proof (translation)
Rewrite using `[(GlobalTheory.T.permutation_matrix_properties K β (e.symm.trans e')).2.1]`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Rewrite using `[PI.GreenLabelSurjWork.glEquiv_val, PI.GreenLabelSurjWork.glEquiv_val, PI.GreenLabelSurjWork.glEquiv_val]`. Simplify using the standard rewrite rules.
-/
theorem glEquiv_conj (e e' : α ≃ β) (g : GL α K) :
    glEquiv K e' g =
      pm K (e.symm.trans e') * glEquiv K e g * (pm K (e.symm.trans e'))⁻¹ := by
  rw [(GlobalTheory.T.permutation_matrix_properties K β (e.symm.trans e')).2.1]
  apply Units.ext
  ext i j
  rw [PI.GreenLabelSurjWork.glEquiv_val, PI.GreenLabelSurjWork.glEquiv_val,
    PI.GreenLabelSurjWork.glEquiv_val]
  simp

/- English proof (translation)
Use `set P : GL β K := pm K (e.symm.trans e') with hP`. Set `m : (mu : Type) ≃ₗ[ℂ] (mu : Type)` to `LinearEquiv.ofLinear (mu.ρ P⁻¹) (mu.ρ P) (by rw [← Module.End.mul_eq_comp, ← map_mul]; simp; rfl) (by rw [← Module.End.mul_eq_comp, ← map_mul]; simp; rfl)`. Use `⟨φ.trans m, fun g x => ?_⟩` and prove the remaining obligations. Establish `hm : ∀ y, m y = mu.ρ P⁻¹ y` using `fun _ => rfl`. Simplify using `only [LinearEquiv.trans_apply, hm]`.

Rewrite using `[h, glEquiv_conj e e' g, ← hP]`. Establish `: P⁻¹ * (P * glEquiv K e g * P⁻¹) = glEquiv K e g * P⁻¹` using `by group`. Rewrite using `[← Module.End.mul_apply, ← map_mul, this, map_mul, Module.End.mul_apply]`.
-/
theorem along_of_along (lam : FDRep ℂ (GL α K)) (mu : FDRep ℂ (GL β K)) (e e' : α ≃ β)
    (φ : lam ≃ₗ[ℂ] mu) (h : ∀ g x, φ (lam.ρ g x) = mu.ρ (glEquiv K e' g) (φ x)) :
    ∃ ψ : lam ≃ₗ[ℂ] mu, ∀ g x, ψ (lam.ρ g x) = mu.ρ (glEquiv K e g) (ψ x) := by
  set P : GL β K := pm K (e.symm.trans e') with hP
  let m : (mu : Type) ≃ₗ[ℂ] (mu : Type) := LinearEquiv.ofLinear (mu.ρ P⁻¹) (mu.ρ P)
    (by rw [← Module.End.mul_eq_comp, ← map_mul]; simp; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul]; simp; rfl)
  refine ⟨φ.trans m, fun g x => ?_⟩
  have hm : ∀ y, m y = mu.ρ P⁻¹ y := fun _ => rfl
  simp only [LinearEquiv.trans_apply, hm]
  rw [h, glEquiv_conj e e' g, ← hP]
  have : P⁻¹ * (P * glEquiv K e g * P⁻¹) = glEquiv K e g * P⁻¹ := by group
  rw [← Module.End.mul_apply, ← map_mul, this, map_mul, Module.End.mul_apply]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨e', φ, h⟩`. Conclude with `along_of_along lam mu e e' φ h`. Introduce and unpack `⟨φ, h⟩`. Conclude with `⟨e, φ, h⟩`.
-/
theorem cuspIso_iff_along (lam : FDRep ℂ (GL α K)) (mu : FDRep ℂ (GL β K)) (e : α ≃ β) :
    CuspIso K lam mu ↔
      ∃ φ : lam ≃ₗ[ℂ] mu, ∀ g x, φ (lam.ρ g x) = mu.ρ (glEquiv K e g) (φ x) := by
  constructor
  · rintro ⟨e', φ, h⟩
    exact along_of_along lam mu e e' φ h
  · rintro ⟨φ, h⟩
    exact ⟨e, φ, h⟩

/- English proof (translation)
Rewrite using `[GlobalTheory.T.simple_iff_irreducible.2 (GL α K) lam (transp e.symm mu)]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨ε, h⟩`. Use `⟨ε, fun g x => ?_⟩` and prove the remaining obligations. Use `h g x` as an intermediate fact.

Rewrite `this` using `[PI.GreenLabelSurjWork.transp_ρ, glEquiv_symm_symm]`. Conclude with `this`. Introduce and unpack `⟨φ, h⟩`. Use `⟨φ, fun g x => ?_⟩` and prove the remaining obligations. Rewrite using `[PI.GreenLabelSurjWork.transp_ρ, glEquiv_symm_symm]`.

Conclude with `h g x`.
-/
theorem iso_transp_symm_iff (lam : FDRep ℂ (GL α K)) (mu : FDRep ℂ (GL β K)) (e : α ≃ β) :
    Nonempty (lam ≅ transp e.symm mu) ↔
      ∃ φ : lam ≃ₗ[ℂ] mu, ∀ g x, φ (lam.ρ g x) = mu.ρ (glEquiv K e g) (φ x) := by
  rw [GlobalTheory.T.simple_iff_irreducible.2 (GL α K) lam (transp e.symm mu)]
  constructor
  · rintro ⟨ε, h⟩
    refine ⟨ε, fun g x => ?_⟩
    have := h g x
    rw [PI.GreenLabelSurjWork.transp_ρ, glEquiv_symm_symm] at this
    exact this
  · rintro ⟨φ, h⟩
    refine ⟨φ, fun g x => ?_⟩
    rw [PI.GreenLabelSurjWork.transp_ρ, glEquiv_symm_symm]
    exact h g x

/- English proof (translation)
Rewrite using `[GlobalTheory.T.simple_iff_irreducible.2 (GL β K) (transp e lam) mu]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨ε, h⟩`. Use `⟨ε, fun g x => ?_⟩` and prove the remaining obligations. Use `h (glEquiv K e g) x` as an intermediate fact.

Rewrite `this` using `[PI.GreenLabelSurjWork.transp_ρ, MulEquiv.symm_apply_apply]`. Conclude with `this`. Introduce and unpack `⟨φ, h⟩`. Use `⟨φ, fun γ x => ?_⟩` and prove the remaining obligations. Rewrite using `[PI.GreenLabelSurjWork.transp_ρ]`.

Use `h ((glEquiv K e).symm γ) x` as an intermediate fact. Rewrite `this` using `[MulEquiv.apply_symm_apply]`. Conclude with `this`.
-/
theorem iso_transp_iff (lam : FDRep ℂ (GL α K)) (mu : FDRep ℂ (GL β K)) (e : α ≃ β) :
    Nonempty (transp e lam ≅ mu) ↔
      ∃ φ : lam ≃ₗ[ℂ] mu, ∀ g x, φ (lam.ρ g x) = mu.ρ (glEquiv K e g) (φ x) := by
  rw [GlobalTheory.T.simple_iff_irreducible.2 (GL β K) (transp e lam) mu]
  constructor
  · rintro ⟨ε, h⟩
    refine ⟨ε, fun g x => ?_⟩
    have := h (glEquiv K e g) x
    rw [PI.GreenLabelSurjWork.transp_ρ, MulEquiv.symm_apply_apply] at this
    exact this
  · rintro ⟨φ, h⟩
    refine ⟨φ, fun γ x => ?_⟩
    rw [PI.GreenLabelSurjWork.transp_ρ]
    have := h ((glEquiv K e).symm γ) x
    rw [MulEquiv.apply_symm_apply] at this
    exact this

/- English proof (translation)
Establish `hT : Simple (transp e.symm mu)` using `PI.GreenLabelSurjWork.transp_simple e.symm mu hm`. Establish `hc : ∀ g, mu.character (glEquiv K e g) = (transp e.symm mu).character g`. Introduce `g`. Use `show _ = LinearMap.trace ℂ _ ((transp e.symm mu).ρ g)`. Rewrite using `[PI.GreenLabelSurjWork.transp_ρ, glEquiv_symm_symm]`.

Both sides reduce to the same expression. Use `haveI : Invertible (Nat.card (GL α K) : ℂ) := invertibleOfNonzero (by`. Conclude with `Nat.card_pos.ne')` after adjusting the coercions. Establish `ho` using `FDRep.char_orthonormal (transp e.symm mu) lam`. Establish `hiff : CuspIso K lam mu ↔ Nonempty (transp e.symm mu ≅ lam)`.

Rewrite using `[cuspIso_iff_along lam mu e, ← iso_transp_symm_iff lam mu e]`. Conclude with `⟨fun ⟨i⟩ => ⟨i.symm⟩, fun ⟨i⟩ => ⟨i.symm⟩⟩`. Simplify using `only [ip, Set.ncard_univ, Set.mem_univ, if_true, hc]`. Simplify using `only [mul_comm (lam.character _)]`. Rewrite using `[ho]`.

Simplify using `only [hiff]`.
-/
theorem ip_char (lam : FDRep ℂ (GL α K)) (mu : FDRep ℂ (GL β K)) (e : α ≃ β)
    (hl : Simple lam) (hm : Simple mu) :
    ip Set.univ lam.character (fun x => mu.character (glEquiv K e x)) =
      (open Classical in if CuspIso K lam mu then 1 else 0) := by
  classical
  have hT : Simple (transp e.symm mu) := PI.GreenLabelSurjWork.transp_simple e.symm mu hm
  have hc : ∀ g, mu.character (glEquiv K e g) = (transp e.symm mu).character g := by
    intro g
    show _ = LinearMap.trace ℂ _ ((transp e.symm mu).ρ g)
    rw [PI.GreenLabelSurjWork.transp_ρ, glEquiv_symm_symm]
    rfl
  haveI : Invertible (Nat.card (GL α K) : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  have ho := FDRep.char_orthonormal (transp e.symm mu) lam
  have hiff : CuspIso K lam mu ↔ Nonempty (transp e.symm mu ≅ lam) := by
    rw [cuspIso_iff_along lam mu e, ← iso_transp_symm_iff lam mu e]
    exact ⟨fun ⟨i⟩ => ⟨i.symm⟩, fun ⟨i⟩ => ⟨i.symm⟩⟩
  simp only [ip, Set.ncard_univ, Set.mem_univ, if_true, hc]
  simp only [mul_comm (lam.character _)]
  rw [ho]
  simp only [hiff]

/- English proof (translation)
Introduce `K _ _ _ α β _ _ _ _ lam mu e hl hm`. Use `⟨ip_char lam mu e hl hm, ?_⟩` and prove the remaining obligations. Rewrite using `[cuspIso_iff_along lam mu e, iso_transp_iff lam mu e]`.
-/
theorem main : ReciprocityTheory.Ty.Fin.St.IpCuspIso := by
  intro K _ _ _ α β _ _ _ _ lam mu e hl hm
  refine ⟨ip_char lam mu e hl hm, ?_⟩
  rw [cuspIso_iff_along lam mu e, iso_transp_iff lam mu e]

end GlobalTheory.CompanionTheory.TyFin.IpIso
