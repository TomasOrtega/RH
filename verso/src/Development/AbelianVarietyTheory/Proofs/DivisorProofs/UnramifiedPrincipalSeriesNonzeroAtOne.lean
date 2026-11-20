import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WEMulNUMulTD
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsBiequivariant
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct

namespace GlobalTheory.PrinTwo.Spher

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

local notation "E₂" => two (stdSum (rfl : 1 + 1 = 1 + 1))

def leftChar (μ₁ μ₂ : kˣ →* ℂˣ) : parab k E₂ →* ℂˣ :=
  (deltaHalf k (Two (Fin 1) (Fin 1))).comp (leviProj k E₂) *
    (detChar (Fin 1) μ₁).comp
      ((Pi.evalMonoidHom (fun x => GL (Two (Fin 1) (Fin 1) x) k) false).comp (leviProj k E₂)) *
    (detChar (Fin 1) μ₂).comp
      ((Pi.evalMonoidHom (fun x => GL (Two (Fin 1) (Fin 1) x) k) true).comp (leviProj k E₂))

/- English proof (translation)
Use `show (deltaHalf k (Two (Fin 1) (Fin 1)) (leviProj k _ p) : ℂ) • extTensor (detRep (Fin 1) μ₁) (detRep (Fin 1) μ₂) ((leviTwo k (Fin 1) (Fin 1)).symm (leviProj k _ p)) ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) = _`. Rewrite using `[extTensor_tmul]`. Simplify using `only [detRep, ofChar_apply, detChar_apply]`. Rewrite using `[show ∀ a c : ℂ, a ⊗ₜ[ℂ] c = (a * c) • ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) from fun a c => by`. Rewrite using `[mul_smul, ← TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_one, mul_one],`.

Use the proof step `smul_smul]`. Use `congr 1`. Simplify using `only [leftChar, MonoidHom.mul_apply, MonoidHom.comp_apply, Pi.evalMonoidHom_apply, detChar_apply, Units.val_mul, mul_one]`. Rewrite using `[← mul_assoc]`. Both sides reduce to the same expression.
-/
theorem act_one (μ₁ μ₂ : kˣ →* ℂˣ) (p : parab k E₂) :
    ((twist ((extTensor (detRep (Fin 1) μ₁) (detRep (Fin 1) μ₂)).comp
        (leviTwo k (Fin 1) (Fin 1)).symm.toMonoidHom) (deltaHalf k (Two (Fin 1) (Fin 1)))).comp
      (leviProj k E₂)) p ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) =
    (leftChar μ₁ μ₂ p : ℂ) • ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) := by
  show (deltaHalf k (Two (Fin 1) (Fin 1)) (leviProj k _ p) : ℂ) •
    extTensor (detRep (Fin 1) μ₁) (detRep (Fin 1) μ₂)
      ((leviTwo k (Fin 1) (Fin 1)).symm (leviProj k _ p)) ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) = _
  rw [extTensor_tmul]
  simp only [detRep, ofChar_apply, detChar_apply]
  rw [show ∀ a c : ℂ, a ⊗ₜ[ℂ] c = (a * c) • ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) from fun a c => by
    rw [mul_smul, ← TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_one, mul_one],
    smul_smul]
  congr 1
  simp only [leftChar, MonoidHom.mul_apply, MonoidHom.comp_apply, Pi.evalMonoidHom_apply, detChar_apply,
    Units.val_mul, mul_one]
  rw [← mul_assoc]
  rfl

/- English proof (translation)
Consider the cases of `b`. Use `⟨E₂ ⟨false, default⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[GeneralLinearGroup.val_det_apply, Matrix.det_unique]`. Both sides reduce to the same expression. Use `⟨E₂ ⟨true, default⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[GeneralLinearGroup.val_det_apply, Matrix.det_unique]`. Both sides reduce to the same expression.
-/
theorem val_det_leviProj (p : parab k E₂) (b : Bool) : ∃ i : Fin (1 + 1),
    ((GeneralLinearGroup.det (leviProj k E₂ p b) : kˣ) : k) = (p : GL (Fin (1 + 1)) k).val i i := by
  cases b
  · refine ⟨E₂ ⟨false, default⟩, ?_⟩
    rw [GeneralLinearGroup.val_det_apply, Matrix.det_unique]
    rfl
  · refine ⟨E₂ ⟨true, default⟩, ?_⟩
    rw [GeneralLinearGroup.val_det_apply, Matrix.det_unique]
    rfl

/- English proof (translation)
Establish `hp' : ((p⁻¹ : parab k E₂) : GL (Fin (1 + 1)) k) ∈ KO k (Fin (1 + 1))`. Rewrite using `[Subgroup.coe_inv]`. Conclude with `inv_mem hp`. Take `⟨h1, -⟩` from `(GlobalTheory.SplitFlip.mem_KO_iff _).1 hp`. Take `⟨h2, -⟩` from `(GlobalTheory.SplitFlip.mem_KO_iff _).1 hp'`.

Establish `a1 : valuation k ((GeneralLinearGroup.det (leviProj k E₂ p b) : kˣ) : k) ≤ 1`. Take `⟨i, hi⟩` from `val_det_leviProj p b`. Rewrite using `[hi]`. Conclude with `h1 _ _`. Establish `a2 : valuation k ((GeneralLinearGroup.det (leviProj k E₂ p⁻¹ b) : kˣ) : k) ≤ 1`.

Take `⟨i, hi⟩` from `val_det_leviProj p⁻¹ b`. Rewrite using `[hi]`. Conclude with `h2 _ _`. Rewrite `a2` using `[map_inv, Pi.inv_apply, map_inv, Units.val_inv_eq_inv_val, map_inv₀]`. Conclude with `le_antisymm a1 ((inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (Units.ne_zero _)))).1 a2)`.
-/
theorem valuation_det_leviProj (p : parab k E₂) (hp : (p : GL (Fin (1 + 1)) k) ∈ KO k (Fin (1 + 1)))
    (b : Bool) : valuation k ((GeneralLinearGroup.det (leviProj k E₂ p b) : kˣ) : k) = 1 := by
  have hp' : ((p⁻¹ : parab k E₂) : GL (Fin (1 + 1)) k) ∈ KO k (Fin (1 + 1)) := by
    rw [Subgroup.coe_inv]; exact inv_mem hp
  obtain ⟨h1, -⟩ := (GlobalTheory.SplitFlip.mem_KO_iff _).1 hp
  obtain ⟨h2, -⟩ := (GlobalTheory.SplitFlip.mem_KO_iff _).1 hp'
  have a1 : valuation k ((GeneralLinearGroup.det (leviProj k E₂ p b) : kˣ) : k) ≤ 1 := by
    obtain ⟨i, hi⟩ := val_det_leviProj p b; rw [hi]; exact h1 _ _
  have a2 : valuation k ((GeneralLinearGroup.det (leviProj k E₂ p⁻¹ b) : kˣ) : k) ≤ 1 := by
    obtain ⟨i, hi⟩ := val_det_leviProj p⁻¹ b; rw [hi]; exact h2 _ _
  rw [map_inv, Pi.inv_apply, map_inv, Units.val_inv_eq_inv_val, map_inv₀] at a2
  exact le_antisymm a1 ((inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (Units.ne_zero _)))).1 a2)

/- English proof (translation)
Simplify using `only [leftChar, MonoidHom.mul_apply, MonoidHom.comp_apply, Pi.evalMonoidHom_apply, detChar_apply, deltaHalf_apply, Fintype.prod_bool]`. Rewrite using `[isUnram_absPow k _ _ (valuation_det_leviProj p hp true), isUnram_absPow k _ _ (valuation_det_leviProj p hp false), h₁ _ (valuation_det_leviProj p hp false), h₂ _ (valuation_det_leviProj p hp true)]`. Simplify using the standard rewrite rules.
-/
theorem leftChar_eq_one {μ₁ μ₂ : kˣ →* ℂˣ} (h₁ : IsUnram μ₁) (h₂ : IsUnram μ₂) (p : parab k E₂)
    (hp : (p : GL (Fin (1 + 1)) k) ∈ KO k (Fin (1 + 1))) : leftChar μ₁ μ₂ p = 1 := by
  simp only [leftChar, MonoidHom.mul_apply, MonoidHom.comp_apply, Pi.evalMonoidHom_apply, detChar_apply,
    deltaHalf_apply, Fintype.prod_bool]
  rw [isUnram_absPow k _ _ (valuation_det_leviProj p hp true),
    isUnram_absPow k _ _ (valuation_det_leviProj p hp false), h₁ _ (valuation_det_leviProj p hp false),
    h₂ _ (valuation_det_leviProj p hp true)]
  simp

end GlobalTheory.PrinTwo.Spher

namespace GlobalTheory.PrinTwo

open Spher

/- English proof (translation)
Introduce `k _ _ _ _ μ₁ μ₂ h₁ h₂`. Take `⟨f, f1, fl, fr⟩` from `GlobalTheory.ParahoricVec.exists_biequivariant (parab k (two (stdSum (rfl : 1 + 1 = 1 + 1)))) (KO k (Fin (1 + 1))) (leftChar μ₁ μ₂) 1 (fun p j h => by`. Rewrite using `[MonoidHom.one_apply]`. Conclude with `leftChar_eq_one h₁ h₂ p (h ▸ j.2))`. Set `F : GL (Fin (1 + 1)) k → ℂ ⊗[ℂ] ℂ` to `fun g => f g • ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ))`.

Use `⟨⟨⟨F, fun p g => ?_⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show f ((p : GL (Fin (1 + 1)) k) * g) • ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) = _`. Simplify using `only [F]`. Rewrite using `[map_smul, act_one, fl, smul_smul, mul_comm]`. Use `mem_smoothPart_of_nhds (Filter.mem_of_superset (GlobalTheory.SplitFlip.isOpen_KO.mem_nhds (one_mem _)) fun u hu => ?_)` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Use `show f (x * u) • ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) = f x • ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ))`. Use `fr x ⟨u, hu⟩` as an intermediate fact. Simplify using `only [MonoidHom.one_apply, Units.val_one, mul_one] at this`.

Rewrite using `[this]`. Use `show TensorProduct.lid ℂ ℂ (f 1 • ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ))) ≠ 0`. Simplify using `[f1]`.
-/
theorem exists_ev_one_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ), GlobalTheory.SplitWeil.IsUnram μ₁ → GlobalTheory.SplitWeil.IsUnram μ₂ → ∃ f : GlobalTheory.PrinTwo.PSp μ₁ μ₂, GlobalTheory.PrinTwo.ev f 1 ≠ 0 := by
  intro k _ _ _ _ μ₁ μ₂ h₁ h₂
  obtain ⟨f, f1, fl, fr⟩ := GlobalTheory.ParahoricVec.exists_biequivariant (parab k (two (stdSum (rfl : 1 + 1 = 1 + 1))))
    (KO k (Fin (1 + 1))) (leftChar μ₁ μ₂) 1 (fun p j h => by
      rw [MonoidHom.one_apply]
      exact leftChar_eq_one h₁ h₂ p (h ▸ j.2))
  let F : GL (Fin (1 + 1)) k → ℂ ⊗[ℂ] ℂ := fun g => f g • ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ))
  refine ⟨⟨⟨F, fun p g => ?_⟩, ?_⟩, ?_⟩
  · show f ((p : GL (Fin (1 + 1)) k) * g) • ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) = _
    simp only [F]
    rw [map_smul, act_one, fl, smul_smul, mul_comm]
  · refine mem_smoothPart_of_nhds (Filter.mem_of_superset
      (GlobalTheory.SplitFlip.isOpen_KO.mem_nhds (one_mem _)) fun u hu => ?_)
    apply Subtype.ext
    funext x
    show f (x * u) • ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) = f x • ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ))
    have := fr x ⟨u, hu⟩
    simp only [MonoidHom.one_apply, Units.val_one, mul_one] at this
    rw [this]
  · show TensorProduct.lid ℂ ℂ (f 1 • ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ))) ≠ 0
    simp [f1]

end GlobalTheory.PrinTwo
