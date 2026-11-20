import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open GlobalTheory.UnitLemma Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma.TorusAction

open InvAlg

variable {K : UQ} (B : InvAlg K)

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Use the resulting assumption.

Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem mem_mulLat_unit (u : B.Aˣ) (L : Submodule K.O B.A) (y : B.A) :
    y ∈ mulLat K.O (u : B.A) L ↔ ((u⁻¹ : B.Aˣ) : B.A) * y ∈ L := by
  unfold mulLat
  simp only [Submodule.mem_map, LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [← mul_assoc, Units.inv_mul, one_mul]
  · intro h
    exact ⟨_, h, by rw [← mul_assoc, Units.mul_inv, one_mul]⟩

/- English proof (translation)
Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sigma_eq_inv (t : B.Aˣ) (ht : t ∈ B.T) : B.σ (t : B.A) = ((t⁻¹ : B.Aˣ) : B.A) := by
  have h : (t : B.A) * B.σ (t : B.A) = 1 := ht
  calc B.σ (t : B.A) = ((t⁻¹ : B.Aˣ) : B.A) * ((t : B.A) * B.σ (t : B.A)) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = _ := by rw [h, mul_one]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem isLat_mulLat (u : B.Aˣ) (L : Submodule K.O B.A) (hL : IsLat K.O K.E L) :
    IsLat K.O K.E (mulLat K.O (u : B.A) L) := by
  refine ⟨hL.1.map _, ?_⟩
  have hc : ((mulLat K.O (u : B.A) L : Submodule K.O B.A) : Set B.A) =
      (LinearMap.mulLeft K.E (u : B.A)) '' (L : Set B.A) := by
    unfold mulLat; rw [Submodule.map_coe]; rfl
  rw [hc, Submodule.span_image, hL.2, Submodule.map_top, LinearMap.range_eq_top]
  intro y
  exact ⟨((u⁻¹ : B.Aˣ) : B.A) * y, by simp [← mul_assoc]⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Take a linear combination of the given relations to obtain the conclusion.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem torus_mem_X (K : UQ) (B : InvAlg K) (x : B.A) :
    ∀ t ∈ B.T, ∀ L ∈ B.X x, mulLat K.O (t : B.A) L ∈ B.X x := by
  intro t ht L hL
  obtain ⟨hlat, hg, hdual⟩ := hL
  have hs := sigma_eq_inv B t ht
  refine ⟨isLat_mulLat B t L hlat, ?_, ?_⟩
  · intro y hy
    rw [mem_mulLat_unit] at hy ⊢
    have := hg _ hy
    rwa [mul_left_comm] at this
  · intro y
    rw [mem_mulLat_unit, hdual]
    constructor
    · intro h z hz
      rw [mem_mulLat_unit] at hz
      have := h _ hz
      have e : B.herm x (((t⁻¹ : B.Aˣ) : B.A) * y) (((t⁻¹ : B.Aˣ) : B.A) * z) = B.herm x y z := by
        have hs' : B.σ ((t⁻¹ : B.Aˣ) : B.A) = (t : B.A) := by rw [← hs, B.σ_σ]
        unfold InvAlg.herm; rw [map_mul B.σ, hs']
        congr 1
        linear_combination (x * y * B.σ z) * Units.inv_mul t
      rwa [e] at this
    · intro h w hw
      have hz : (t : B.A) * w ∈ mulLat K.O (t : B.A) L := by
        rw [mem_mulLat_unit, ← mul_assoc, Units.inv_mul, one_mul]; exact hw
      have := h _ hz
      have e : B.herm x (((t⁻¹ : B.Aˣ) : B.A) * y) w = B.herm x y ((t : B.A) * w) := by
        unfold InvAlg.herm; rw [map_mul B.σ, hs]; congr 1; ring
      rwa [e]

end GlobalTheory.UnitLemma.TorusAction
