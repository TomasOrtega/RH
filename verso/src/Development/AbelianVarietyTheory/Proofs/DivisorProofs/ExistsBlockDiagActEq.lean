import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions

open GlobalTheory.FinGL Formalism.L2.DIV Module

namespace GlobalTheory.FinGL

/- English proof (translation)
Use `⟨Subgroup.inclusion (GlobalTheory.Parabolic.levi_le_blockTri b) (GlobalTheory.Parabolic.leviProj b p), ?_, fun i k => GlobalTheory.Parabolic.leviProj_apply b p i k⟩` and prove the remaining obligations. Use `set m := Subgroup.inclusion (GlobalTheory.Parabolic.levi_le_blockTri b) (GlobalTheory.Parabolic.leviProj b p) with hm`. Establish `h1 : GlobalTheory.Parabolic.leviProj b (m⁻¹ * p) = 1`. Rewrite using `[map_mul, map_inv, hm, GlobalTheory.Parabolic.leviProj_inclusion, inv_mul_cancel]`. Establish `h2 : σ (m⁻¹ * p) = 1`.

Use `hσ.infl _ fun i j hij => ?_` and prove the remaining obligations. Establish `e` using `GlobalTheory.Parabolic.leviProj_apply b (m⁻¹ * p) i j`. Rewrite `e` using `[h1, if_pos hij]`. Rewrite using `[← e]`. Simplify using the standard rewrite rules.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem IsCuspDatum.exists_blockDiag_act_eq (F : Type) [Field F] (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) (hσ : IsCuspDatum b σ)
    (p : blockTri (κ := F) b) :
    ∃ m : blockTri (κ := F) b, σ m = σ p ∧ ∀ i k : Fin r, ((m : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k =
      if b i = b k then ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k else 0 := by
  refine ⟨Subgroup.inclusion (GlobalTheory.Parabolic.levi_le_blockTri b) (GlobalTheory.Parabolic.leviProj b p), ?_,
    fun i k => GlobalTheory.Parabolic.leviProj_apply b p i k⟩
  set m := Subgroup.inclusion (GlobalTheory.Parabolic.levi_le_blockTri b) (GlobalTheory.Parabolic.leviProj b p) with hm
  have h1 : GlobalTheory.Parabolic.leviProj b (m⁻¹ * p) = 1 := by
    rw [map_mul, map_inv, hm, GlobalTheory.Parabolic.leviProj_inclusion, inv_mul_cancel]
  have h2 : σ (m⁻¹ * p) = 1 := by
    refine hσ.infl _ fun i j hij => ?_
    have e := GlobalTheory.Parabolic.leviProj_apply b (m⁻¹ * p) i j
    rw [h1, if_pos hij] at e
    rw [← e]
    simp
  calc σ m = σ m * σ (m⁻¹ * p) := by rw [h2, mul_one]
    _ = σ p := by rw [← map_mul, mul_inv_cancel_left]

end GlobalTheory.FinGL
