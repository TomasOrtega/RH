import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem discriminant_slash_specialLinearGroup (x : SL(2, ℤ)) :
    (ModularForm.discriminant ∣[(12 : ℤ)] x) = ModularForm.discriminant :=
  (isCF_coe_top CuspForm.discriminant).1 x (Subgroup.mem_top x)

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem exists_eq_discriminant_mul (Γ : Subgroup SL(2, ℤ)) (K : ℤ) (H : ℍ → ℂ) (hH : IsMF Γ K H)
    (hdec : ∀ x : SL(2, ℤ), (H ∣[K] x) =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im)) :
    ∃ G : ℍ → ℂ, IsMF Γ (K - 12) G ∧ H = ModularForm.discriminant * G := by
  have hsl : ∀ x : SL(2, ℤ), (H / ModularForm.discriminant) ∣[K - 12] x =
      (H ∣[K] x) / ModularForm.discriminant := by
    intro x
    have := ModularForm.div_slash_SL2 K 12 x H ModularForm.discriminant
    rw [discriminant_slash_specialLinearGroup] at this
    exact this
  refine ⟨H / ModularForm.discriminant, ⟨fun γ hγ => ?_, ?_, fun x => ?_⟩, ?_⟩
  · rw [hsl, hH.1 γ hγ]
  · exact hH.2.1.div CuspForm.discriminant.holo' ModularForm.discriminant_ne_zero
  · rw [hsl, IsBoundedAtImInfty, BoundedAtFilter]
    exact (Asymptotics.div_isBoundedUnder_of_isBigO ((hdec x).trans ModularForm.exp_isBigO_discriminant)).isBigO_one ℝ
  · ext τ
    simp [mul_div_cancel₀ _ (ModularForm.discriminant_ne_zero τ)]

end GlobalTheory
