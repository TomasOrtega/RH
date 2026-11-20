import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lpart
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHolomorphyInParameter
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2DualWhittakerPair.PfCont

/- English proof (translation)
By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.
-/
theorem mul_concat_column {F : Type} [Field F] (u A : Matrix (Fin 2) (Fin 2) F) (y : Fin 2 → F) :
    u * cat3 A y = cat3 (u * A) (u *ᵥ y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cat3, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem continuous_Rpart_Pf : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle),
    IsStd ψ → ∀ Φ ∈ LFS.SB F, ∀ h : GL (Fin 2) F,
      Continuous fun z : GL (Fin 2) F => Rpart ψ (Pf Φ h z) := by
  intro F _ _ _ _ _ _ ψ _ Φ hΦ h
  obtain ⟨U, hU⟩ := GlobalTheory.CompanionTheory.LFHolP.exists_left_invariant hΦ.1 hΦ.2
  have hP : ∀ g u : GL (Fin 2) F, u ∈ U → Pf Φ h (g * u) = Pf Φ h g := by
    intro g u hu
    funext M
    have hu' : u⁻¹ ∈ U := inv_mem hu
    have h1 := hU _ hu' (cat3 ((g⁻¹ : GL (Fin 2) F).val * M * (tinv h).val)
      ((g⁻¹ : GL (Fin 2) F).val *ᵥ e1))
    rw [mul_concat_column] at h1
    simp only [Pf, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, ← Matrix.mulVec_mulVec] at h1 ⊢
    exact h1
  have hl : IsLocallyConstant fun z : GL (Fin 2) F => Rpart ψ (Pf Φ h z) :=
    GlobalTheory.CompanionTheory.RankinSelbergMellinContinuation.isLocallyConstant_of_invariant _ U.toSubgroup U.isOpen
      fun g u hu => by simp only [hP g u hu]
  exact hl.continuous

end GlobalTheory.CompanionTheory.GL2DualWhittakerPair.PfCont
