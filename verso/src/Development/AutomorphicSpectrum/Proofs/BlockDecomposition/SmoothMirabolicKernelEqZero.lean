import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipMir
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedKernelOfSmallBoxCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedInvariantSmallBoxesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformTwistedInvarianceOnBallStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorFixedBySmallBoxStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicRestrictionUnipotentSmoothStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvertibleMatrixLastLineGivenStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix

namespace GlobalTheory.CompanionTheory.MirFourier

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem eq_zero_of_forall_twKer : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k (m + 1)) V), IsSmooth τ → ∀ v : V, v ∈ twKer τ (MirUin k (m + 1)) 1 → (∀ g : GL (Fin (m + 1)) k, τ (levi k (m + 1) g) v ∈ twKer τ (MirUin k (m + 1)) (mirChar k ψ m)) → v = 0 := by
  intro k _ _ _ _ ψ hψ hψ1 m V _ _ τ hτ v h0 hg
  have hρ : IsSmooth (τ.comp (unipMir k (m + 1))) := GlobalTheory.T.mirabolic_restriction_unipotent_smooth k (m + 1) V τ hτ
  have hall : ∀ a : Fin (m + 1) → k,
      v ∈ twKer (τ.comp (unipMir k (m + 1))) ⊤ (chiOn k ψ a ⊤) := by
    intro a
    by_cases ha : a = 0
    · subst ha
      exact mem_chi_zero ψ τ h0
    · obtain ⟨g, hgr⟩ := GlobalTheory.T.exists_invertible_matrix_last_line_given k m a ha
      have e : (fun j => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j) = a := funext hgr
      have := mem_chi_row ψ τ g (hg g)
      rw [e, ← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one,
        Module.End.one_apply] at this
      exact this
  obtain ⟨N, hN⟩ := GlobalTheory.T.smooth_vector_fixed_by_small_box k (m + 1) V _ hρ v
  obtain ⟨J, hJ⟩ := GlobalTheory.T.uniform_twisted_invariance_on_ball k ψ hψ (m + 1) V _ v (addCharConductor ψ - N)
    (fun a => GlobalTheory.T.twisted_invariant_small_boxes k (m + 1) V _ (chi k ψ a) v (hall a))
  exact GlobalTheory.T.twisted_kernel_of_small_box_character k ψ hψ hψ1 (m + 1) V _ hρ v N (min J N) (min_le_right _ _) hN
    (fun a ha => hJ (min J N) (min_le_left _ _) a ha)

end GlobalTheory.CompanionTheory.MirFourier

end
