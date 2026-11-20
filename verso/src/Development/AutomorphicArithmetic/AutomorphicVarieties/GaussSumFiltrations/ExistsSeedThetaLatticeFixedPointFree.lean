import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ThetaTranslateIntegralCongruentOneModPrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsEvenPositiveDefiniteIntMatrixDetSq
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ThetaSlashEighthRootOfSquareDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ThetaSeriesHolomorphicQExpansionOfBoundedCoeff
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Assume the negation of the conclusion and derive a contradiction. Supply the required witnesses or components. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions.

Apply the first step, then apply the next step to every resulting obligation. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem seed_exists : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ : F, IsDel p δ → ∃ θ : Hn F → ℂ, Seed ι δ θ := by
  intro F _ _ _ p hp ι hp2 δ hδ
  obtain ⟨G, S, t, hL⟩ := GlobalTheory.T.exists_evenPositiveDefinite_intMatrix_det_sq p hp.out hp2
  have hsupp : ∀ x : (Fin (p - 1) ⊕ Fin (p - 1)) → F, (oneL x : ℂ) ≠ 0 → x ∈ aL (Fin (p - 1) ⊕ Fin (p - 1)) (1 : F) := by
    intro x hx
    have hx' : x ∈ LL F (Fin (p - 1) ⊕ Fin (p - 1)) := by
      by_contra h
      exact hx (by simp [oneL, h])
    exact ⟨x, hx', by simp⟩
  have hbd : ∀ x : (Fin (p - 1) ⊕ Fin (p - 1)) → F, ‖(oneL x : ℂ)‖ ≤ 1 := by
    intro x
    unfold oneL
    split_ifs <;> simp
  obtain ⟨-, hhol, hgr, -⟩ := GlobalTheory.T.thetaSeries_holomorphic_qExpansion_of_bounded_coeff F _ G hL.pos (1 : F) oneL 1 hsupp hbd
  obtain ⟨N, hN, hlev⟩ := GlobalTheory.T.theta_slash_eighth_root_of_square_det F _ G hL.pos t hL.det (p - 1) hL.card
  exact ⟨th G oneL, hhol, hgr, fun γ hγ => GlobalTheory.T.theta_translate_integral_congruent_one_mod_prime F p ι hp2 δ hδ _ G S t hL γ hγ, N, hN, hlev⟩

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.exists_seed_theta_lattice_fixedPointFree : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ : F, IsDel p δ → ∃ θ : Hn F → ℂ, Seed ι δ θ := by
  first | exact @GlobalTheory.HilbertThetaSeries.seed_exists | exact GlobalTheory.HilbertThetaSeries.seed_exists | (intros; apply GlobalTheory.HilbertThetaSeries.seed_exists <;> assumption)
