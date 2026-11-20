import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialFormsBasis
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMonomialFormsBasis.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.monomial_forms_basis : ∀ {K : Type} [Field K] {n d : ℕ} (a : ℕ), ∃ b : Module.Basis (Gam n d × {D : Finset (E n d) // D.card = a}) K (Om K (Lr K n d) a), ∀ p, b p = monW K p.1 p.2 := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.BasisW.monW_basis | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.BasisW.monW_basis | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.BasisW.monW_basis <;> assumption)
