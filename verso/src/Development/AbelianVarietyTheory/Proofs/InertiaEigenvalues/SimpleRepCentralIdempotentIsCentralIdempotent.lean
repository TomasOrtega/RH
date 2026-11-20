import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Formalism.PadicSubsetSums.CentralIdempotents.HCDisjointO
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoBlockEqZeroIff
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CharIdem
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerOSys
open Polynomial CategoryTheory

namespace GlobalTheory.SerOSys

/- English proof (translation)
Replace the relevant objects with their definitions. Both sides reduce to the same expression.
-/
theorem zIdem_eq_charIdem {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) :
    zIdem τ = PI.CharIdem.charIdem τ := by
  unfold zIdem PI.CharIdem.charIdem
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem zIdem_centralIdempotent : ∀ {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ), Simple τ →
    zIdem τ * zIdem τ = zIdem τ ∧ ∀ a, zIdem τ * a = a * zIdem τ := by
  intro Γ _ _ τ hτ
  have h := orthogonalCentral Γ τ τ hτ hτ
  rw [zIdem_eq_charIdem]
  exact ⟨h.2.2.1, h.2.2.2.1⟩

end GlobalTheory.SerOSys
