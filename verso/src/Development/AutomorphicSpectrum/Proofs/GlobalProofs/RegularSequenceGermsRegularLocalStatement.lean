import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RegularSequenceGermsRegularLocal
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ResKCoords.stalk_to_localization` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FRegularSequenceGermsRegularLocal.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.regular_sequence_germs_regular_local : ∀ (Y : Scheme.{0}) (U : Y.affineOpens) (y : Y) (hy : y ∈ U.1), IsRegularLocalRing (Y.presheaf.stalk y) → ∀ (m : ℕ) (f : Fin m → Γ(Y, U.1)), FinalTheorems.Rsp (Y.presheaf.stalk y) m (fun i => Y.presheaf.germ U.1 y hy (f i)) → IsRegularLocalRing (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal) ∧ FinalTheorems.Rsp (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal) m (fun i => algebraMap Γ(Y, U.1) _ (f i)) ∧ ∀ s : Γ(Y, U.1), y ∈ Y.basicOpen s ↔ s ∉ (U.2.primeIdealOf ⟨y, hy⟩).asIdeal := by
  first | exact @GlobalTheory.CompanionTheory.ResKCoords.stalk_to_localization | exact GlobalTheory.CompanionTheory.ResKCoords.stalk_to_localization | (intros; apply GlobalTheory.CompanionTheory.ResKCoords.stalk_to_localization <;> assumption)
