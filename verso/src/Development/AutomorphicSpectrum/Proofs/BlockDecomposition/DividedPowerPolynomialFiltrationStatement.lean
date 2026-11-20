import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerPolynomialFiltration
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.PDFil.fil_pdPoly` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FDividedPowerPolynomialFiltration.lean&line=208#L208)
-/
theorem _root_.GlobalTheory.T.divided_power_polynomial_filtration : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J)), Q.IsStd δ η → (∀ a c, fil δ a * fil δ c ≤ fil δ (a + c)) ∧ (∀ a c, a ≤ c → fil δ c ≤ fil δ a) ∧ fil δ 0 = ⊤ ∧ ∀ (r : ℕ) (z : Q.P), z ∈ fil η r ↔ ∀ k, Q.e.repr z k ∈ fil δ (r - k) := by
  first | exact @GlobalTheory.CompanionTheory.PDFil.fil_pdPoly | exact GlobalTheory.CompanionTheory.PDFil.fil_pdPoly | (intros; apply GlobalTheory.CompanionTheory.PDFil.fil_pdPoly <;> assumption)
