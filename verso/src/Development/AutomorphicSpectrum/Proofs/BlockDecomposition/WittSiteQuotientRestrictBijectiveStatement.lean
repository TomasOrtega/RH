import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittSiteQuotientRestrictBijective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ResVq
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ZariskiStratumQuotient.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWittSiteQuotientRestrictBijective.lean&line=105#L105)
-/
theorem _root_.GlobalTheory.T.witt_site_quotient_restrict_bijective : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (m : ℕ) (𝒱 : Set X.Opens) (c : WittVector l k), sSup 𝒱 = ⊤ → ∀ j, Function.Bijective ((resVq q ρ m 𝒱 c).pull j) := by
  first | exact @GlobalTheory.CompanionTheory.ZariskiStratumQuotient.main | exact GlobalTheory.CompanionTheory.ZariskiStratumQuotient.main | (intros; apply GlobalTheory.CompanionTheory.ZariskiStratumQuotient.main <;> assumption)
