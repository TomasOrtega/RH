import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousAlgebraUniversalProperty
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FContinuousAlgebraUniversalProperty.lean&line=236#L236)
-/
theorem _root_.GlobalTheory.T.continuous_algebra_universal_property : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l), ∃ η : (((base l).cont ℤ_[l]).A)ˣ, ((base l).cont ℤ_[l]).sharp η = 1 ∧ PAlg.Hom.f (contShift (base l)) η = ((base l).cont ℤ_[l]).s (ε.e 0) * η ∧ ∀ (A t : PAlg l), t.IsTest → ∀ (φ : A ⟶ t) (u : (t.A)ˣ), t.sharp u = 1 → ∃! ψ : A.cont ℤ_[l] ⟶ t, A.toCont ℤ_[l] ≫ ψ = φ ∧ PAlg.Hom.f ψ (PAlg.Hom.f (contMap A.fromBase ℤ_[l]) η) = u := by
  first | exact @GlobalTheory.CompanionTheory.ContUniv.main | exact GlobalTheory.CompanionTheory.ContUniv.main | (intros; apply GlobalTheory.CompanionTheory.ContUniv.main <;> assumption)
