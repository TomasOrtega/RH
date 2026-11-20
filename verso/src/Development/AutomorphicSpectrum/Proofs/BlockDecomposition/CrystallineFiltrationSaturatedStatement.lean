import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineFiltrationSaturated
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCrystallineFiltrationSaturated.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.crystalline_filtration_saturated : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ) (z : A.Acr0), (l : A.Acr0) * z ∈ A.Fil0 r → z ∈ A.Fil0 r := by
  first | exact @GlobalTheory.CompanionTheory.PerfFil.crystalline_filtration_l_saturated | exact GlobalTheory.CompanionTheory.PerfFil.crystalline_filtration_l_saturated | (intros; apply GlobalTheory.CompanionTheory.PerfFil.crystalline_filtration_l_saturated <;> assumption)
