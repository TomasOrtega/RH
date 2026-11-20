import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistFrobeniusFiltrationCompat
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTwistFrobeniusFiltrationCompat.lean&line=184#L184)
-/
theorem _root_.GlobalTheory.T.twist_frobenius_filtration_compat : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (σ : Gal(PadicAlgCl l/K)), (∀ x ∈ (tw σ A).Fil0 1, (pdOk_twId σ A).acr0 x ∈ A.Fil0 1) ∧ (∀ x ∈ A.PFil0, A.pdOk_frob.acr0 x ∈ Ideal.span {(l : A.Acr0)}) ∧ (∀ n r, ∀ x ∈ (tw σ A).Fil n r, twAcr σ A n x ∈ A.Fil n r) ∧ (∀ n, Function.Bijective (twAcr σ A n)) ∧ ∀ n x, twAcr σ A n ((tw σ A).phi n x) = A.phi n (twAcr σ A n x) := by
  first | exact @GlobalTheory.CompanionTheory.TwFil.tw_fil | exact GlobalTheory.CompanionTheory.TwFil.tw_fil | (intros; apply GlobalTheory.CompanionTheory.TwFil.tw_fil <;> assumption)
