import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFunctionsPerfectAdicRing
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ContFn.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FContinuousFunctionsPerfectAdicRing.lean&line=110#L110)
-/
theorem _root_.GlobalTheory.T.continuous_functions_perfect_adic_ring : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (Γ : Type) [TopologicalSpace Γ], PerfectRing (A.contR Γ) l ∧ IsAdicComplete (Ideal.span {A.contC Γ A.pi}) (A.contR Γ) ∧ A.contC Γ A.pi ∈ nonZeroDivisors (A.contR Γ) ∧ ∀ (k : ℕ) (f : A.contR Γ), f ∈ Ideal.span {A.contC Γ A.pi ^ k} ↔ ∀ γ, f.1 γ ∈ Ideal.span {A.pi ^ k} := by
  first | exact @GlobalTheory.CompanionTheory.ContFn.main | exact GlobalTheory.CompanionTheory.ContFn.main | (intros; apply GlobalTheory.CompanionTheory.ContFn.main <;> assumption)
