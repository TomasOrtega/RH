import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthWittCohomology
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LevelOne.finiteLength_level_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFiniteLengthWittCohomology.lean&line=102#L102)
-/
theorem _root_.GlobalTheory.T.finite_length_witt_cohomology : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (j : ℕ),
    Module.Finite (Wc.Wm l k 1) (HO (St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ {⊤}) j) →
    IsFiniteLength (WittVector l k) (CH.H (Wc.OM l (B.schFn q) ρ 1) j) := by
  first | exact @GlobalTheory.CompanionTheory.LevelOne.finiteLength_level_one | exact GlobalTheory.CompanionTheory.LevelOne.finiteLength_level_one | (intros; apply GlobalTheory.CompanionTheory.LevelOne.finiteLength_level_one <;> assumption)
