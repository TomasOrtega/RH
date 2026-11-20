import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittLevelOneGradedFinite
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.FibGr.level_one_gr_finite` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWittLevelOneGradedFinite.lean&line=91#L91)
-/
theorem _root_.GlobalTheory.T.witt_level_one_graded_finite : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q] (ρ : O →+* k) (U : Cov q) (r j : ℕ),
    Module.Finite (Wc.Wm l k 1) (CH.H (sq (sFil (St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ (Set.range U.U)) r) (sFil (St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ (Set.range U.U)) ((r : ℤ) + 1))) j) := by
  first | exact @GlobalTheory.CompanionTheory.FibGr.level_one_gr_finite | exact GlobalTheory.CompanionTheory.FibGr.level_one_gr_finite | (intros; apply GlobalTheory.CompanionTheory.FibGr.level_one_gr_finite <;> assumption)
