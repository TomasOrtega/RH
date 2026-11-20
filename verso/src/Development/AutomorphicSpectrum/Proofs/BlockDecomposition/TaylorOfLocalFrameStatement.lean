import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TaylorOfLocalFrame
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ConeLocal.taylor_loc` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTaylorOfLocalFrame.lean&line=91#L91)
-/
theorem _root_.GlobalTheory.T.taylor_of_local_frame : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {d : ℕ} (c : Coord q W d) (s : ℕ) (E : Frame (sP (KS q s {W})) d)
    (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D), IsLoc q s c.t E ε →
    letI := (strV q W).toAlgebra
    ∀ (D : Fin d → Derivation K Γ(X, W) Γ(X, W)), (∀ k j, D k (c.t j) = if k = j then 1 else 0) →
    Taylor (sFil (KS q s {W})) E (fun k x => ε (D k (ε.symm x))) := by
  first | exact @GlobalTheory.CompanionTheory.ConeLocal.taylor_loc | exact GlobalTheory.CompanionTheory.ConeLocal.taylor_loc | (intros; apply GlobalTheory.CompanionTheory.ConeLocal.taylor_loc <;> assumption)
