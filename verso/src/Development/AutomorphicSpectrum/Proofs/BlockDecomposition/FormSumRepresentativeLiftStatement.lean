import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormSumRepresentativeLift
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ConeLocal.rep_collapse` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFormSumRepresentativeLift.lean&line=105#L105)
-/
theorem _root_.GlobalTheory.T.form_sum_representative_lift : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} {d : ℕ} (hF : IsFil Φ Fil) (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil)
    (m : ℕ) (r : ℤ), r = m → ∀ {ι : Type} [Fintype ι] (J : ι → Fin m → Fin d) (w : ι → Φ.A.obj E.D) (x : CH.H (gr Fil r) m),
      CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (fun u => ∑ i, E.form σ (J i) (w i) u) x →
      CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (fun u => ∑ I : Idx m d, E.form σ I.1 (∑ i, sgn I (J i) • w i) u) x := by
  first | exact @GlobalTheory.CompanionTheory.ConeLocal.rep_collapse | exact GlobalTheory.CompanionTheory.ConeLocal.rep_collapse | (intros; apply GlobalTheory.CompanionTheory.ConeLocal.rep_collapse <;> assumption)
