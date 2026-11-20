import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrameUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClassicalLiftOfSmooth
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Introduce `p _ B G _ hG y n hn t ht`. Use `hG.comm` as an intermediate fact. Use `hG.smooth` as an intermediate fact. Use `GrpTangent.etale_torsion G hn` as an intermediate fact. Establish `hP` using `GrpTangent.isPullback_torsion G n`.

Establish `e : ∀ {T : Scheme.{0}} (q : T ⟶ B), (1 : Over.mk q ⟶ G).left = q ≫ η[G].left`. Introduce `T q`. Rewrite using `[Hom.one_def, Over.comp_left]`. Both sides reduce to the same expression. Establish `w : t.left ≫ (mulN G n).left = (spMap (IsLocalRing.residue (OO p)) ≫ y) ≫ η[G].left`.

Rewrite using `[← Over.comp_left, GrpTangent.comp_mulN, ht, e]`. Take `⟨c, hc₁, hc₂⟩` from `ZJ.exists_classical_lift_of_smooth p _ _ (torsion G n).hom y (hP.lift _ _ w) (hP.lift_snd _ _ w)`. Set `b : Over.mk y ⟶ G` to `Over.homMk (c ≫ (torsion.ι G n).left) (by`. Rewrite using `[Category.assoc, Over.w]`. Conclude with `hc₁)`.

Use `⟨b, ?_, ?_⟩` and prove the remaining obligations. Use `Over.OverMorphism.ext ?_` and prove the remaining obligations. Rewrite using `[← GrpTangent.comp_mulN, Over.comp_left, e]`. Express the relevant statement in the definitionally equal form `(c ≫ (torsion.ι G n).left) ≫ _ = _`. Rewrite using `[Category.assoc, hP.w, ← Category.assoc, hc₁]`.

Express the relevant statement in the definitionally equal form `_ ≫ c ≫ (torsion.ι G n).left = _`. Rewrite using `[← Category.assoc]`. Conclude with `(congrArg (· ≫ (torsion.ι G n).left) hc₂).trans (hP.lift_fst _ _ w)`.
-/
theorem ZJ.exists_torsion_lift_of_residue :
    ∀ (p : ℕ) [Fact p.Prime] (B : Scheme.{0}) (G : Over B) [GrpObj G], IsSemiAbelian G → ∀ (y : Sp (OO p) ⟶ B) (n : ℕ), IsUnit (n : Γ(B, ⊤)) → ∀ t : Over.mk (spMap (IsLocalRing.residue (OO p)) ≫ y) ⟶ G, t ^ n = 1 → ∃ b : Over.mk y ⟶ G, b ^ n = 1 ∧ spMap (IsLocalRing.residue (OO p)) ≫ b.left = t.left := by
  intro p _ B G _ hG y n hn t ht
  have := hG.comm
  have := hG.smooth
  have := GrpTangent.etale_torsion G hn
  have hP := GrpTangent.isPullback_torsion G n
  have e : ∀ {T : Scheme.{0}} (q : T ⟶ B), (1 : Over.mk q ⟶ G).left = q ≫ η[G].left := by
    intro T q
    rw [Hom.one_def, Over.comp_left]; rfl
  have w : t.left ≫ (mulN G n).left =
      (spMap (IsLocalRing.residue (OO p)) ≫ y) ≫ η[G].left := by
    rw [← Over.comp_left, GrpTangent.comp_mulN, ht, e]
  obtain ⟨c, hc₁, hc₂⟩ := ZJ.exists_classical_lift_of_smooth p _ _ (torsion G n).hom y
    (hP.lift _ _ w) (hP.lift_snd _ _ w)
  let b : Over.mk y ⟶ G := Over.homMk (c ≫ (torsion.ι G n).left) (by
    rw [Category.assoc, Over.w]; exact hc₁)
  refine ⟨b, ?_, ?_⟩
  · refine Over.OverMorphism.ext ?_
    rw [← GrpTangent.comp_mulN, Over.comp_left, e]
    change (c ≫ (torsion.ι G n).left) ≫ _ = _
    rw [Category.assoc, hP.w, ← Category.assoc, hc₁]
  · change _ ≫ c ≫ (torsion.ι G n).left = _
    rw [← Category.assoc]
    exact (congrArg (· ≫ (torsion.ι G n).left) hc₂).trans (hP.lift_fst _ _ w)

end GlobalTheory
