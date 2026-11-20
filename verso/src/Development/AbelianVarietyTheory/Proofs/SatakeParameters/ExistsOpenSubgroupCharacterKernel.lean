import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
namespace GlobalTheory.Cong.LevelExt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
-/
theorem mem_locU_iff {w : HeightOneSpectrum (𝓞 E)} (x : UA E n) :
    x ∈ locU n w ↔ x ∈ finU E n ∧ ∀ u, Apart u w → cLoc u x = 1 := by
  unfold locU Apart
  simp only [Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker]

/- English proof (translation)
Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem cLoc_conj_eq_one {w : HeightOneSpectrum (𝓞 E)} (x : UA E n) (h1 : cLoc w x = 1) :
    cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x = 1 := by
  have hw1 : ∀ v, v = w → cLoc v x = 1 := by
    rintro v rfl
    exact h1
  have hce := GlobalTheory.SplitPts.comp_eq x (conjSrc (GlobalTheory.SplitPts.conjE E) w)
  rw [hw1 _ (GlobalTheory.SplitPts.conjSrc_conjSrc_cm w), Units.val_one, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.transpose_one, Matrix.one_mul] at hce
  exact Units.ext hce

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem one_of_cLoc {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) (x : UA E n) (h1 : cLoc w x = 1) :
    ∀ u, ¬ Apart u w → cLoc u x = 1 := by
  intro u hu
  have hu' : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) := by
    by_contra h
    exact hu h
  rcases (GlobalTheory.SplitPts.over_split hw).2.2 u hu' with rfl | rfl
  · exact h1
  · exact cLoc_conj_eq_one x h1

end GlobalTheory.Cong.LevelExt
