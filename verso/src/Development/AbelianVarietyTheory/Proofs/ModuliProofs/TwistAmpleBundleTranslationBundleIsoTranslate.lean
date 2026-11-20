import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionDivision
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRigidifiedTwist
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPolarisationFormOfLineBundleStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteAndSurjectiveOfFormIsStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.TwistIsTranslate

open CechPic

variable {K : Type} [Field K]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Rewrite the conclusion using the stated equalities.
-/
theorem pull_const {A T : Over (Sp K)} (x : 𝟙_ (Over (Sp K)) ⟶ A) (c : CechPic.Pic A.left) :
    CechPic.pull (toUnit T ≫ x).left c = 0 := by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  have hx : CechPic.pull x.left (cls L hL) = 0 := by
    have hc := hL.cover
    let z₀ : (𝟙_ (Over (Sp K))).left := (default : PrimeSpectrum K)
    have hz : x.left z₀ ∈ (⨆ i, L.U i) := by rw [hc]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    refine GlobalTheory.RigidifyTwist.pull_cls_eq_zero hL x.left i fun z => ?_
    rwa [show z = z₀ from Subsingleton.elim (α := PrimeSpectrum K) _ _]
  rw [Over.comp_left, pull_comp, hx, map_zero]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Simplify to obtain the desired conclusion from the available facts. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_comp_eq [IsAlgClosed K] {A B : Over (Sp K)} (s : A ⟶ B) [IsFinite s.left] [Surjective s.left]
    (y : 𝟙_ (Over (Sp K)) ⟶ B) : ∃ x : 𝟙_ (Over (Sp K)) ⟶ A, x ≫ s = y := by
  obtain ⟨t, ht⟩ := ReciprocityTheory.ChartRestriction.G.H1.SectionDivision.exists_section (k := K) (pullback.snd s.left y.left)
  have h1 := Over.w s
  have h2 := Over.w y
  refine ⟨Over.homMk (t ≫ pullback.fst s.left y.left) ?_, ?_⟩
  · simp only [Category.assoc, ← h1, pullback.condition_assoc, h2]
    simpa using ht
  · ext
    simp only [Over.comp_left, Over.homMk_left, Category.assoc, pullback.condition]
    rw [← Category.assoc, ht]
    exact Category.id_comp _

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws.
-/
theorem lam_id_const {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] (x : 𝟙_ (Over (Sp K)) ⟶ A)
    (c : CechPic.Pic A.left) :
    lam c (𝟙 A) (toUnit A ≫ x) = CechPic.pull ((toUnit A ≫ x) * 𝟙 A).left c - c := by
  have h1 : (1 : A ⟶ A) = toUnit A ≫ (1 : 𝟙_ (Over (Sp K)) ⟶ A) := by simp
  have hc : (𝟙 A) * (toUnit A ≫ x) = (toUnit A ≫ x) * 𝟙 A := mul_comm _ _
  simp only [lam, hc, Over.id_left, pull_id, pull_const, h1]
  abel

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.
-/
theorem iso_of_formIs (P : Out.PolAV (Sp K)) (M : LB P.A.left) (hM : M.IsLB) (s : P.A ⟶ P.A) (hs : FormIs P M s)
    (x : 𝟙_ (Over (Sp K)) ⟶ P.A) :
    LBIso (LB.div M (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, ((toUnit P.A ≫ x ≫ s) * 𝟙 P.A).left] ![1, -1]))
      (M.pull ((toUnit P.A ≫ x) * 𝟙 P.A).left) := by
  obtain ⟨-, hiso⟩ := hs
  have hL : P.L.IsLB := P.isLB
  have hc1 : (cubeLB P.A ![fst P.A P.A, snd P.A P.A] M).IsLB := LB.isLB_linComb hM _ _
  have hc2 : (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ s] P.L).IsLB := LB.isLB_linComb hL _ _
  have hLam : abelian₂ P.A M = cubeLB P.A ![fst P.A P.A, snd P.A P.A] M := rfl
  rw [hLam] at hiso
  have e := (cls_eq_iff hc1 hc2).2 hiso
  rw [cls_cube_two hM _ _ hc1, cls_cube_two hL _ _ hc2] at e
  have e2 := congrArg (CechPic.pull (lift (𝟙 P.A) (toUnit P.A ≫ x)).left) e
  rw [pull_lam, pull_lam] at e2
  simp only [lift_fst, lift_snd_assoc, lift_snd] at e2
  rw [lam_id_const, Category.assoc, lam_id_const] at e2
  have hd := LB.isLB_div hM (LB.isLB_linComb hL (K := Fin 2)
    ![𝟙 P.A.left, ((toUnit P.A ≫ x ≫ s) * 𝟙 P.A).left] ![1, -1])
  refine (cls_eq_iff hd (pull_isLB hM _)).1 ?_
  rw [cls_div hM (LB.isLB_linComb hL _ _), cls_linComb hL, cls_pull hM]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, pull_id, one_smul,
    neg_smul]
  rw [sub_eq_iff_eq_add] at e2
  rw [e2]
  abel

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem twist_iso_translate : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (y : 𝟙_ (Over (Sp K)) ⟶ P.A), M.IsLB → Out.RelAmple P.A M → ∃ x : 𝟙_ (Over (Sp K)) ⟶ P.A, LBIso (LB.div M (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, ((toUnit P.A ≫ y) * 𝟙 P.A).left] ![1, -1])) (M.pull ((toUnit P.A ≫ x) * 𝟙 P.A).left) := by
  intro hA hB K _ _ P M y hM hAmp
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_polarisationForm_of_lineBundle hA hB K P M hM
  obtain ⟨hfin, hsurj⟩ := GlobalTheory.T.isFinite_and_surjective_of_formIs' hA hB K P M s hM hAmp hs
  obtain ⟨x, hx⟩ := exists_comp_eq s y
  refine ⟨x, ?_⟩
  have h := iso_of_formIs P M hM s hs x
  rwa [hx] at h

end GlobalTheory.TwistIsTranslate
