import Formalism.SharpRestriction.GlobalSchurBounds.LinkMin
import Formalism.SharpRestriction.GlobalSchurBounds.IntegralityOfRationalityLocal
import Formalism.LocalToGlobal.GlobalTheory.GL6.RamifiedLatticeOfRankSlopeLength
import Formalism.LocalToGlobal.GlobalTheory.GL6.SecondBranchInclLengthOfLengths

noncomputable section

namespace Formalism.MainNotions.RT

open Formalism.BasicNotions Classical

def ConcreteFormsLevelZero (D : D7) (u : D.what₂.Word) : Prop := FormsTwistCompatibilityFamily D u ∧ product_first_zeroth_parts.admS D u

def FreeTT (D : D7) (u : D.what₂.Word) : Prop := ConcreteFormsLevelZero D u → Nonempty (product_first_zeroth_parts.FreeT D u)

def SlopeLineT (D : D7) (u : D.what₂.Word) : Prop := product_first_zeroth_parts.HidaSetting D u → ConcreteFormsLevelZero D u → product_first_zeroth_parts.SlopeLine D u

def SecondBranchIntegralityUnderForms (D : D7) (u : D.what₂.Word) : Prop :=
  product_first_zeroth_parts.HidaSetting D u → ConcreteFormsLevelZero D u → Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.SecondBranchInclusionLength D u

/- English proof (translation)
Equip the data with the indicated structure. Equip the data with the indicated structure. Equip the data with the indicated structure. Introduce a local definition for the expression. Apply function extensionality and compare values at an arbitrary argument.

Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Equip the data with the indicated structure. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Treat this case separately.

Treat this case separately. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Establish an intermediate fact. Treat this case separately. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem freeT_of_model {D : D7} {u : D.what₂.Word} (M : Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.FreeRankModel (D.mem u).A) :
    Nonempty (product_first_zeroth_parts.FreeT D u) := by
  letI := M.grp
  letI := M.finX
  letI := M.act
  let ph : (∀ v : (D.mem u).A.vT, ((D.mem u).A.Fv v)ˣ) →* ((D.mem u).A.vT → M.H) :=
    { toFun := fun g v => M.e v (g v)
      map_one' := by
        funext v
        exact (M.e v).map_one
      map_mul' := by
        intro g h
        funext v
        exact (M.e v).map_mul (g v) (h v) }
  letI : MulAction (∀ v : (D.mem u).A.vT, ((D.mem u).A.Fv v)ˣ) M.X := MulAction.compHom M.X ph
  have hsingle : ∀ v (a : ((D.mem u).A.Fv v)ˣ), ph (Pi.mulSingle v a) = (Pi.mulSingle v (M.e v a) : (D.mem u).A.vT → M.H) := by
    intro v a
    funext w
    by_cases hw : w = v
    · subst hw
      show M.e w ((Pi.mulSingle w a : (∀ v : (D.mem u).A.vT, ((D.mem u).A.Fv v)ˣ)) w) = (Pi.mulSingle w (M.e w a) : (D.mem u).A.vT → M.H) w
      simp only [Pi.mulSingle_eq_same]
    · show M.e w ((Pi.mulSingle v a : (∀ v : (D.mem u).A.vT, ((D.mem u).A.Fv v)ˣ)) w) = (Pi.mulSingle v (M.e v a) : (D.mem u).A.vT → M.H) w
      first
      | simp [Pi.mulSingle_eq_of_ne hw]
      | (simp only [Pi.mulSingle_eq_of_ne hw]; exact (M.e w).map_one)
  refine ⟨{ X := M.X, Θ := M.E, free := ?_, equiv := ?_ }⟩
  · intro g x hx
    have h1 : ph g = 1 := M.free (ph g) x hx
    funext v
    have h2 : M.e v (g v) = 1 := congrFun h1 v
    first
    | exact (M.e v).map_eq_one_iff.mp h2
    | exact (MulEquiv.map_eq_one_iff (M.e v)).mp h2
  · intro v a φ h x
    rw [M.intertw v a φ h x]
    show M.E φ ((Pi.mulSingle v (M.e v a) : (D.mem u).A.vT → M.H) • x) = M.E φ (ph (Pi.mulSingle v a) • x)
    rw [hsingle]

/- English proof (translation)
Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem free_structure_under_forms (D : D7) (u : D.what₂.Word) : Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.FormsCompatible D u ∧ product_first_zeroth_parts.admS D u → Nonempty (product_first_zeroth_parts.FreeT D u) := by
  rintro ⟨⟨Tf, -⟩, hA⟩
  obtain ⟨M⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.free_rank_model_of_split Tf hA (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.splitAtT_of_tied Tf.atT)
  exact freeT_of_model M

/- English proof (translation)
Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem slope_line_under_forms (D : D7) (u : D.what₂.Word) :
    product_first_zeroth_parts.HidaSetting D u → Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.FormsCompatible D u ∧ product_first_zeroth_parts.admS D u → product_first_zeroth_parts.SlopeLine D u := by
  rintro hS ⟨⟨Tf, hC⟩, hA⟩
  exact Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.slope_formula_of_character_finite hS Tf hC hA

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem lemma_B_second_branch_of_length (D : D7) (u : D.what₂.Word) (hT : Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.FormsCompatible D u ∧ product_first_zeroth_parts.admS D u)
    (h : Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.SeenPlaceLatticeLengthFormula D u) : Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.SecondBranchInclusionLength D u := by
  obtain ⟨T, -⟩ := hT.1
  exact Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.second_branch_incl_length_of_second T h

variable {eps : ℝ}

/- English proof (translation)
Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem slope_free_branch_family (Fm : FamP eps) (tT : FamU Fm ConcreteFormsLevelZero) (hWT : ∀ (D : D7) (u : D.what₂.Word), FreeTT D u)
    (hμT : ∀ (D : D7) (u : D.what₂.Word), SlopeLineT D u) (hBT : ∀ (D : D7) (u : D.what₂.Word), SecondBranchIntegralityUnderForms D u) :
    FamU Fm (fun D u => Nonempty (product_first_zeroth_parts.FreeT D u)) ∧ FamU Fm product_first_zeroth_parts.SlopeLine ∧ FamU Fm Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.SecondBranchInclusionLength := by
  unfold FamU at tT ⊢
  obtain ⟨x0, hx⟩ := tT
  exact ⟨⟨x0, fun x h0 h1 i u hS => hWT _ u (hx x h0 h1 i u hS)⟩,
    ⟨x0, fun x h0 h1 i u hS => hμT _ u hS (hx x h0 h1 i u hS)⟩,
    ⟨x0, fun x h0 h1 i u hS => hBT _ u hS (hx x h0 h1 i u hS)⟩⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem linkGLOBAL7_tied6b (Fm : FamP eps) (Cabs CH C0 C5 : ℝ) (hCabs : 0 ≤ Cabs) (hCH : 0 < CH) (hC0 : 3 ≤ C0)
    (h2b : flipTwoThree.fam0 Fm StandardLattice.MassRatio₂) (h2v : flipTwoThree.fam0 Fm StandardLattice.BaseVolumeEqualsMass) (h3 : flipTwoThree.fam0 Fm StandardLattice.SigmaDegreeTwoSidedBoundOfGap)
    (hZa : flipTwoThree.FamilySlopeLowerOpenPart Fm) (hZb : flipTwoThree.FamilySlopeMaxOpenPart Fm C5)
    (tCV : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u))

    (tT : FamU Fm ConcreteFormsLevelZero) (hWT : ∀ (D : D7) (u : D.what₂.Word), FreeTT D u)
    (hμT : ∀ (D : D7) (u : D.what₂.Word), SlopeLineT D u) (hBT : ∀ (D : D7) (u : D.what₂.Word), SecondBranchIntegralityUnderForms D u)
    (hI : FamU Fm Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.HeckeIntegralLevelZero) (hR : FamU Fm Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.HeckeRamifiedLevelZero) :
    TuSize Fm → LinkGLOBAL7 Fm Cabs CH C0 Cabs 0 := by
  obtain ⟨hW, hμ, hB⟩ := slope_free_branch_family Fm tT hWT hμT hBT
  first
  | (apply linkGLOBAL7_min <;> assumption)
  | (apply Formalism.MainNotions.Lnk.linkGLOBAL7_min <;> assumption)
  | (apply Formalism.MainNotions.GlobalTheoryTheory.linkGLOBAL7_min <;> assumption)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem linkGLOBAL7_tied6 (Fm : FamP eps) (Cabs CH C0 C5 : ℝ) (hCabs : 0 ≤ Cabs) (hCH : 0 < CH) (hC0 : 3 ≤ C0)
    (h2b : flipTwoThree.fam0 Fm StandardLattice.MassRatio₂) (h2v : flipTwoThree.fam0 Fm StandardLattice.BaseVolumeEqualsMass) (h3 : flipTwoThree.fam0 Fm StandardLattice.SigmaDegreeTwoSidedBoundOfGap)
    (hZa : flipTwoThree.FamilySlopeLowerOpenPart Fm) (hZb : flipTwoThree.FamilySlopeMaxOpenPart Fm C5)
    (tCV : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u))

    (tT : FamU Fm ConcreteFormsLevelZero)

    (hWT : ∀ (D : D7) (u : D.what₂.Word), FreeTT D u) (hμT : ∀ (D : D7) (u : D.what₂.Word), SlopeLineT D u)
    (hBT : ∀ (D : D7) (u : D.what₂.Word), SecondBranchIntegralityUnderForms D u) (hIT : ∀ (D : D7) (u : D.what₂.Word), IntegralityLevelZeroUnderForms D u)
    (hFT : ∀ (D : D7) (u : D.what₂.Word), FiSt0T D u) (hXT : ∀ (D : D7) (u : D.what₂.Word), CrossDia0T D u)
    (hUT : ∀ (D : D7) (u : D.what₂.Word), UnfAll0T D u) :
    TuSize Fm → LinkGLOBAL7 Fm Cabs CH C0 Cabs 0 :=
  linkGLOBAL7_tied6b Fm Cabs CH C0 C5 hCabs hCH hC0 h2b h2v h3 hZa hZb tCV tT hWT hμT hBT
    (hI_tied Fm tT hIT) (hR_tied Fm tT hFT hXT hUT)

end Formalism.MainNotions.RT

end
