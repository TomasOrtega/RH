import Formalism.SharpRestriction.GrowthBounds.AdmissibleIntegers.StatementsOfRemainingBound
import Formalism.SharpRestriction.GrowthBounds.AdmissibleIntegers.RemainingPrimesOfAdmitted
import Formalism.SharpRestriction.GrowthBounds.AdmissibleIntegers.FirstTermSizeBound

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions Formalism.MainNotions.WeilJacquetShalikaLaw

namespace Formalism.MainNotions.WeilJacquetShalikaLaw.Proof

/- English proof (translation)
Introduce `_ _ _ _ hI hD` and use `remaining_primes_of_admitted hI hD`.
-/
theorem restComp_proved : RestComp := fun _ _ _ _ hI hD => remaining_primes_of_admitted hI hD

/- English proof (translation)
Introduce `D L` and use `first_term_size_bound D L`.
-/
theorem restSz_proved : RestSz 12 := fun D L => first_term_size_bound D L

/- English proof (translation)
The claim follows from `stmt_of_rest restComp_proved D L X Y K c Dx`.
-/
theorem stmt_proved (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D) (Dx : DivX D) :
    Stmt D L X Y K c Dx := stmt_of_rest restComp_proved D L X Y K c Dx

/- English proof (translation)
The claim follows from `stmtE_of_rest restComp_proved (by norm_num) restSz_proved D L X Y K c Dx`.
-/
theorem stmtE_proved (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D) (Dx : DivX D) :
    ClosedFormOfAdmitted D L X Y K c Dx := stmtE_of_rest restComp_proved (by norm_num) restSz_proved D L X Y K c Dx

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, fun _ _ _ _ => stmt_proved _ _ _ _ _ _ _⟩`.
-/
theorem stmtF_proved {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : KudlaFamilyStatement Fm :=
  ⟨0, fun _ _ _ _ => stmt_proved _ _ _ _ _ _ _⟩

/- English proof (translation)
The claim follows from `stmtEF_of_rest restComp_proved (by norm_num) restSz_proved Fm`.
-/
theorem stmtEF_proved {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : FamilyClosedForm Fm :=
  stmtEF_of_rest restComp_proved (by norm_num) restSz_proved Fm

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => stmtEF_proved Fm⟩⟩`.
-/
theorem stmtClosed_proved (𝒞 : Formalism.MainNotions.FamClass) : ClosedAbsoluteShare 𝒞 :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => stmtEF_proved Fm⟩⟩

end Formalism.MainNotions.WeilJacquetShalikaLaw.Proof

end
