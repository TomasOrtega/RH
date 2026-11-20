import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem theorem_one_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.wachTheoremLocal D.loc HW D.locA F Cm := h.1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem consistency_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.consL D.loc HW D.locA F := h.2.1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem proposition_two_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.prop2L D.loc HW D.locA F := h.2.2.1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lemma_three_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.wachLengthLocal D.loc HW D.locA F := h.2.2.2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem first_clause_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.p1L D.loc HW D.locA F := by
  intro l _ K s LL hg
  exact (h.1 l K s LL hg).1

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem second_clause_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.p2L D.loc HW D.locA F := by
  intro l _ K s LL hg
  exact (h.1 l K s LL hg).2.1

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem third_clause_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.p3L D.loc HW D.locA F Cm := by
  intro l _ K s LL hg
  exact (h.1 l K s LL hg).2.2.1

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem fourth_clause_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.p4L D.loc HW D.locA F Cm := by
  intro l _ K s LL hg
  exact (h.1 l K s LL hg).2.2.2.1

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem fifth_clause_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.p5L D.loc HW D.locA F := by
  intro l _ K s LL hg
  exact (h.1 l K s LL hg).2.2.2.2.1

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem sixth_clause_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.p6L D.loc HW D.locA F := by
  intro l _ K s LL hg
  exact (h.1 l K s LL hg).2.2.2.2.2.1

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem seventh_clause_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.p7L D.loc HW D.locA F := by
  intro l _ K s LL hg
  exact (h.1 l K s LL hg).2.2.2.2.2.2.1

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem eighth_clause_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.p8L D.loc HW D.locA F := by
  intro l _ K s LL hg
  exact (h.1 l K s LL hg).2.2.2.2.2.2.2.1

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem delta_invariants_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.p9L D.loc HW D.locA F := by
  intro l _ K s LL hg
  exact (h.1 l K s LL hg).2.2.2.2.2.2.2.2.1

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem tenth_clause_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.p10L D.loc HW D.locA F := by
  intro l _ K s LL hg
  exact (h.1 l K s LL hg).2.2.2.2.2.2.2.2.2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem second_first_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.p2aL D.loc HW D.locA F := by
  intro l _ K s LL hg
  exact (h.2.2.1 l K s LL hg).1

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem second_b_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.p2bL D.loc HW D.locA F := by
  intro l _ K s LL hg
  exact (h.2.2.1 l K s LL hg).2.1

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem second_c_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.p2cL D.loc HW D.locA F := by
  intro l _ K s LL hg
  exact (h.2.2.1 l K s LL hg).2.2.1

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem second_dual_of_local_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : Formalism.MainNotions.DeltaInvariantLattices.p2dL D.loc HW D.locA F := by
  intro l _ K s LL hg
  exact (h.2.2.1 l K s LL hg).2.2.2

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lifting_local_of_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ) (h : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.LiftingTheory.ConclusionL D HW F := h.1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wach_of_lifting_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ) (h : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.LiftingTheory.ConclusionW D HW F := h.2.1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lift_of_lifting_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ) (h : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.LiftingTheory.LiftTheoremAllCases D HW F CA CB CK := h.2.2.2.2.2.2.2

end Formalism.MainNotions.N
