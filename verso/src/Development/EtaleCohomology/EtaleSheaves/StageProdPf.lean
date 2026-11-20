import Development.EtaleCohomology.EtaleSheaves.PartDiagCut

noncomputable section
open GlobalTheory.EtC

namespace LateralTheory.E.StageProdPf
open LateralTheory.E.PartDiagCut

/- English proof (translation)
Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem zero_not_mem_S {B : Type} [CommRing B] (I : Ideal B) (P : LateralTheory.E.PartDiagCut.Part (B ⧸ I)) (e : P.1) :
    (0 : B) ∉ S I e.1 := by
  rintro ⟨t, ht⟩
  simp only [map_zero, zero_mul] at ht
  exact (P.idem e.1 e.2).2 ht.symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Supply the required witnesses or components.
-/
theorem StageProd_of (hloc : LateralTheory.E.HensCut.LocAIC) : LateralTheory.E.PartDiagCut.StageProd := by
  intro q B _ _ I hB hq P
  let R : Fin P.1.card → Type := fun k => Localization (S I (P.1.equivFin.symm k).1)
  refine ⟨P.1.card, R, fun k => inferInstance, fun k => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hloc B (S I (P.1.equivFin.symm k).1) (zero_not_mem_S I P _) hB
    refine ⟨h1, h2, ?_⟩
    have := hq.map (algebraMap B (R k))
    rwa [map_natCast] at this
  · exact ⟨(RingEquiv.piCongrLeft (fun e : P.1 => Localization (S I e.1)) P.1.equivFin.symm).symm⟩

end LateralTheory.E.StageProdPf
