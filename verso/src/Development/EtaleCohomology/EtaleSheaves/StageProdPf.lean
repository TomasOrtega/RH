import Development.EtaleCohomology.EtaleSheaves.PartDiagCut

noncomputable section
open GlobalTheory.EtC

namespace LateralTheory.E.StageProdPf
open LateralTheory.E.PartDiagCut

/- English proof (translation)
Introduce and unpack `⟨t, ht⟩`. Simplify using `only [map_zero, zero_mul] at ht`. Conclude with `(P.idem e.1 e.2).2 ht.symm`.
-/
theorem zero_not_mem_S {B : Type} [CommRing B] (I : Ideal B) (P : LateralTheory.E.PartDiagCut.Part (B ⧸ I)) (e : P.1) :
    (0 : B) ∉ S I e.1 := by
  rintro ⟨t, ht⟩
  simp only [map_zero, zero_mul] at ht
  exact (P.idem e.1 e.2).2 ht.symm

/- English proof (translation)
Introduce `q B _ _ I hB hq P`. Set `R : Fin P.1.card → Type` to `fun k => Localization (S I (P.1.equivFin.symm k).1)`. Use `⟨P.1.card, R, fun k => inferInstance, fun k => ?_, ?_⟩` and prove the remaining obligations. Take `⟨h1, h2⟩` from `hloc B (S I (P.1.equivFin.symm k).1) (zero_not_mem_S I P _) hB`. Use `⟨h1, h2, ?_⟩` and prove the remaining obligations.

Use `hq.map (algebraMap B (R k))` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Conclude with `⟨(RingEquiv.piCongrLeft (fun e : P.1 => Localization (S I e.1)) P.1.equivFin.symm).symm⟩`.
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
