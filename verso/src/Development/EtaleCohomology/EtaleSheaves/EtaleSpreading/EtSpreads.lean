import Development.EtaleCohomology.EtaleSheaves.DescendPf

noncomputable section
open CategoryTheory Limits LateralTheory.E.t_E3Cut

namespace LateralTheory.E.SpreadPf

def EtSpreads : Prop := MorphismProperty.PreIndSpreads.{0} Et

/- English proof (translation)
Introduce `A O f hf C _ _ _`. Take `⟨J, _, _, D, t, s, hc, hJ⟩` from `hf`. Establish `hC : Et (CommRingCat.ofHom (algebraMap O C) : O ⟶ CommRingCat.of C)`. Express the relevant statement in the definitionally equal form `(algebraMap O C).Etale`. Conclude with `RingHom.etale_algebraMap.mpr inferInstance`.

Take `⟨j, T', f', g', hP, hf'⟩` from `hE.exists_isPushout hc _ hC`. Conclude with `⟨D.obj j, t.app j, s.app j, T', f', g'.hom, (hJ j).1, hf', (hJ j).2, hP.flip⟩`.
-/
theorem Spread_of (hE : EtSpreads) : LateralTheory.E.DescendPf.Spread := by
  intro A O f hf C _ _ _
  obtain ⟨J, _, _, D, t, s, hc, hJ⟩ := hf
  have hC : Et (CommRingCat.ofHom (algebraMap O C) : O ⟶ CommRingCat.of C) := by
    change (algebraMap O C).Etale
    exact RingHom.etale_algebraMap.mpr inferInstance
  obtain ⟨j, T', f', g', hP, hf'⟩ := hE.exists_isPushout hc _ hC
  exact ⟨D.obj j, t.app j, s.app j, T', f', g'.hom, (hJ j).1, hf', (hJ j).2, hP.flip⟩

end LateralTheory.E.SpreadPf
