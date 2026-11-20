import Development.EtaleCohomology.EtaleSheaves.DescendPf

noncomputable section
open CategoryTheory Limits LateralTheory.E.t_E3Cut

namespace LateralTheory.E.SpreadPf

def EtSpreads : Prop := MorphismProperty.PreIndSpreads.{0} Et

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. A detailed English derivation is pending.
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
