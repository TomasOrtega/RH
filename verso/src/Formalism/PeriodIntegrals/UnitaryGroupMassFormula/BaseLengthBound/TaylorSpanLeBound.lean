import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorSpanGeneratorsAlt

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

/- English proof (translation)
Introduce `D B P j X ka wL wF G la Q S CRm T c hOk hw hth`. Set `G' : GlobalFamilyData X (addL wF wL T) wL wF` to `{ N := G.N, w := G.w, del := G.del, th' := G.th', rz := G.rz, alz := G.alz, th0 := G.th0, zc := fun _ => 0, rq := 0, th := Fin.elim0, iet := G.iet, et := G.et, mx := G.mx }`. Set `Q' : LocalPointData G' la` to `⟨Q.y, Q.g0, Q.c⟩`. Conclude with `reduced_generators_le (G := G') Q' S hOk.2.1 hOk.2.2.1 hw hth`.
-/
theorem taylorSpanLeBound : TaylorSpanLeBound := by
  intro D B P j X ka wL wF G la Q S CRm T c hOk hw hth
  let G' : GlobalFamilyData X (addL wF wL T) wL wF :=
    { N := G.N, w := G.w, del := G.del, th' := G.th', rz := G.rz, alz := G.alz, th0 := G.th0,
      zc := fun _ => 0, rq := 0, th := Fin.elim0, iet := G.iet, et := G.et, mx := G.mx }
  let Q' : LocalPointData G' la := ⟨Q.y, Q.g0, Q.c⟩
  exact reduced_generators_le (G := G') Q' S hOk.2.1 hOk.2.2.1 hw hth

end PoleLengthBounds
