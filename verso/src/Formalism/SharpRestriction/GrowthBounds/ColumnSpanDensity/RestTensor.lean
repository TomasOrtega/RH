import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Tensor
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.EdgeLatRS

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems

/- English proof (translation)
Introduce `p n' R m e he s`. Take `⟨gs, hgs, -, h2, -⟩` from `edgeLat_RS R e he`. Use `⟨_, ?_, h2 s⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_mul]`. Conclude with `(hgs s).mul (lb_D_det (m + 1) 1 _ (RS.w_ne R))`.
-/
theorem restLeLat : RestLeLat := by
  intro p n' R m e he s
  obtain ⟨gs, hgs, -, h2, -⟩ := edgeLat_RS R e he
  refine ⟨_, ?_, h2 s⟩
  rw [Matrix.det_mul]
  exact (hgs s).mul (lb_D_det (m + 1) 1 _ (RS.w_ne R))

/- English proof (translation)
The claim follows from `restTensor_of restLeLat`.
-/
theorem restTensor : RestTensor := restTensor_of restLeLat

end Formalism.MainNotions.flipOneThree.Pf

end
