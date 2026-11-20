import Formalism.LatticeSlopes.CovolAntiSameRank

namespace Formalism.F

universe u

/- English proof (translation)
Introduce `E _ _ _ L N hL hNL hN`. Conclude with `le_csSup (h E L hL) (show slope N ∈ slopes L from ⟨N, hNL, hN, rfl⟩)`.
-/
theorem slopeLeMuMax_of (h : SlopesBdd.{u}) : SlopeLeMuMax.{u} := by
  intro E _ _ _ L N hL hNL hN
  exact le_csSup (h E L hL) (show slope N ∈ slopes L from ⟨N, hNL, hN, rfl⟩)

/- English proof (translation)
Introduce `E _ _ _ L N hL hNL hN`. Apply `csSup_le_csSup (h E L hL) (show (slopes N).Nonempty from ⟨slope N, N, le_rfl, hN, rfl⟩)` to reduce the goal to its premises. Introduce and unpack `t ⟨M, hMN, hM, rfl⟩`. Conclude with `⟨M, hMN.trans hNL, hM, rfl⟩`.
-/
theorem muMaxMono_of (h : SlopesBdd.{u}) : MuMaxMono.{u} := by
  intro E _ _ _ L N hL hNL hN
  apply csSup_le_csSup (h E L hL) (show (slopes N).Nonempty from ⟨slope N, N, le_rfl, hN, rfl⟩)
  rintro t ⟨M, hMN, hM, rfl⟩
  exact ⟨M, hMN.trans hNL, hM, rfl⟩

end Formalism.F
