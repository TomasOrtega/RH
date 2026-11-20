import Formalism.LatticeSlopes.CovolAntiSameRank

namespace Formalism.F

universe u

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem slopeLeMuMax_of (h : SlopesBdd.{u}) : SlopeLeMuMax.{u} := by
  intro E _ _ _ L N hL hNL hN
  exact le_csSup (h E L hL) (show slope N ∈ slopes L from ⟨N, hNL, hN, rfl⟩)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem muMaxMono_of (h : SlopesBdd.{u}) : MuMaxMono.{u} := by
  intro E _ _ _ L N hL hNL hN
  apply csSup_le_csSup (h E L hL) (show (slopes N).Nonempty from ⟨slope N, N, le_rfl, hN, rfl⟩)
  rintro t ⟨M, hMN, hM, rfl⟩
  exact ⟨M, hMN.trans hNL, hM, rfl⟩

end Formalism.F
