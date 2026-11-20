import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocRankAdjoin
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartRankAdjoin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

/- English proof (translation)
Introduce `K _ ι _ K' _ ι' _ κ v P' n G J s α W hv hP' hZ hJ hs hsP hW`. Establish `hrel : ∀ k', ∃ i, (X ⟨k', i⟩ : MRing ι') ∉ P'` using `hP'.2.1.2.2`. Use `choose i' hi' using hrel`. Establish `hfib : IsProjVarF (fibreIdeal κ G) 0` using `hDim K ι K' ι' κ v P' (n + 1) 0 G hv hP' hZ`. Establish `hz : ∀ k : FibreBlock κ, G.x' ⟨k.1, i' k.1⟩ ≠ 0`.

Introduce `k h0`. Apply `hi' k.1` to reduce the goal to its premises. Rewrite using `[← G.genericFibre_ker_target, RingHom.mem_ker, aeval_X]`. Conclude with `h0`. Establish `hj : IsChart (fibreIdeal κ G) (fun k => i' k.1)`.

Introduce `k hk`. Apply `hz k` to reduce the goal to its premises. Rewrite `hk` using `[fibreIdeal, RingHom.mem_ker, aeval_X]`. Conclude with `hk`. Rewrite using `[hJ.1 _ Fin.elim0 _ hfib hj, hAdj K ι K' ι' κ v P' n G s α W i' hv hP' hZ hs hsP hW hi']`.

Use `congr 1`. Conclude with `(ChartRankAdjoin.proof (FibreBlock κ) (fibreIdx ι' κ) G.Φ G.Φ' (fun q => G.x' ⟨q.1.1, q.2⟩) (fun k => i' k.1) hz hfib.1.2.1).symm`.
-/
theorem SemilocRank.proof (hDim : FibreDimStatement) (hAdj : SemilocRankAdjoin.Statement) :
    SemilocRank.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G J s α W hv hP' hZ hJ hs hsP hW
  have hrel : ∀ k', ∃ i, (X ⟨k', i⟩ : MRing ι') ∉ P' := hP'.2.1.2.2
  choose i' hi' using hrel
  have hfib : IsProjVarF (fibreIdeal κ G) 0 := hDim K ι K' ι' κ v P' (n + 1) 0 G hv hP' hZ
  have hz : ∀ k : FibreBlock κ, G.x' ⟨k.1, i' k.1⟩ ≠ 0 := by
    intro k h0
    apply hi' k.1
    rw [← G.genericFibre_ker_target, RingHom.mem_ker, aeval_X]
    exact h0
  have hj : IsChart (fibreIdeal κ G) (fun k => i' k.1) := by
    intro k hk
    apply hz k
    rw [fibreIdeal, RingHom.mem_ker, aeval_X] at hk
    exact hk
  rw [hJ.1 _ Fin.elim0 _ hfib hj, hAdj K ι K' ι' κ v P' n G s α W i' hv hP' hZ hs hsP hW hi']
  congr 1
  exact (ChartRankAdjoin.proof (FibreBlock κ) (fibreIdx ι' κ) G.Φ G.Φ' (fun q => G.x' ⟨q.1.1, q.2⟩)
    (fun k => i' k.1) hz hfib.1.2.1).symm

end GroundTheory.Heights₂.Heights.Inter
