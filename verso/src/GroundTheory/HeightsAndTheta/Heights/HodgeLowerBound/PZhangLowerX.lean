import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsZhangLowerX
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCurvePointsFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo HilbertSamuel.CurvePointsFinite

/- English proof (translation)
Establish `: W.IsPrime` using `hW.2.1.1`. Use `charZero_fractionRing W hW.2.2.1` as an intermediate fact. Establish `hEq` using `mCoordIdeal_genericPt W hW.2.1.2.1`. Establish `hP : IsArithVar (mCoordIdeal (genericPt W)) 1` using `by rw [hEq]; exact hW`. Establish `hdeg` using `IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.degC_eq hP`.

Rewrite `hdeg` using `[hEq]`. Use `IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.isAlgebraic_blockFnField hP` as an intermediate fact. Use `set L := ReciprocityTheory.ChartRestriction.G.AI.I4.blockFnField (genericPt W)`. Use `set S : Set (FractionRing (MRing ι ⧸ W)) := {t | ∃ p q : Σ k, ι k, p.1 = q.1 ∧ t = genericPt W p / genericPt W q}`. Establish `hSfin : S.Finite` using `(Set.finite_range fun pq : (Σ k, ι k) × (Σ k, ι k) ↦ genericPt W pq.1 / genericPt W pq.2).subset fun t ⟨p, q, _, ht⟩ ↦ ⟨(p, q), ht.symm⟩`.

Establish `: Finite S` using `hSfin.to_subtype`. Establish `hint : ∀ t ∈ S, IsIntegral ℚ t` using `fun t ht ↦ ((Algebra.IsAlgebraic.isAlgebraic (⟨t, IntermediateField.subset_adjoin ℚ S ht⟩ : L)).isIntegral).map L.val`. Establish `: FiniteDimensional ℚ L` using `IntermediateField.finiteDimensional_adjoin hint`. Rewrite using `[hdeg]`. Conclude with `Nat.card_pos_iff.2 ⟨⟨IsAlgClosed.lift⟩, inferInstance⟩`.
-/
theorem degC_pos_of_isArithVar_one {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {W : Ideal (MRing ι)} (hW : IsArithVar W 1) : 0 < degC W := by
  have : W.IsPrime := hW.2.1.1
  have := charZero_fractionRing W hW.2.2.1
  have hEq := mCoordIdeal_genericPt W hW.2.1.2.1
  have hP : IsArithVar (mCoordIdeal (genericPt W)) 1 := by rw [hEq]; exact hW
  have hdeg := IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.degC_eq hP
  rw [hEq] at hdeg
  have := IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.isAlgebraic_blockFnField hP
  set L := ReciprocityTheory.ChartRestriction.G.AI.I4.blockFnField (genericPt W)
  set S : Set (FractionRing (MRing ι ⧸ W)) :=
    {t | ∃ p q : Σ k, ι k, p.1 = q.1 ∧ t = genericPt W p / genericPt W q}
  have hSfin : S.Finite := (Set.finite_range fun pq : (Σ k, ι k) × (Σ k, ι k) ↦
      genericPt W pq.1 / genericPt W pq.2).subset fun t ⟨p, q, _, ht⟩ ↦ ⟨(p, q), ht.symm⟩
  have : Finite S := hSfin.to_subtype
  have hint : ∀ t ∈ S, IsIntegral ℚ t := fun t ht ↦
    ((Algebra.IsAlgebraic.isAlgebraic (⟨t, IntermediateField.subset_adjoin ℚ S ht⟩ : L)).isIntegral).map
      L.val
  have : FiniteDimensional ℚ L := IntermediateField.finiteDimensional_adjoin hint
  rw [hdeg]
  exact Nat.card_pos_iff.2 ⟨⟨IsAlgClosed.lift⟩, inferInstance⟩

/- English proof (translation)
Introduce `K _ ι _ P P0 n A e II hII hP hP0 hs hnef hc hh`. Use `h K ι P P0 n A e II hII hP hP0 hs hnef hc fun W hW hPW ↦ ?_` and prove the remaining obligations. Establish `hd : (0 : ℝ) < degC W` using `Nat.cast_pos.2 (degC_pos_of_isArithVar_one hW)`. Establish `h1` using `hh W hW hPW`. Rewrite `h1` using `[IndefiniteRowSideFullHecke.HeightsSet.height, le_div_iff₀ hd]`. Then use the resulting hypothesis.
-/
theorem ZhangLowerX.proof (h : SuccessiveMinimaLowerBound) : ZhangLowerX.Statement := by
  intro K _ ι _ P P0 n A e II hII hP hP0 hs hnef hc hh
  refine h K ι P P0 n A e II hII hP hP0 hs hnef hc fun W hW hPW ↦ ?_
  have hd : (0 : ℝ) < degC W := Nat.cast_pos.2 (degC_pos_of_isArithVar_one hW)
  have h1 := hh W hW hPW
  rwa [IndefiniteRowSideFullHecke.HeightsSet.height, le_div_iff₀ hd] at h1

end GroundTheory.Heights₂.Heights.LowerBoundFree
