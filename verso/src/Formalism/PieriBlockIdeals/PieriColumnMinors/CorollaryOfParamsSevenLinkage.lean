import Formalism.PieriBlockIdeals.HidaLatticeInclusionAtCoarseWeightBound
import Formalism.PieriBlockIdeals.PieriColumnMinors.CorollaryOfParamsLinkage

namespace Formalism.CohomologicalDescent.Down7

/- English proof (translation)
Unfold `Formalism.CohomologicalDescent.ShortWeightBounds.cShort6 Formalism.CohomologicalDescent.UnitNormBounds.cCoarse`. Establish `e : ((q : ℝ) + 2 * (j : ℝ)) * (((h : ℝ) + (N' : ℝ)) / ((l : ℝ) - 1) + 6) = ((q : ℝ) + 2 * (j : ℝ)) * (((h : ℝ) + (N' : ℝ)) / ((l : ℝ) - 1)) + ((q : ℝ) + 2 * (j : ℝ)) * 6` using `by ring`. Establish `hq : (0 : ℝ) ≤ ((q : ℝ) + 2 * (j : ℝ)) * 6` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma cShort6_le_cCoarse (l k j t q h N' ecl : ℕ) (xm xp mB : ℤ) (I : ℝ) :
    Formalism.CohomologicalDescent.ShortWeightBounds.cShort6 l k j t q h N' ecl xm xp mB I ≤
      Formalism.CohomologicalDescent.UnitNormBounds.cCoarse l k j t q h N' ecl xm xp mB I := by
  unfold Formalism.CohomologicalDescent.ShortWeightBounds.cShort6 Formalism.CohomologicalDescent.UnitNormBounds.cCoarse
  have e : ((q : ℝ) + 2 * (j : ℝ)) * (((h : ℝ) + (N' : ℝ)) / ((l : ℝ) - 1) + 6) =
      ((q : ℝ) + 2 * (j : ℝ)) * (((h : ℝ) + (N' : ℝ)) / ((l : ℝ) - 1)) +
        ((q : ℝ) + 2 * (j : ℝ)) * 6 := by ring
  have hq : (0 : ℝ) ≤ ((q : ℝ) + 2 * (j : ℝ)) * 6 := by positivity
  linarith

/- English proof (translation)
Unfold `Formalism.CohomologicalDescent.ShortWeightBounds.Wts.JW Formalism.CohomologicalDescent.ShortWeightBounds.Wts.coarseWeightBound`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `τ _`. Unfold `Formalism.CohomologicalDescent.DepthNonnegative.cTau Formalism.CohomologicalDescent.ShortWeightBounds.cFloorShort6 Formalism.CohomologicalDescent.DepthNonnegative.cFloorCoarse`. Use `split_ifs`.

Conclude with `min_le_min_left _ (Nat.floor_mono (cShort6_le_cCoarse _ _ _ _ _ _ _ _ _ _ _ _))`. Conclude with `le_rfl`.
-/
private lemma JW_le_coarseWeightBound {ι : Type} [Fintype ι] [DecidableEq ι] (W : Formalism.CohomologicalDescent.ShortWeightBounds.Wts ι)
    (P : Formalism.CohomologicalDescent.LogSmallConstantBounds.Par) (l : ℕ) : W.JW P l ≤ W.coarseWeightBound P l := by
  unfold Formalism.CohomologicalDescent.ShortWeightBounds.Wts.JW Formalism.CohomologicalDescent.ShortWeightBounds.Wts.coarseWeightBound
  apply Finset.sum_le_sum
  intro τ _
  unfold Formalism.CohomologicalDescent.DepthNonnegative.cTau Formalism.CohomologicalDescent.ShortWeightBounds.cFloorShort6 Formalism.CohomologicalDescent.DepthNonnegative.cFloorCoarse
  split_ifs
  · exact min_le_min_left _ (Nat.floor_mono (cShort6_le_cCoarse _ _ _ _ _ _ _ _ _ _ _ _))
  · exact le_rfl

/- English proof (translation)
Introduce `y`. Establish `hy` using `h (a ^ (J' - J) • y)`. Rewrite `hy` using `[smul_smul, ← pow_add, Nat.add_sub_cancel' hJ]`. Then use the resulting hypothesis.
-/
private lemma pow_smul_mem_mono' {T M S : Type*} [Monoid T] [MulAction T M] [Membership M S]
    (a : T) (s : S) {J J' : ℕ} (hJ : J ≤ J') (h : ∀ y : M, a ^ J • y ∈ s) :
    ∀ y : M, a ^ J' • y ∈ s := by
  intro y
  have hy := h (a ^ (J' - J) • y)
  rwa [smul_smul, ← pow_add, Nat.add_sub_cancel' hJ] at hy

/- English proof (translation)
Unfold `Formalism.CohomologicalDescent.ShortWeightBounds.HidaSetting.Incl Formalism.CohomologicalDescent.DepthNonnegative.TopIncl at h ⊢`. Conclude with `pow_smul_mem_mono' _ _ hJ h`.
-/
private lemma Incl_mono {ι : Type} [DecidableEq ι] {N : ℕ} {lam : ι → ℕ → ℕ}
    (X : Formalism.CohomologicalDescent.ShortWeightBounds.HidaSetting ι N lam) (l J J' : ℕ) (h : X.Incl l J) (hJ : J ≤ J') :
    X.Incl l J' := by
  unfold Formalism.CohomologicalDescent.ShortWeightBounds.HidaSetting.Incl Formalism.CohomologicalDescent.DepthNonnegative.TopIncl at h ⊢
  exact pow_smul_mem_mono' _ _ hJ h

/- English proof (translation)
Introduce `P hP hL ι _ _ W hW l X hl hu hlJ hin`. Take `⟨h1, h2⟩` from `Formalism.CohomologicalDescent.Down.inclusion_w_real_holds P hP hL ι W hW l X hl hu hlJ hin`. Conclude with `⟨Incl_mono X l _ _ h1 (JW_le_coarseWeightBound W P l), le_trans h2 (JW_le_coarseWeightBound W P l)⟩`.
-/
theorem inclusion_w_seven_real_holds : HidaLatticeInclusionAtCoarseWeightBound := by
  intro P hP hL ι _ _ W hW l X hl hu hlJ hin
  obtain ⟨h1, h2⟩ := Formalism.CohomologicalDescent.Down.inclusion_w_real_holds P hP hL ι W hW l X hl hu hlJ hin
  exact ⟨Incl_mono X l _ _ h1 (JW_le_coarseWeightBound W P l), le_trans h2 (JW_le_coarseWeightBound W P l)⟩

end Formalism.CohomologicalDescent.Down7
