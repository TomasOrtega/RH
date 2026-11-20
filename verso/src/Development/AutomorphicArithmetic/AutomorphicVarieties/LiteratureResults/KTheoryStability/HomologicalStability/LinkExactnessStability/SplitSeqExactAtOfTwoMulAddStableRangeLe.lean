import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SubClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ZigzagDoubleComplex
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SubClosedSplitSeqAndUniSeqWithMemIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExactAtLinkInSplitSeqOfExactAtSplitSeq
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExactAtUniSeqOrthogonalSplitSeqOfExactAtUniSeq
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.UnimodularSeqComplexExactAtOfAddStableRankLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.PairSeqDoubleComplexBoundaryRelations
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.PairSeqBoundariesLowerBidegreeOfSubClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.PairSeqHorizontalCycleIsBoundaryOfSlicesExact
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.PairSeqVerticalCycleIsBoundaryOfSlicesExact
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.PairNilHbdVbdEqZeroOfCycle
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsBdOfVbdEqOfOneTermCycle
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SubClosed2SplitPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SplitSeqFormsKillUniSeqExactAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsBdOfCycleFormsKillUnimodularVector
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL

namespace GlobalTheory.SeqCx

/- English proof (translation)
Introduce `c hc hbdc`. Take `⟨hhh, hvv, hhv⟩` from `GlobalTheory.T.pairSeqDoubleComplex_boundary_relations ((Fin n → R) × (Fin n → R)) (Fin n → R)`. Take `⟨hmh, hmv, h0⟩` from `GlobalTheory.T.pairSeqBoundaries_lower_bidegree_of_subClosed _ _ (splitPairs R n) (GlobalTheory.T.subClosed2_splitPairs R n)`. Establish `hnil : ([] : List (Fin n → R)) ∈ uniSeq R n` using `⟨fun i => absurd i.2 (by simp), fun i => absurd i.2 (by simp)⟩`. Establish `hc' : c ∈ chains {l | (l, ([] : List (Fin n → R))) ∈ splitPairs R n} p`.

Use `Finsupp.supported_mono ?_ hc` and prove the remaining obligations. Introduce and unpack `l ⟨hl, hlen⟩`. Conclude with `⟨⟨hl, hnil, by simp⟩, hlen⟩`. Take `⟨he, hhe, hve⟩` from `GlobalTheory.T.pair_nil_hbd_vbd_eq_zero_of_cycle _ _ (splitPairs R n) p c hc' hbdc`. Establish `hcol : ∀ a b, a + b = p → ∀ x ∈ chains2 (splitPairs R n) a b, vbd _ _ x = 0 → ∃ y ∈ chains2 (splitPairs R n) a (b + 1), vbd _ _ y = x`.

Introduce `a b hab x hx hvx`. Use `GlobalTheory.T.pairSeqVerticalCycle_is_boundary_of_slices_exact _ _ _ a b ?_ x hx hvx` and prove the remaining obligations. Introduce and unpack `l hl ⟨w, hw⟩`. Establish `hls : l ∈ splitSeq R n` using `hw.1`. Establish `hset : {w | (l, w) ∈ splitPairs R n} = {w | w ∈ uniSeq R n ∧ ∀ y ∈ l, ∀ u ∈ w, y.2 ⬝ᵥ u = 0}`.

Use extensionality with `w`. Conclude with `⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hls, h.1, h.2⟩⟩`. Rewrite using `[hset]`. Conclude with `GlobalTheory.T.exactAt_uniSeq_orthogonal_splitSeq_of_exactAt_uniSeq R s hs n (n - a) b l hls (by omega) (by omega) (GlobalTheory.T.unimodularSeqComplex_exactAt_of_add_stableRank_le R s hs (n - a) b (by omega))`. Establish `hrow : ∀ a b, a + b = p + 1 → 2 ≤ b → ∀ x ∈ chains2 (splitPairs R n) a b, hbd _ _ x = 0 → ∃ y ∈ chains2 (splitPairs R n) (a + 1) b, hbd _ _ y = x`.

Introduce `a b hab hb x hx hhx`. Use `GlobalTheory.T.pairSeqHorizontalCycle_is_boundary_of_slices_exact _ _ _ a b ?_ x hx hhx` and prove the remaining obligations. Introduce and unpack `w hw ⟨l, hl⟩`. Establish `hwu : w ∈ uniSeq R n` using `hl.2.1`. Establish `hset : {l | (l, w) ∈ splitPairs R n} = {σ | σ ∈ splitSeq R n ∧ ∀ y ∈ σ, ∀ u ∈ w, y.2 ⬝ᵥ u = 0}`.

Use extensionality with `σ`. Conclude with `⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hwu, h.2⟩⟩`. Rewrite using `[hset]`. Conclude with `GlobalTheory.T.splitSeq_forms_kill_uniSeq_exactAt R s hs n ih a w hwu (by omega) (by omega)`. Take `⟨z, hz, hhz, hvz⟩` from `GlobalTheory.zigzag_double_complex _ (chains2 (splitPairs R n)) (hbd _ _) (vbd _ _) p hhh hhv hmh hmv h0 hcol hrow hvv _ he hhe hve`.

Use `GlobalTheory.T.exists_bd_of_vbd_eq_of_oneTerm_cycle _ _ (splitPairs R n) (splitSeq R n) p ?_ z hz hhz c hvz` and prove the remaining obligations. Introduce and unpack `u ⟨l, hl⟩ c' hc' hbc'`. Establish `hu : [u] ∈ uniSeq R n` using `hl.2.1`. Establish `hset : {l | (l, [u]) ∈ splitPairs R n} = {σ | σ ∈ splitSeq R n ∧ ∀ y ∈ σ, ∀ v ∈ [u], y.2 ⬝ᵥ v = 0}`. Use extensionality with `σ`.

Conclude with `⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hu, h.2⟩⟩`. Rewrite `hc'` using `[hset]`. Conclude with `GlobalTheory.T.exists_bd_of_cycle_forms_kill_unimodular_vector R s hs n ih p u hu hp c' hc' hbc'`.
-/
theorem splitAcyclic_step (R : Type) [CommRing R] (s : ℕ) (hs : StableRangeLe R s) (n : ℕ)
    (ih : ∀ n' < n, ∀ p' : ℕ, 2 * p' + s + 1 ≤ n' → ExactAt (splitSeq R n') p') (p : ℕ)
    (hp : 2 * p + s + 1 ≤ n) : ExactAt (splitSeq R n) p := by
  intro c hc hbdc
  obtain ⟨hhh, hvv, hhv⟩ := GlobalTheory.T.pairSeqDoubleComplex_boundary_relations ((Fin n → R) × (Fin n → R)) (Fin n → R)
  obtain ⟨hmh, hmv, h0⟩ := GlobalTheory.T.pairSeqBoundaries_lower_bidegree_of_subClosed _ _ (splitPairs R n) (GlobalTheory.T.subClosed2_splitPairs R n)
  have hnil : ([] : List (Fin n → R)) ∈ uniSeq R n :=
    ⟨fun i => absurd i.2 (by simp), fun i => absurd i.2 (by simp)⟩
  have hc' : c ∈ chains {l | (l, ([] : List (Fin n → R))) ∈ splitPairs R n} p := by
    refine Finsupp.supported_mono ?_ hc
    rintro l ⟨hl, hlen⟩
    exact ⟨⟨hl, hnil, by simp⟩, hlen⟩
  obtain ⟨he, hhe, hve⟩ := GlobalTheory.T.pair_nil_hbd_vbd_eq_zero_of_cycle _ _ (splitPairs R n) p c hc' hbdc
  have hcol : ∀ a b, a + b = p → ∀ x ∈ chains2 (splitPairs R n) a b,
      vbd _ _ x = 0 → ∃ y ∈ chains2 (splitPairs R n) a (b + 1), vbd _ _ y = x := by
    intro a b hab x hx hvx
    refine GlobalTheory.T.pairSeqVerticalCycle_is_boundary_of_slices_exact _ _ _ a b ?_ x hx hvx
    rintro l hl ⟨w, hw⟩
    have hls : l ∈ splitSeq R n := hw.1
    have hset : {w | (l, w) ∈ splitPairs R n} =
        {w | w ∈ uniSeq R n ∧ ∀ y ∈ l, ∀ u ∈ w, y.2 ⬝ᵥ u = 0} := by
      ext w
      exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hls, h.1, h.2⟩⟩
    rw [hset]
    exact GlobalTheory.T.exactAt_uniSeq_orthogonal_splitSeq_of_exactAt_uniSeq R s hs n (n - a) b l hls (by omega) (by omega)
      (GlobalTheory.T.unimodularSeqComplex_exactAt_of_add_stableRank_le R s hs (n - a) b (by omega))
  have hrow : ∀ a b, a + b = p + 1 → 2 ≤ b → ∀ x ∈ chains2 (splitPairs R n) a b,
      hbd _ _ x = 0 → ∃ y ∈ chains2 (splitPairs R n) (a + 1) b, hbd _ _ y = x := by
    intro a b hab hb x hx hhx
    refine GlobalTheory.T.pairSeqHorizontalCycle_is_boundary_of_slices_exact _ _ _ a b ?_ x hx hhx
    rintro w hw ⟨l, hl⟩
    have hwu : w ∈ uniSeq R n := hl.2.1
    have hset : {l | (l, w) ∈ splitPairs R n} =
        {σ | σ ∈ splitSeq R n ∧ ∀ y ∈ σ, ∀ u ∈ w, y.2 ⬝ᵥ u = 0} := by
      ext σ
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hwu, h.2⟩⟩
    rw [hset]
    exact GlobalTheory.T.splitSeq_forms_kill_uniSeq_exactAt R s hs n ih a w hwu (by omega) (by omega)
  obtain ⟨z, hz, hhz, hvz⟩ := GlobalTheory.zigzag_double_complex _ (chains2 (splitPairs R n)) (hbd _ _) (vbd _ _) p
    hhh hhv hmh hmv h0 hcol hrow hvv _ he hhe hve
  refine GlobalTheory.T.exists_bd_of_vbd_eq_of_oneTerm_cycle _ _ (splitPairs R n) (splitSeq R n) p ?_ z hz hhz c hvz
  rintro u ⟨l, hl⟩ c' hc' hbc'
  have hu : [u] ∈ uniSeq R n := hl.2.1
  have hset : {l | (l, [u]) ∈ splitPairs R n} =
      {σ | σ ∈ splitSeq R n ∧ ∀ y ∈ σ, ∀ v ∈ [u], y.2 ⬝ᵥ v = 0} := by
    ext σ
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hu, h.2⟩⟩
  rw [hset] at hc'
  exact GlobalTheory.T.exists_bd_of_cycle_forms_kill_unimodular_vector R s hs n ih p u hu hp c' hc' hbc'

/- English proof (translation)
Introduce `R _ s hs n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih => exact splitAcyclic_step R s hs n ih`.
-/
theorem exactAt_splitSeq_of_stableRange : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s →
    ∀ n p : ℕ, 2 * p + s + 1 ≤ n → ExactAt (splitSeq R n) p := by
  intro R _ s hs n
  induction n using Nat.strong_induction_on with
  | _ n ih => exact splitAcyclic_step R s hs n ih

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.SeqCx.exactAt_splitSeq_of_stableRange`. Consider the case `exact @GlobalTheory.SeqCx.splitAcyclic_step`.
-/
theorem _root_.GlobalTheory.T.splitSeq_exactAt_of_two_mul_add_stableRange_le : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ n p : ℕ, 2 * p + s + 1 ≤ n → ExactAt (splitSeq R n) p := by
  first
  | exact @GlobalTheory.SeqCx.exactAt_splitSeq_of_stableRange
  | exact @GlobalTheory.SeqCx.splitAcyclic_step
end
