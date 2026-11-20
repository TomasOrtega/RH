import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIdemSumSubOfSubsetAndOrthogonalStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.MoveArgsOneTranspose
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedHomLatticeIffIntegralOnUnitHalfStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankCol
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FlipTop

/- English proof (translation)
Introduce `D T L sc G B μ₀ hL t e e' he he' hAA Φ j hj`. Establish `hsub : GlobalTheory.FlipTop.topPl L t ⊆ locPl G t`. Introduce `w hw`. Break down `Finset.mem_union.1 hw with h | h` into its components or cases. Conclude with `Finset.mem_union_left _ (levelChainTypePlaces_subset_chosenPlaces G hL t h)`.

Conclude with `Finset.mem_union_right _ h`. Take `⟨he₁, -⟩` from `GlobalTheory.T.isIdemSum_sub_of_subset_and_orthogonal he he' hsub`. Establish `h1` using `GlobalTheory.PlaceDatum.idemSum_mul_self he'`. Establish `h2` using `GlobalTheory.PlaceDatum.idemSum_mul_self he₁`. Take `⟨-, c1, c0⟩` from `GlobalTheory.FunObj.Comparison₂.cpt_idemSum he'`.

Take `⟨-, d1, -⟩` from `GlobalTheory.FunObj.Comparison₂.cpt_idemSum he₁`. Establish `ha` using `GlobalTheory.FlipTop.rank_col G hj.le`. Establish `hb` using `GlobalTheory.FlipTop.rank_col G hj`. Use function extensionality and compare the values at `x`. Rewrite using `[GlobalTheory.HalfProd.prodHalf_apply, add_sub_cancel]`.

Unfold `GlobalTheory.FlipStart.givenFn`. Distinguish the cases in `hx : IsHalf e x`. Use `swap`. Rewrite using `[if_neg hx, if_neg hx, mul_zero]`. Rewrite using `[if_pos hx, if_pos hx, mul_one]`.

Use `set N := GlobalTheory.FunObj.Comparison₂.fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D)) with hN`. Establish `hfr : ∀ a : AE D, GlobalTheory.FunObj.Comparison₂.fr (B.β 0 (j + 1)) (B.β 0 j) ((a • x).map (toEAf D)) = toEAf D a • N`. Introduce `a`. Rewrite using `[hN, ← GlobalTheory.FunObj.Comparison₂.fr_smul]`. Use `congr 1`.

Use extensionality with `p q`. Simplify using `[Matrix.map_apply, Matrix.smul_apply, RingHom.map_mul]`. Establish `hcomp : ∀ (a : AE D) (w : Pl D.host.E), cpt (D` using `D) w (toEAf D a) = 1 → (GlobalTheory.FunObj.Comparison₂.fr (B.β 0 (j + 1)) (B.β 0 j) ((a • x).map (toEAf D))).map (cpt (D := D) w) = N.map (cpt (D := D) w) := by`. Introduce `a w hw`. Rewrite using `[hfr]`.

Use extensionality with `p q`. Simplify using `[Matrix.map_apply, Matrix.smul_apply, RingHom.map_mul, hw]`. Establish `hsubm : ∀ w : Pl D.host.E, GlobalTheory.StepData.IntM ((N.map (cpt (D` using `D) w)).submatrix (GlobalTheory.FunObj.Comparison₂.ixOf G t w hb) (GlobalTheory.FunObj.Comparison₂.ixOf G t w ha)) ↔ GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) := fun w => ⟨fun h i l => by simpa using h ((GlobalTheory.FunObj.Comparison₂.ixOf G t w hb).symm i) ((GlobalTheo …`. Establish `hR : ∀ w, givenDatum t w B Φ (edgeOf (.down t 0 j)) (locArg B t w (.down t 0 j) x) = stepFn L t w j ((N.map (cpt (D` using `D) w)).submatrix (GlobalTheory.FunObj.Comparison₂.ixOf G t w hb) (GlobalTheory.FunObj.Comparison₂.ixOf G t w ha)) := by`. Introduce `w`.

Establish `hla : locArg B t w (.down t 0 j) x = B.coord t w (X` using `(0, j + 1)) (Y := (0, j)) ⟨Nat.zero_le _, hj⟩ ⟨Nat.zero_le _, hj.le⟩ ((x.map (toEAf D)).map (cpt (D := D) w)) := by`. Rewrite using `[Matrix.map_map]`. Conclude with `dif_pos ⟨Nat.zero_le _, hj⟩`. Rewrite using `[hla]`. Conclude with `GlobalTheory.FunObj.Comparison₂.givenDatum_theta_coord B t w Φ hj ha hb (x.map (toEAf D))`.

Rewrite using `[Finset.prod_congr rfl fun w _ => hR w, ← Finset.prod_sdiff hsub]`. Establish `hout : ∀ w ∈ locPl G t \ GlobalTheory.FlipTop.topPl L t, stepFn L t w j ((N.map (cpt (D` using `D) w)).submatrix (GlobalTheory.FunObj.Comparison₂.ixOf G t w hb) (GlobalTheory.FunObj.Comparison₂.ixOf G t w ha)) = if GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) then 1 else 0 := by`. Introduce `w hw`. Take `⟨-, hw2⟩` from `Finset.mem_sdiff.1 hw`. Establish `hP : w ∉ L.Pg` using `fun h => hw2 (Finset.mem_union_left _ h)`.

Establish `hQ : w ∉ L.Q t` using `fun h => hw2 (Finset.mem_union_right _ h)`. Unfold `stepFn`. Rewrite using `[if_neg hP, if_neg hQ, Set.indicator_apply]`. Conclude with `if_congr (hsubm w) rfl rfl`. Rewrite using `[Finset.prod_congr rfl hout, Finset.prod_boole]`.

Establish `hx1 : IsHalf (e - e') ((e - e') • x)` using `fun p q => by`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, h2]`. Establish `hS : IsSelfDualC (G.pS (.mu t 0 j)) (G.latS (.mu t 0 j))` using `(colY_isV D T L μ₀ hL j hj.le).sd`. Establish `hT : IsSelfDualC (G.pT (.mu t 0 j)) (G.latT (.mu t 0 j))` using `(colY_isV D T L μ₀ hL (j + 1) hj).sd`. Establish `hAA' : ∀ w ∈ locPl G t \ GlobalTheory.FlipTop.topPl L t, ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)` using `fun w hw => hAA w (Finset.mem_sdiff.1 hw).1 (Finset.mem_sdiff.1 hw).2`.

Establish `hlat` using `GlobalTheory.T.mem_completedHomLattice_iff_integral_on_unit_half hS hT (B.isFrame_β hL (Nat.zero_le _) hj.le) (B.isFrame_β hL (Nat.zero_le _) hj) he₁ hAA' ((e - e') • x) hx1`. Establish `k1 : halfInd (e - e') (latO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (G.latS (.mu t 0 j) : Set _) (G.latT (.mu t 0 j) : Set _) fun _ => True) ((e - e') • x) = if ∀ w ∈ locPl G t \ GlobalTheory.FlipTop.topPl L t, GlobalTheory.StepData.IntM (N.map (cpt (D` using `D) w)) then 1 else 0 := by`. Unfold `halfInd`. Use `if_congr ?_ rfl rfl` and prove the remaining obligations. Rewrite using `[and_iff_left hx1, hlat]`.

Conclude with `forall₂_congr fun w hw => by rw [hcomp _ w (d1 w hw)]`. Establish `hint : IsIntM (toEAf D e' • N) ↔ ∀ w ∈ GlobalTheory.FlipTop.topPl L t, GlobalTheory.StepData.IntM (N.map (cpt (D` using `D) w)) := by`. Prove the components needed by the constructor for the conclusion. Introduce `h w hw i l`. Use `(mem_OA_iff _).1 (h i l) w` as an intermediate fact.

Rewrite `this` using `[Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, c1 w hw, one_mul]`. Conclude with `(GlobalTheory.FunObj.Comparison₂.vEq w).le_one_iff_le_one.2 this`. Introduce `h i l`. Use `(mem_OA_iff _).2 fun w => ?_` and prove the remaining obligations. Rewrite using `[Matrix.smul_apply, smul_eq_mul, RingHom.map_mul]`.

Distinguish the cases in `hw : w ∈ GlobalTheory.FlipTop.topPl L t`. Rewrite using `[c1 w hw, one_mul]`. Conclude with `(GlobalTheory.FunObj.Comparison₂.vEq w).le_one_iff_le_one.1 (h w hw i l)`. Rewrite using `[c0 w hw, zero_mul]`. Conclude with `zero_mem _`.

Establish `hx0 : IsHalf e' (e' • x)` using `fun p q => by`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, h1]`. Establish `k0 : GlobalTheory.FlipTop.topFn B t e' j ha hb (e' • x) = ∏ w ∈ GlobalTheory.FlipTop.topPl L t, stepFn L t w j ((N.map (cpt (D` using `D) w)).submatrix (GlobalTheory.FunObj.Comparison₂.ixOf G t w hb) (GlobalTheory.FunObj.Comparison₂.ixOf G t w ha)) := by`. Unfold `GlobalTheory.FlipTop.topFn`. Rewrite using `[Finset.prod_congr rfl fun w hw => by rw [hcomp e' w (c1 w hw)]]`.

Distinguish the cases in `H : ∀ w ∈ GlobalTheory.FlipTop.topPl L t, GlobalTheory.StepData.IntM (N.map (cpt (D := D) w))`. Rewrite using `[if_pos ⟨hx0, by rw [hfr]; exact hint.2 H⟩]`. Rewrite `H` using `[if_neg fun h => H (by have h' := h.2; rw [hfr] at h'; exact hint.1 h')] push_neg`. Take `⟨w, hw, hn⟩` from `H`. Use `(Finset.prod_eq_zero hw ?_).symm` and prove the remaining obligations.

Assume the negation of the conclusion as `h0`. Conclude with `hn ((hsubm w).1 (GlobalTheory.FunObj.LocTest.intM_of_stepFn t w j h0))`. Rewrite using `[k0, k1, mul_comm]`.
-/
theorem prodHalf_topFn_eq_givenFn : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (B : Frames G) {μ₀ : T}, L.Is μ₀ →
    ∀ (t : T) {e e' : AE D}, IsIdemSum e (locPl G t) → IsIdemSum e' (GlobalTheory.FlipTop.topPl L t) → (∀ w ∈ locPl G t, w ∉ GlobalTheory.FlipTop.topPl L t → ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)) → ∀ (Φ : G.Datum) (j : ℕ) (hj : j < D.R.m),
    GlobalTheory.HalfProd.prodHalf e' (e - e') (halfInd (e - e') (latO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (G.latS (.mu t 0 j) : Set _) (G.latT (.mu t 0 j) : Set _) fun _ => True)) (GlobalTheory.FlipTop.topFn B t e' j (GlobalTheory.FlipTop.rank_col G hj.le) (GlobalTheory.FlipTop.rank_col G hj)) =
      GlobalTheory.FlipStart.givenFn B t Φ e (.down t 0 j) := by
  intro D T L sc G B μ₀ hL t e e' he he' hAA Φ j hj
  classical
  have hsub : GlobalTheory.FlipTop.topPl L t ⊆ locPl G t := by
    intro w hw
    rcases Finset.mem_union.1 hw with h | h
    · exact Finset.mem_union_left _ (levelChainTypePlaces_subset_chosenPlaces G hL t h)
    · exact Finset.mem_union_right _ h
  obtain ⟨he₁, -⟩ := GlobalTheory.T.isIdemSum_sub_of_subset_and_orthogonal he he' hsub
  have h1 := GlobalTheory.PlaceDatum.idemSum_mul_self he'
  have h2 := GlobalTheory.PlaceDatum.idemSum_mul_self he₁
  obtain ⟨-, c1, c0⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he'
  obtain ⟨-, d1, -⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he₁
  have ha := GlobalTheory.FlipTop.rank_col G hj.le
  have hb := GlobalTheory.FlipTop.rank_col G hj
  funext x
  rw [GlobalTheory.HalfProd.prodHalf_apply, add_sub_cancel]
  unfold GlobalTheory.FlipStart.givenFn
  by_cases hx : IsHalf e x
  swap
  · rw [if_neg hx, if_neg hx, mul_zero]
  rw [if_pos hx, if_pos hx, mul_one]
  set N := GlobalTheory.FunObj.Comparison₂.fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D)) with hN
  have hfr : ∀ a : AE D, GlobalTheory.FunObj.Comparison₂.fr (B.β 0 (j + 1)) (B.β 0 j) ((a • x).map (toEAf D)) = toEAf D a • N := by
    intro a
    rw [hN, ← GlobalTheory.FunObj.Comparison₂.fr_smul]
    congr 1
    ext p q
    simp [Matrix.map_apply, Matrix.smul_apply, RingHom.map_mul]
  have hcomp : ∀ (a : AE D) (w : Pl D.host.E), cpt (D := D) w (toEAf D a) = 1 →
      (GlobalTheory.FunObj.Comparison₂.fr (B.β 0 (j + 1)) (B.β 0 j) ((a • x).map (toEAf D))).map (cpt (D := D) w) = N.map (cpt (D := D) w) := by
    intro a w hw
    rw [hfr]
    ext p q
    simp [Matrix.map_apply, Matrix.smul_apply, RingHom.map_mul, hw]

  have hsubm : ∀ w : Pl D.host.E, GlobalTheory.StepData.IntM ((N.map (cpt (D := D) w)).submatrix (GlobalTheory.FunObj.Comparison₂.ixOf G t w hb)
      (GlobalTheory.FunObj.Comparison₂.ixOf G t w ha)) ↔ GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) := fun w =>
    ⟨fun h i l => by simpa using h ((GlobalTheory.FunObj.Comparison₂.ixOf G t w hb).symm i) ((GlobalTheory.FunObj.Comparison₂.ixOf G t w ha).symm l),
      fun h i l => h _ _⟩
  have hR : ∀ w, givenDatum t w B Φ (edgeOf (.down t 0 j)) (locArg B t w (.down t 0 j) x) =
      stepFn L t w j ((N.map (cpt (D := D) w)).submatrix (GlobalTheory.FunObj.Comparison₂.ixOf G t w hb) (GlobalTheory.FunObj.Comparison₂.ixOf G t w ha)) := by
    intro w
    have hla : locArg B t w (.down t 0 j) x = B.coord t w (X := (0, j + 1)) (Y := (0, j)) ⟨Nat.zero_le _, hj⟩
        ⟨Nat.zero_le _, hj.le⟩ ((x.map (toEAf D)).map (cpt (D := D) w)) := by
      rw [Matrix.map_map]
      exact dif_pos ⟨Nat.zero_le _, hj⟩
    rw [hla]
    exact GlobalTheory.FunObj.Comparison₂.givenDatum_theta_coord B t w Φ hj ha hb (x.map (toEAf D))
  rw [Finset.prod_congr rfl fun w _ => hR w, ← Finset.prod_sdiff hsub]
  have hout : ∀ w ∈ locPl G t \ GlobalTheory.FlipTop.topPl L t, stepFn L t w j ((N.map (cpt (D := D) w)).submatrix
      (GlobalTheory.FunObj.Comparison₂.ixOf G t w hb) (GlobalTheory.FunObj.Comparison₂.ixOf G t w ha)) =
      if GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) then 1 else 0 := by
    intro w hw
    obtain ⟨-, hw2⟩ := Finset.mem_sdiff.1 hw
    have hP : w ∉ L.Pg := fun h => hw2 (Finset.mem_union_left _ h)
    have hQ : w ∉ L.Q t := fun h => hw2 (Finset.mem_union_right _ h)
    unfold stepFn
    rw [if_neg hP, if_neg hQ, Set.indicator_apply]
    exact if_congr (hsubm w) rfl rfl
  rw [Finset.prod_congr rfl hout, Finset.prod_boole]

  have hx1 : IsHalf (e - e') ((e - e') • x) := fun p q => by
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, h2]
  have hS : IsSelfDualC (G.pS (.mu t 0 j)) (G.latS (.mu t 0 j)) := (colY_isV D T L μ₀ hL j hj.le).sd
  have hT : IsSelfDualC (G.pT (.mu t 0 j)) (G.latT (.mu t 0 j)) := (colY_isV D T L μ₀ hL (j + 1) hj).sd
  have hAA' : ∀ w ∈ locPl G t \ GlobalTheory.FlipTop.topPl L t, ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1) := fun w hw =>
    hAA w (Finset.mem_sdiff.1 hw).1 (Finset.mem_sdiff.1 hw).2
  have hlat := GlobalTheory.T.mem_completedHomLattice_iff_integral_on_unit_half hS hT (B.isFrame_β hL (Nat.zero_le _) hj.le) (B.isFrame_β hL (Nat.zero_le _) hj) he₁ hAA'
    ((e - e') • x) hx1
  have k1 : halfInd (e - e') (latO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (G.latS (.mu t 0 j) : Set _)
      (G.latT (.mu t 0 j) : Set _) fun _ => True) ((e - e') • x) =
      if ∀ w ∈ locPl G t \ GlobalTheory.FlipTop.topPl L t, GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) then 1 else 0 := by
    unfold halfInd
    refine if_congr ?_ rfl rfl
    rw [and_iff_left hx1, hlat]
    exact forall₂_congr fun w hw => by rw [hcomp _ w (d1 w hw)]

  have hint : IsIntM (toEAf D e' • N) ↔ ∀ w ∈ GlobalTheory.FlipTop.topPl L t, GlobalTheory.StepData.IntM (N.map (cpt (D := D) w)) := by
    constructor
    · intro h w hw i l
      have := (mem_OA_iff _).1 (h i l) w
      rw [Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, c1 w hw, one_mul] at this
      exact (GlobalTheory.FunObj.Comparison₂.vEq w).le_one_iff_le_one.2 this
    · intro h i l
      refine (mem_OA_iff _).2 fun w => ?_
      rw [Matrix.smul_apply, smul_eq_mul, RingHom.map_mul]
      by_cases hw : w ∈ GlobalTheory.FlipTop.topPl L t
      · rw [c1 w hw, one_mul]
        exact (GlobalTheory.FunObj.Comparison₂.vEq w).le_one_iff_le_one.1 (h w hw i l)
      · rw [c0 w hw, zero_mul]
        exact zero_mem _
  have hx0 : IsHalf e' (e' • x) := fun p q => by
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, h1]
  have k0 : GlobalTheory.FlipTop.topFn B t e' j ha hb (e' • x) = ∏ w ∈ GlobalTheory.FlipTop.topPl L t, stepFn L t w j
      ((N.map (cpt (D := D) w)).submatrix (GlobalTheory.FunObj.Comparison₂.ixOf G t w hb) (GlobalTheory.FunObj.Comparison₂.ixOf G t w ha)) := by
    unfold GlobalTheory.FlipTop.topFn
    rw [Finset.prod_congr rfl fun w hw => by rw [hcomp e' w (c1 w hw)]]
    by_cases H : ∀ w ∈ GlobalTheory.FlipTop.topPl L t, GlobalTheory.StepData.IntM (N.map (cpt (D := D) w))
    · rw [if_pos ⟨hx0, by rw [hfr]; exact hint.2 H⟩]
    · rw [if_neg fun h => H (by have h' := h.2; rw [hfr] at h'; exact hint.1 h')]
      push_neg at H
      obtain ⟨w, hw, hn⟩ := H
      refine (Finset.prod_eq_zero hw ?_).symm
      by_contra h0
      exact hn ((hsubm w).1 (GlobalTheory.FunObj.LocTest.intM_of_stepFn t w j h0))
  rw [k0, k1, mul_comm]

end GlobalTheory.FlipTop

end
