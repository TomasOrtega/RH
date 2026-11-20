import Mathlib
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.StFSSmallCountBound
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.FSScaled
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PScaledFSTopPos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPerturbSemipos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ZcombIsConjInvariantH
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SmallSectionCountLeOfInjOn
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefOnGenericOfSemipos
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSmallGenHeightsNonneg
import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmIUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I2 GroundTheory.Heights₂.Heights.HilbertSamuel MvPolynomial
  Filter Topology

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Establish `hM : IsSemipositiveRel ⊥ P (constLine (ι` using `ι) 0) := by`. Use `⟨G5.isSmoothHerm_constLine 0, fun z _ w _ => ?_⟩` and prove the remaining obligations. Simplify using `[leviForm, constLine, HermLine.ofWeight]`. Conclude with `ScaledFSTopPos.semipos_of_h_eq (funext fun z => by simp [HermLine.zcomb]) (PerturbSemipos.proof K ι ⊥ P _ 0 1 hM le_rfl zero_le_one)`.
-/
theorem fsH_semipos (P : Ideal (MRing ι)) : IsSemipositiveRel ⊥ P (fsH ι) := by
  have hM : IsSemipositiveRel ⊥ P (constLine (ι := ι) 0) := by
    refine ⟨G5.isSmoothHerm_constLine 0, fun z _ w _ => ?_⟩
    simp [leviForm, constLine, HermLine.ofWeight]
  exact ScaledFSTopPos.semipos_of_h_eq (funext fun z => by simp [HermLine.zcomb])
    (PerturbSemipos.proof K ι ⊥ P _ 0 1 hM le_rfl zero_le_one)

/- English proof (translation)
The claim follows from `Mono.semipos_constShift (fsH_semipos P) (-Real.log C)`.
-/
theorem fsScaled_semipos (P : Ideal (MRing ι)) (C : ℝ) : IsSemipositiveRel ⊥ P (fsScaled ι C) :=
  Mono.semipos_constShift (fsH_semipos P) (-Real.log C)

/- English proof (translation)
Establish `hC0 : 0 < C` using `lt_of_lt_of_le zero_lt_one hC`. Establish `hBa` using `fsScaled_a ι C`. Set `e` to `Fintype.equivFin (∀ k, ι k)`. Set `w : Fin (Fintype.card (∀ k, ι k)) → MRing ι` to `fun j => ∏ k, (X ⟨k, e.symm j k⟩ : MRing ι) ^ (fun _ : K => (1 : ℕ)) k`. Use `SmallGenHeightsNonneg.proof K ι P (fsScaled ι C) II _ w hII (fsScaled_semipos P C).1 (fun k => by rw [hBa]; norm_num) (fun j => ?_) (fun Q hQ _ => ?_) (fun j z hz => ?_)` and prove the remaining obligations.

Establish `h` using `GroundTheory.Heights₂.Heights.Inter.ThmIUnique.isMultiHomog_coordMonomial (e.symm j) (fun _ : K => (1 : ℕ))`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Rewrite using `[hBa]`. Both sides reduce to the same expression.

Set `c : ∀ k, ι k` to `fun k => (hQ.2.2 k).choose`. Conclude with `⟨e c, by`. Simplify using `only [w, Equiv.symm_apply_apply]`. Conclude with `GroundTheory.Heights₂.Heights.Inter.ThmIUnique.coordMonomial_not_mem hQ.1 c (fun k => (hQ.2.2 k).choose_spec) _⟩`. Establish `hpos` using `(fsH ι).pos z hz.1`.

Establish `hlog` using `ScaledFSTopPos.logNorm_fsH_nonpos (e.symm j) hz.1`. Unfold `logNorm at hlog`. Rewrite `hlog` using `[Real.log_nonpos_iff (div_nonneg (norm_nonneg _) hpos.le), div_le_one hpos]`. Rewrite using `[fsScaled_h ι hC0]`. Conclude with `hlog.trans (le_mul_of_one_le_left hpos.le hC)`.
-/
theorem fsScaled_heightsNonneg (P : Ideal (MRing ι)) {C : ℝ} (hC : 1 ≤ C) (II : IntersectionSystem)
    (hII : IsIntersectionSystem II) : HeightsNonneg II P (fsScaled ι C) := by
  classical
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hBa := fsScaled_a ι C
  let e := Fintype.equivFin (∀ k, ι k)
  let w : Fin (Fintype.card (∀ k, ι k)) → MRing ι :=
    fun j => ∏ k, (X ⟨k, e.symm j k⟩ : MRing ι) ^ (fun _ : K => (1 : ℕ)) k
  refine SmallGenHeightsNonneg.proof K ι P (fsScaled ι C) II _ w hII (fsScaled_semipos P C).1
    (fun k => by rw [hBa]; norm_num) (fun j => ?_) (fun Q hQ _ => ?_) (fun j z hz => ?_)
  · have h := GroundTheory.Heights₂.Heights.Inter.ThmIUnique.isMultiHomog_coordMonomial (e.symm j) (fun _ : K => (1 : ℕ))
    convert h using 1
    funext k
    rw [hBa]
    rfl
  · let c : ∀ k, ι k := fun k => (hQ.2.2 k).choose
    exact ⟨e c, by
      simp only [w, Equiv.symm_apply_apply]
      exact GroundTheory.Heights₂.Heights.Inter.ThmIUnique.coordMonomial_not_mem hQ.1 c
        (fun k => (hQ.2.2 k).choose_spec) _⟩
  · have hpos := (fsH ι).pos z hz.1
    have hlog := ScaledFSTopPos.logNorm_fsH_nonpos (e.symm j) hz.1
    unfold logNorm at hlog
    rw [Real.log_nonpos_iff (div_nonneg (norm_nonneg _) hpos.le), div_le_one hpos] at hlog
    rw [fsScaled_h ι hC0]
    exact hlog.trans (le_mul_of_one_le_left hpos.le hC)

/- English proof (translation)
Introduce `K _ ι _ Ω _ y D II hII har hb C hC`. Use `set B := fsScaled ι C with hBdef`. Use `set F : ℝ := ((D + 1).factorial : ℝ) with hF`. Establish `hFpos : 0 < F` using `by rw [hF]; exact_mod_cast Nat.factorial_pos _`. Establish `hsemi : IsSemipositiveRel ⊥ (mCoordIdeal y) B` using `fsScaled_semipos _ C`.

Establish `hT` using `hHS K ι Ω y D B ⊥ II hII har hb bot_le hsemi (Mono.conj_constShift (fsH_isConjInvariantH ι) (-Real.log C)) (ProjLine.nefOnFibres_of_nonneg _ B.a fun k => by rw [hBdef, fsScaled_a]; norm_num) (NefOnGenericOfSemipos.proof K ι _ ⊥ B bot_le hsemi) (fsScaled_heightsNonneg _ hC II hII)`. Use `set L := II K ι (mCoordIdeal y) (D + 1) (fun _ => B) with hL`. Use `⟨(|L| + 1) / F, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hT.eventually (gt_mem_nhds (show L < L + 1 by linarith)), eventually_ge_atTop 1] with n hn hn1`. Establish `hnpos : (0 : ℝ) < n` using `by exact_mod_cast hn1`.

Establish `hm : (0 : ℝ) < (n : ℝ) ^ (D + 1) / F` using `by positivity`. Rewrite `hn` using `[div_lt_iff₀ hm]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem FSSmallCountBound.proof (hHS : MoriwakiHSStatement) : FSSmallCountBound.Statement := by
  intro K _ ι _ Ω _ y D II hII har hb C hC
  set B := fsScaled ι C with hBdef
  set F : ℝ := ((D + 1).factorial : ℝ) with hF
  have hFpos : 0 < F := by rw [hF]; exact_mod_cast Nat.factorial_pos _
  have hsemi : IsSemipositiveRel ⊥ (mCoordIdeal y) B := fsScaled_semipos _ C
  have hT := hHS K ι Ω y D B ⊥ II hII har hb bot_le hsemi
    (Mono.conj_constShift (fsH_isConjInvariantH ι) (-Real.log C))
    (ProjLine.nefOnFibres_of_nonneg _ B.a fun k => by rw [hBdef, fsScaled_a]; norm_num)
    (NefOnGenericOfSemipos.proof K ι _ ⊥ B bot_le hsemi)
    (fsScaled_heightsNonneg _ hC II hII)
  set L := II K ι (mCoordIdeal y) (D + 1) (fun _ => B) with hL
  refine ⟨(|L| + 1) / F, ?_⟩
  filter_upwards [hT.eventually (gt_mem_nhds (show L < L + 1 by linarith)), eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hm : (0 : ℝ) < (n : ℝ) ^ (D + 1) / F := by positivity
  rw [div_lt_iff₀ hm] at hn
  calc smallSectionCount (IsSmallH (mCoordIdeal y) y B) (chartLat y B.a) n
      ≤ (L + 1) * ((n : ℝ) ^ (D + 1) / F) := hn.le
    _ ≤ (|L| + 1) * ((n : ℝ) ^ (D + 1) / F) := by gcongr; exact le_abs_self L
    _ = (|L| + 1) / F * (n : ℝ) ^ (D + 1) := by ring

end

end GroundTheory.Heights₂.Heights.ForSecondHalf
