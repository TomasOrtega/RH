import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockBoundUniformiser
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Imports

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

/- English proof (translation)
Establish `hIn` using `realise hH aTop aPlus hT hP`. Establish `hm0 : 0 ≤ X.m` using `hH.2.2.2.2.2.2.2.2.1`. Establish `hm1 : X.m ≤ X.L.b' / (X.L.k * X.L.Q * X.L.Y)` using `hH.2.2.2.2.2.2.2.2.2`. Establish `h` using `h11 hH (realW X.L.TT X.j X.L.a aTop aPlus) hIn X.m hm0 hm1 dl.1 dl.2`. Rewrite `h` using `[rankOnDigits_eq, realW_top, realW_plus]`.

Conclude with `(h hc).2`.
-/
theorem rank_le {D : Formalism.BasicNotions.D7} {CYb Cde Ck CD Cb Cc : ℝ} (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X)
    (h11 : adm11 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X) (aTop : Fin X.s → ℕ) (aPlus : ℕ)
    (hT : aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA)) (hP : aPlus ∈ X.winA) (dl : DCl X)
    (hc : Compat C0 CE1 CE2 X dl aTop) :
    clSum C0 CE1 CE2 X (bRank C0 CE1 CE2 X aTop aPlus) aTop dl ≤ mCl C0 CE1 CE2 X dl aTop := by
  have hIn := realise hH aTop aPlus hT hP
  have hm0 : 0 ≤ X.m := hH.2.2.2.2.2.2.2.2.1
  have hm1 : X.m ≤ X.L.b' / (X.L.k * X.L.Q * X.L.Y) := hH.2.2.2.2.2.2.2.2.2
  have h := h11 hH (realW X.L.TT X.j X.L.a aTop aPlus) hIn X.m hm0 hm1 dl.1 dl.2
  rw [rankOnDigits_eq, realW_top, realW_plus] at h
  exact (h hc).2

/- English proof (translation)
Unfold `cbox`. Simplify using `only [Finset.mem_filter]`.
-/
theorem mem_cbox {dl : DCl X} {aTop : Fin X.s → ℕ} :
    aTop ∈ cbox C0 CE1 CE2 X dl ↔
      aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA) ∧ Compat C0 CE1 CE2 X dl aTop := by
  classical
  unfold cbox
  simp only [Finset.mem_filter]

/- English proof (translation)
Rewrite using `[clSum_eq_sum (kept_finite X.p X.r (X.S C0 CE1 CE2) aTop)]`. Unfold `idx keptSet`. Rewrite using `[Finset.sum_sigma]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem clSum_levels (dl : DCl X) (aTop : Fin X.s → ℕ) (f : SegBlock X.s X.r → Lv C0 CE1 CE2 X → ℕ) :
    ((clSum C0 CE1 CE2 X (fun b => ∑ x ∈ lv C0 CE1 CE2 X aTop b, f b x) aTop dl : ℕ) : ℝ) =
      ∑ z ∈ idx C0 CE1 CE2 X dl aTop, (f z.1 z.2 : ℝ) := by
  rw [clSum_eq_sum (kept_finite X.p X.r (X.S C0 CE1 CE2) aTop)]
  unfold idx keptSet
  rw [Finset.sum_sigma]
  push_cast
  rfl

/- English proof (translation)
Take `⟨aPlus, hP⟩` from `hW`. Take `⟨hT, hc⟩` from `mem_cbox.1 ha`. Rewrite using `[← clSum_levels dl aTop (fun b x => rL C0 CE1 CE2 X aTop b x)]`. Establish `h1 : clSum C0 CE1 CE2 X (fun b => ∑ x ∈ lv C0 CE1 CE2 X aTop b, rL C0 CE1 CE2 X aTop b x) aTop dl ≤ clSum C0 CE1 CE2 X (bRank C0 CE1 CE2 X aTop aPlus) aTop dl`. Rewrite using `[clSum_eq_sum (kept_finite X.p X.r (X.S C0 CE1 CE2) aTop), clSum_eq_sum (kept_finite X.p X.r (X.S C0 CE1 CE2) aTop)]`.

Use `Finset.sum_le_sum fun b hb => ?_` and prove the remaining obligations. Establish `hk : Kept X.p X.r (X.S C0 CE1 CE2) aTop b` using `(kept_finite X.p X.r (X.S C0 CE1 CE2) aTop).mem_toFinset.1 (Finset.mem_filter.1 hb).1`. Conclude with `hDir aTop hT aPlus hP b hk`. Conclude with `h1.trans (rank_le hH h11 aTop aPlus hT hP dl hc)` after adjusting the coercions.
-/
theorem claim2 {D : Formalism.BasicNotions.D7} {CYb Cde Ck CD Cb Cc : ℝ} (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X)
    (h11 : adm11 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X) (hDir : RestDir C0 CE1 CE2 X) (hW : X.winA.Nonempty)
    (dl : DCl X) (aTop : Fin X.s → ℕ) (ha : aTop ∈ cbox C0 CE1 CE2 X dl) :
    ∑ z ∈ idx C0 CE1 CE2 X dl aTop, (rL C0 CE1 CE2 X aTop z.1 z.2 : ℝ) ≤ (mCl C0 CE1 CE2 X dl aTop : ℝ) := by
  obtain ⟨aPlus, hP⟩ := hW
  obtain ⟨hT, hc⟩ := mem_cbox.1 ha
  rw [← clSum_levels dl aTop (fun b x => rL C0 CE1 CE2 X aTop b x)]
  have h1 : clSum C0 CE1 CE2 X (fun b => ∑ x ∈ lv C0 CE1 CE2 X aTop b, rL C0 CE1 CE2 X aTop b x) aTop dl ≤
      clSum C0 CE1 CE2 X (bRank C0 CE1 CE2 X aTop aPlus) aTop dl := by
    rw [clSum_eq_sum (kept_finite X.p X.r (X.S C0 CE1 CE2) aTop), clSum_eq_sum (kept_finite X.p X.r (X.S C0 CE1 CE2) aTop)]
    refine Finset.sum_le_sum fun b hb => ?_
    have hk : Kept X.p X.r (X.S C0 CE1 CE2) aTop b :=
      (kept_finite X.p X.r (X.S C0 CE1 CE2) aTop).mem_toFinset.1 (Finset.mem_filter.1 hb).1
    exact hDir aTop hT aPlus hP b hk
  exact_mod_cast h1.trans (rank_le hH h11 aTop aPlus hT hP dl hc)

/- English proof (translation)
Establish `hY : (1 : ℝ) ≤ X.L.Y` using `hH.1.1`. Establish `hY0 : (0 : ℝ) < X.L.Y` using `by linarith`. Introduce `dl hdl`. Establish `hbox : (CountingStatementReduction.box X).filter (fun a => Compat C0 CE1 CE2 X dl a.1) = cbox C0 CE1 CE2 X dl ×ˢ X.winA`. Use extensionality with `a`.

Simplify using `only [CountingStatementReduction.box, Finset.mem_filter, Finset.mem_product, mem_cbox]`. The claim follows by propositional logic. Rewrite using `[hbox, Finset.sum_product, Finset.sum_product]`. Establish `hR : ∑ aTop ∈ cbox C0 CE1 CE2 X dl, ∑ _aPlus ∈ X.winA, (mCl C0 CE1 CE2 X dl aTop : ℝ) = (X.winA.card : ℝ) * ∑ aTop ∈ cbox C0 CE1 CE2 X dl, (mCl C0 CE1 CE2 X dl aTop : ℝ)`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_const, nsmul_eq_mul]`. Rewrite using `[hR]`. Distinguish the cases in `hW : X.winA.Nonempty`. Use `swap`.

Rewrite `hW` using `[Finset.not_nonempty_iff_eq_empty]`. Simplify using `[hW]`. Distinguish the cases in `hA : (cbox C0 CE1 CE2 X dl).Nonempty`. Use `swap`. Rewrite `hA` using `[Finset.not_nonempty_iff_eq_empty]`.

Simplify using `[hA]`. Take `⟨a0, ha0⟩` from `hA`. Establish `hL : ∑ aTop ∈ cbox C0 CE1 CE2 X dl, ∑ aPlus ∈ X.winA, ((clSum C0 CE1 CE2 X (fun b => blockBadness C0 CE1 CE2 X aTop aPlus b ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋) aTop dl : ℕ) : ℝ) = ∑ aTop ∈ cbox C0 CE1 CE2 X dl, ∑ aPlus ∈ X.winA, ∑ z ∈ idx C0 CE1 CE2 X dl a0, (bLvl C0 CE1 CE2 X aTop aP …`. Use `Finset.sum_congr rfl fun aTop ha => Finset.sum_congr rfl fun aPlus _ => ?_` and prove the remaining obligations. Rewrite using `[← hFree dl hdl aTop ha a0 ha0]`.

Conclude with `clSum_levels dl aTop (fun b x => bLvl C0 CE1 CE2 X aTop aPlus b x ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋)`. Rewrite using `[hL]`. Establish `key` using `assemble (cbox C0 CE1 CE2 X dl) X.winA (idx C0 CE1 CE2 X dl a0) (Finset.univ : Finset (Fin (X.S C0 CE1 CE2).t)) (fun aTop aPlus z => (bLvl C0 CE1 CE2 X aTop aPlus z.1 z.2 ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℝ)) (fun aTop z => (bY C0 CE1 CE2 X aTop z.1 z.2 ⌊D1r C0 CE1 CE2 X CM⌋ : ℝ)) …`. Rewrite `key` using `[Finset.card_univ, Fintype.card_fin]`. Conclude with `key`.

Introduce `aTop ha z hz`. Establish `h` using `hPlus dl hdl aTop ha z (by rw [hFree dl hdl aTop ha a0 ha0]; exact hz)`. Establish `e : (rL C0 CE1 CE2 X aTop z.1 z.2 : ℝ) = (dimY X.p (r` using `X.r) (gB C0 CE1 CE2 X aTop 0 z.1) z.2.1 z.2.2 : ℝ) * (dXi X.r ((X.S C0 CE1 CE2).bPlus - z.2.2) : ℝ) := by`. Unfold `rL`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite `h` using `[e]`. Conclude with `h`. Introduce `z hz`. Conclude with `hTM dl hdl a0 ha0 z hz`.

Introduce `aTop ha`. Establish `h` using `claim2 hH h11 hDir hW dl aTop ha`. Rewrite `h` using `[hFree dl hdl aTop ha a0 ha0]`. Use `le_trans (le_of_eq ?_) h` and prove the remaining obligations. Use `Finset.sum_congr rfl fun z _ => ?_` and prove the remaining obligations.

Unfold `rL`. Use `push_cast`. Both sides reduce to the same expression. Introduce `aTop ha i _`. Conclude with `hRat dl hdl aTop ha i`.
-/
theorem digit_class_dimension_comparison_of_remaining_estimates {D : Formalism.BasicNotions.D7} {CYb Cde Ck CD Cb Cc : ℝ} (CM : ℝ) (hCM : 0 ≤ CM)
    (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) (h11 : adm11 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X)
    (hPlus : RestPlus C0 CE1 CE2 X CM) (hTM : RestTM C0 CE1 CE2 X CM) (hDir : RestDir C0 CE1 CE2 X)
    (hFree : RestFree C0 CE1 CE2 X) (hRat : RestRatio C0 CE1 CE2 X) :
    DigitClassDimensionComparison C0 CE1 CE2 X (fun aTop aPlus b => blockBadness C0 CE1 CE2 X aTop aPlus b ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋)
      ((30 + CM) / X.L.Y * ((X.S C0 CE1 CE2).t : ℝ) * Real.exp 3 + 5 / X.L.Y) := by
  classical
  have hY : (1 : ℝ) ≤ X.L.Y := hH.1.1
  have hY0 : (0 : ℝ) < X.L.Y := by linarith
  intro dl hdl
  have hbox : (CountingStatementReduction.box X).filter (fun a => Compat C0 CE1 CE2 X dl a.1) = cbox C0 CE1 CE2 X dl ×ˢ X.winA := by
    ext a
    simp only [CountingStatementReduction.box, Finset.mem_filter, Finset.mem_product, mem_cbox]
    tauto
  rw [hbox, Finset.sum_product, Finset.sum_product]
  have hR : ∑ aTop ∈ cbox C0 CE1 CE2 X dl, ∑ _aPlus ∈ X.winA, (mCl C0 CE1 CE2 X dl aTop : ℝ) =
      (X.winA.card : ℝ) * ∑ aTop ∈ cbox C0 CE1 CE2 X dl, (mCl C0 CE1 CE2 X dl aTop : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hR]
  by_cases hW : X.winA.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty] at hW
    simp [hW]
  by_cases hA : (cbox C0 CE1 CE2 X dl).Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty] at hA
    simp [hA]
  obtain ⟨a0, ha0⟩ := hA
  have hL : ∑ aTop ∈ cbox C0 CE1 CE2 X dl, ∑ aPlus ∈ X.winA,
        ((clSum C0 CE1 CE2 X (fun b => blockBadness C0 CE1 CE2 X aTop aPlus b ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋) aTop dl : ℕ) : ℝ) =
      ∑ aTop ∈ cbox C0 CE1 CE2 X dl, ∑ aPlus ∈ X.winA, ∑ z ∈ idx C0 CE1 CE2 X dl a0,
        (bLvl C0 CE1 CE2 X aTop aPlus z.1 z.2 ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℝ) := by
    refine Finset.sum_congr rfl fun aTop ha => Finset.sum_congr rfl fun aPlus _ => ?_
    rw [← hFree dl hdl aTop ha a0 ha0]
    exact clSum_levels dl aTop (fun b x => bLvl C0 CE1 CE2 X aTop aPlus b x ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋)
  rw [hL]
  have key := assemble (cbox C0 CE1 CE2 X dl) X.winA (idx C0 CE1 CE2 X dl a0)
    (Finset.univ : Finset (Fin (X.S C0 CE1 CE2).t))
    (fun aTop aPlus z => (bLvl C0 CE1 CE2 X aTop aPlus z.1 z.2 ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℝ))
    (fun aTop z => (bY C0 CE1 CE2 X aTop z.1 z.2 ⌊D1r C0 CE1 CE2 X CM⌋ : ℝ))
    (fun z => (dXi X.r ((X.S C0 CE1 CE2).bPlus - z.2.2) : ℝ))
    (fun aTop z => (dimY X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 z.1) z.2.1 z.2.2 : ℝ))
    (fun aTop i => upd C0 CE1 CE2 X dl aTop i)
    (fun aTop => (mCl C0 CE1 CE2 X dl aTop : ℝ))
    ((30 + CM) / X.L.Y) (5 / X.L.Y) (Real.exp 3) (by positivity) (by positivity) (fun z => Nat.cast_nonneg _)
    ?_ ?_ ?_ ?_
  · rw [Finset.card_univ, Fintype.card_fin] at key
    exact key
  · intro aTop ha z hz
    have h := hPlus dl hdl aTop ha z (by rw [hFree dl hdl aTop ha a0 ha0]; exact hz)
    have e : (rL C0 CE1 CE2 X aTop z.1 z.2 : ℝ) =
        (dimY X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 z.1) z.2.1 z.2.2 : ℝ) *
          (dXi X.r ((X.S C0 CE1 CE2).bPlus - z.2.2) : ℝ) := by
      unfold rL
      push_cast
      rfl
    rw [e] at h
    exact h
  · intro z hz
    exact hTM dl hdl a0 ha0 z hz
  · intro aTop ha
    have h := claim2 hH h11 hDir hW dl aTop ha
    rw [hFree dl hdl aTop ha a0 ha0] at h
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun z _ => ?_
    unfold rL
    push_cast
    rfl
  · intro aTop ha i _
    exact hRat dl hdl aTop ha i

def RestAll (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM C : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    BlockBoundUniformiser C0 CE1 CE2 X ∧ RestPlus C0 CE1 CE2 X CM ∧ RestTM C0 CE1 CE2 X CM ∧ RestDir C0 CE1 CE2 X ∧
      RestFree C0 CE1 CE2 X ∧ RestRatio C0 CE1 CE2 X ∧ RestDepth C0 CE1 CE2 X CM C

/- English proof (translation)
Introduce `hH _`. Take `⟨hBlk, hPlus, hTM, hDir, hFree, hRat, hD0, hDep⟩` from `hR hH`. Establish `hY : (1 : ℝ) ≤ X.L.Y` using `hH.1.1`. Establish `hY0 : (0 : ℝ) < X.L.Y` using `by linarith`. Establish `hN : (1 : ℝ) ≤ (X.N₁ : ℝ)` using `by exact_mod_cast hH.1.2.2.2.2.2.1`.

Establish `ht : (0 : ℝ) ≤ ((X.S C0 CE1 CE2).t : ℝ)` using `Nat.cast_nonneg _`. Establish `he : (0 : ℝ) < Real.exp 3` using `Real.exp_pos 3`. Use `⟨fun aTop aPlus b => blockBadness C0 CE1 CE2 X aTop aPlus b ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋, (30 + CM) / X.L.Y * ((X.S C0 CE1 CE2).t : ℝ) * Real.exp 3 + 5 / X.L.Y, by positivity, ?_, ?_, digit_class_dimension_comparison_of_remaining_estimates CM hCM hH h11 hPlus hTM hDir hFree hRat …` and prove the remaining obligations. Establish `e1 : 2 * ((30 + CM) / X.L.Y * ((X.S C0 CE1 CE2).t : ℝ) * Real.exp 3 + 5 / X.L.Y) * Real.exp 3 = 2 * ((30 + CM) * ((X.S C0 CE1 CE2).t : ℝ) * Real.exp 3 + 5) * Real.exp 3 / X.L.Y`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e1]`. Apply `div_le_div_of_nonneg_right _ hY0.le` to reduce the goal to its premises. Establish `h1 : (30 + CM) * ((X.S C0 CE1 CE2).t : ℝ) * Real.exp 3 + 5 ≤ ((30 + CM) * Real.exp 3 + 5) * (((X.S C0 CE1 CE2).t : ℝ) + 1)`. Establish `: 0 ≤ (30 + CM) * Real.exp 3` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.

Establish `h2 : 0 ≤ (30 + CM) * Real.exp 3 + 5` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_right _ he.le` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = (2 * ((30 + CM) * Real.exp 3 + 5) * Real.exp 3) * (((X.S C0 CE1 CE2).t : ℝ) + 1) := by ring`.

Use `_ ≤ C * (((X.S C0 CE1 CE2).t : ℝ) + 1) := mul_le_mul_of_nonneg_right hC (by linarith)`. Use `_ ≤ C * (((X.S C0 CE1 CE2).t : ℝ) + 1) * X.N₁ := by`. Establish `: 0 ≤ C * (((X.S C0 CE1 CE2).t : ℝ) + 1)` using `mul_nonneg (le_trans (by positivity) hC) (by linarith)`. Use the polynomial consequences of the given equalities and inequalities. Introduce `aTop hT aPlus hP b hk`.

Establish `h0 : (0 : ℤ) ≤ ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋` using `Int.floor_nonneg.2 (mul_nonneg hY0.le hD0)`. Take `⟨L₂, hg, hr⟩` from `hBlk aTop hT aPlus hP b hk _ h0`. Use `⟨L₂, GoodSub_mono ?_ hg, hr⟩` and prove the remaining obligations. Use `Int.floor_le (X.L.Y * D1r C0 CE1 CE2 X CM)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem segment_weighted_counting_bound_of_all_remaining_bounds (D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM C : ℝ) (X : flipOneThree.Inst) (hCM : 0 ≤ CM)
    (hC : 2 * ((30 + CM) * Real.exp 3 + 5) * Real.exp 3 ≤ C)
    (h11 : adm11 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X)
    (hR : RestAll C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM C X) : SegmentWeightedCountingBound C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X := by
  intro hH _
  obtain ⟨hBlk, hPlus, hTM, hDir, hFree, hRat, hD0, hDep⟩ := hR hH
  have hY : (1 : ℝ) ≤ X.L.Y := hH.1.1
  have hY0 : (0 : ℝ) < X.L.Y := by linarith
  have hN : (1 : ℝ) ≤ (X.N₁ : ℝ) := by exact_mod_cast hH.1.2.2.2.2.2.1
  have ht : (0 : ℝ) ≤ ((X.S C0 CE1 CE2).t : ℝ) := Nat.cast_nonneg _
  have he : (0 : ℝ) < Real.exp 3 := Real.exp_pos 3
  refine ⟨fun aTop aPlus b => blockBadness C0 CE1 CE2 X aTop aPlus b ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋,
    (30 + CM) / X.L.Y * ((X.S C0 CE1 CE2).t : ℝ) * Real.exp 3 + 5 / X.L.Y, by positivity, ?_, ?_,
    digit_class_dimension_comparison_of_remaining_estimates CM hCM hH h11 hPlus hTM hDir hFree hRat⟩
  · have e1 : 2 * ((30 + CM) / X.L.Y * ((X.S C0 CE1 CE2).t : ℝ) * Real.exp 3 + 5 / X.L.Y) * Real.exp 3 =
        2 * ((30 + CM) * ((X.S C0 CE1 CE2).t : ℝ) * Real.exp 3 + 5) * Real.exp 3 / X.L.Y := by
      field_simp
    rw [e1]
    apply div_le_div_of_nonneg_right _ hY0.le
    have h1 : (30 + CM) * ((X.S C0 CE1 CE2).t : ℝ) * Real.exp 3 + 5 ≤
        ((30 + CM) * Real.exp 3 + 5) * (((X.S C0 CE1 CE2).t : ℝ) + 1) := by
      have : 0 ≤ (30 + CM) * Real.exp 3 := by positivity
      nlinarith
    have h2 : 0 ≤ (30 + CM) * Real.exp 3 + 5 := by positivity
    calc 2 * ((30 + CM) * ((X.S C0 CE1 CE2).t : ℝ) * Real.exp 3 + 5) * Real.exp 3
        ≤ 2 * (((30 + CM) * Real.exp 3 + 5) * (((X.S C0 CE1 CE2).t : ℝ) + 1)) * Real.exp 3 := by
          apply mul_le_mul_of_nonneg_right _ he.le
          linarith
      _ = (2 * ((30 + CM) * Real.exp 3 + 5) * Real.exp 3) * (((X.S C0 CE1 CE2).t : ℝ) + 1) := by ring
      _ ≤ C * (((X.S C0 CE1 CE2).t : ℝ) + 1) := mul_le_mul_of_nonneg_right hC (by linarith)
      _ ≤ C * (((X.S C0 CE1 CE2).t : ℝ) + 1) * X.N₁ := by
          have : 0 ≤ C * (((X.S C0 CE1 CE2).t : ℝ) + 1) :=
            mul_nonneg (le_trans (by positivity) hC) (by linarith)
          nlinarith
  · intro aTop hT aPlus hP b hk
    have h0 : (0 : ℤ) ≤ ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ := Int.floor_nonneg.2 (mul_nonneg hY0.le hD0)
    obtain ⟨L₂, hg, hr⟩ := hBlk aTop hT aPlus hP b hk _ h0
    refine ⟨L₂, GoodSub_mono ?_ hg, hr⟩
    have := Int.floor_le (X.L.Y * D1r C0 CE1 CE2 X CM)
    linarith

def RestAllE (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs : ℝ, ∃ CM C : ℝ, 0 ≤ CM ∧ 1 ≤ C ∧
    2 * ((30 + CM) * Real.exp 3 + 5) * Real.exp 3 ≤ C ∧
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X →
      RestAll C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM C X

/- English proof (translation)
The claim follows from `thr_mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc h1 Ckap Cs => by obtain ⟨CM, C, hCM, hC1, hC, h2⟩ := h1 Ckap Cs exact ⟨C, hC1, fun X hA => segment_weighted_counting_bound_of_all_remaining_bounds D C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM C X hCM hC hA.2.2.2.2.2.2 (h2 X hA)⟩) h`.
-/
theorem rest1DAE_of (D : Formalism.BasicNotions.D7) (h : RestAllE D) : DigitClassRemainingUniform D :=
  thr_mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc h1 Ckap Cs => by
    obtain ⟨CM, C, hCM, hC1, hC, h2⟩ := h1 Ckap Cs
    exact ⟨C, hC1, fun X hA =>
      segment_weighted_counting_bound_of_all_remaining_bounds D C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM C X hCM hC hA.2.2.2.2.2.2 (h2 X hA)⟩) h

/- English proof (translation)
The claim follows from `counting_statement_uniform_of_digit_class D (rest1DAE_of D h)`.
-/
theorem theorem_A_closed_of_all_remaining_bounds (D : Formalism.BasicNotions.D7) (h : RestAllE D) : IntegralityFromMetricForLargeConstants D :=
  counting_statement_uniform_of_digit_class D (rest1DAE_of D h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
