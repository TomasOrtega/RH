import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.CoarseCLower

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section Chain

variable {s : ℕ} {p r : ℕ} (S : SegData s) (aTop : Fin s → ℕ) (b : SegBlock s r)

/- English proof (translation)
Establish `hu'` using `u.isLt`. Establish `hne : (x : ℕ) ≠ 2 * s` using `by omega`. Establish `ht : topOf x hne = u` using `Fin.ext (by simp [topOf]; omega)`. Simplify using `only [segChain]`. Rewrite using `[dif_neg hne, if_pos (by omega), ht, if_neg (by omega)]`.
-/
theorem segChain_deg_even (x : Fin (2 * s + 1)) (u : Fin s) (hx : (x : ℕ) = 2 * (u : ℕ)) (hu : S.sigma ≤ (u : ℕ)) :
    (segChain p S aTop b).deg x = b.o u := by
  have hu' := u.isLt
  have hne : (x : ℕ) ≠ 2 * s := by omega
  have ht : topOf x hne = u := Fin.ext (by simp [topOf]; omega)
  simp only [segChain]
  rw [dif_neg hne, if_pos (by omega), ht, if_neg (by omega)]

/- English proof (translation)
Establish `hu'` using `u.isLt`. Establish `hne : (x : ℕ) ≠ 2 * s` using `by omega`. Establish `ht : topOf x hne = u` using `Fin.ext (by simp [topOf]; omega)`. Simplify using `only [segChain]`. Rewrite using `[dif_neg hne, if_neg (by omega), ht, if_neg (by omega)]`.
-/
theorem segChain_deg_odd (x : Fin (2 * s + 1)) (u : Fin s) (hx : (x : ℕ) = 2 * (u : ℕ) + 1)
    (hu : S.sigma ≤ (u : ℕ)) : (segChain p S aTop b).deg x = coarseC p S aTop b u := by
  have hu' := u.isLt
  have hne : (x : ℕ) ≠ 2 * s := by omega
  have ht : topOf x hne = u := Fin.ext (by simp [topOf]; omega)
  simp only [segChain]
  rw [dif_neg hne, if_neg (by omega), ht, if_neg (by omega)]

/- English proof (translation)
Simplify using `only [segChain]`. Rewrite using `[dif_pos hx]`.
-/
theorem segChain_deg_last (x : Fin (2 * s + 1)) (hx : (x : ℕ) = 2 * s) : (segChain p S aTop b).deg x = b.oPlus := by
  simp only [segChain]
  rw [dif_pos hx]

end Chain

/- English proof (translation)
Simplify using `only [levels, Finset.mem_filter]`. Prove the components needed by the constructor for the conclusion. Conclude with `fun h => h.2`. Introduce `h`. Use `⟨?_, h⟩` and prove the remaining obligations.

Rewrite using `[Finset.mem_product, Fintype.mem_piFinset]`. Use `⟨fun i => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.mem_range, Nat.lt_succ_iff]`. Conclude with `(h.1 i).1.trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))`. Rewrite using `[Finset.mem_range, Nat.lt_succ_iff]`.

Conclude with `h.2.trans (min_le_right _ _)`.
-/
theorem mem_levels_iff {N : ℕ} (G : Formalism.GM.M.BlockData N) (x : (Fin G.T.t → ℕ) × ℕ) :
    x ∈ levels G ↔ G.LevelOK x.1 x.2 := by
  simp only [levels, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rw [Finset.mem_product, Fintype.mem_piFinset]
    refine ⟨fun i => ?_, ?_⟩
    · rw [Finset.mem_range, Nat.lt_succ_iff]
      exact (h.1 i).1.trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))
    · rw [Finset.mem_range, Nat.lt_succ_iff]
      exact h.2.trans (min_le_right _ _)

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

/- English proof (translation)
Simplify using `only [uTop]`. Use linear arithmetic over natural numbers and integers.
-/
theorem uTop_ge (i : Fin (X.S C0 CE1 CE2).t) : (X.S C0 CE1 CE2).sigma ≤ ((uTop (X.S C0 CE1 CE2) i : Fin X.s) : ℕ) := by
  simp only [uTop]
  omega

/- English proof (translation)
Simplify using `only [Formalism.GM.M.BlockData.LevelOK, gB, gmB, blockData, BlockData.withMargin, blockBase, gmL, gmT, segTies]`. Use `and_congr (forall_congr' fun i => ?_) ?_` and prove the remaining obligations. Establish `hi` using `(uTop (X.S C0 CE1 CE2) i).isLt`. Rewrite using `[segChain_deg_even (X.S C0 CE1 CE2) aTop b ⟨min (2 * ((uTop (X.S C0 CE1 CE2) i : Fin X.s) : ℕ)) (2 * X.s + 1 - 1), by omega⟩ (uTop _ i) (by simp only; omega) (uTop_ge i), segChain_deg_odd (X.S C0 CE1 CE2) aTop b ⟨min (2 * ((uTop (X.S C0 CE1 CE2) i : Fin X.s) : ℕ) + 1) (2 * X.s + …`. Rewrite using `[segChain_deg_last (X.S C0 CE1 CE2) aTop b ⟨2 * X.s, by omega⟩ rfl]`.
-/
theorem levelOK_gB (aTop : Fin X.s → ℕ) (aPlus : ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) :
    (gB C0 CE1 CE2 X aTop aPlus b).LevelOK x.1 x.2 ↔
      (∀ i : Fin (X.S C0 CE1 CE2).t, x.1 i ≤ b.o (uTop (X.S C0 CE1 CE2) i) ∧
        x.1 i ≤ coarseC X.p (X.S C0 CE1 CE2) aTop b (uTop (X.S C0 CE1 CE2) i)) ∧
      x.2 ≤ min b.oPlus (X.S C0 CE1 CE2).bPlus := by
  simp only [Formalism.GM.M.BlockData.LevelOK, gB, gmB, blockData, BlockData.withMargin, blockBase, gmL, gmT, segTies]
  refine and_congr (forall_congr' fun i => ?_) ?_
  · have hi := (uTop (X.S C0 CE1 CE2) i).isLt
    rw [segChain_deg_even (X.S C0 CE1 CE2) aTop b
        ⟨min (2 * ((uTop (X.S C0 CE1 CE2) i : Fin X.s) : ℕ)) (2 * X.s + 1 - 1), by omega⟩ (uTop _ i)
        (by simp only; omega) (uTop_ge i),
      segChain_deg_odd (X.S C0 CE1 CE2) aTop b
        ⟨min (2 * ((uTop (X.S C0 CE1 CE2) i : Fin X.s) : ℕ) + 1) (2 * X.s + 1 - 1), by omega⟩ (uTop _ i)
        (by simp only; omega) (uTop_ge i)]
  · rw [segChain_deg_last (X.S C0 CE1 CE2) aTop b ⟨2 * X.s, by omega⟩ rfl]

/- English proof (translation)
The claim follows from `(mem_levels_iff (gB C0 CE1 CE2 X aTop 0 b) x).trans (levelOK_gB aTop 0 b x)`.
-/
theorem mem_lv (aTop : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) :
    x ∈ lv C0 CE1 CE2 X aTop b ↔
      (∀ i : Fin (X.S C0 CE1 CE2).t, x.1 i ≤ b.o (uTop (X.S C0 CE1 CE2) i) ∧
        x.1 i ≤ coarseC X.p (X.S C0 CE1 CE2) aTop b (uTop (X.S C0 CE1 CE2) i)) ∧
      x.2 ≤ min b.oPlus (X.S C0 CE1 CE2).bPlus :=
  (mem_levels_iff (gB C0 CE1 CE2 X aTop 0 b) x).trans (levelOK_gB aTop 0 b x)

/- English proof (translation)
Substitute `hb` using the available equality. Simplify `hc` using `only [Compat, DigitsOK, ColumnSystems.digitBlock]`.
-/
theorem digitsOK_of_compat {dl : DCl X} {aTop : Fin X.s → ℕ} (hc : Compat C0 CE1 CE2 X dl aTop)
    (b : SegBlock X.s X.r) (hb : (b.rz, b.ry) = dl) : DigitsOK X.p (X.S C0 CE1 CE2) aTop b := by
  subst hb
  simpa only [Compat, DigitsOK, ColumnSystems.digitBlock] using hc

/- English proof (translation)
Simplify using `only [cbox, Finset.mem_filter] at ha`. Conclude with `ha`.
-/
theorem mem_cbox' {dl : DCl X} {aTop : Fin X.s → ℕ} (ha : aTop ∈ cbox C0 CE1 CE2 X dl) :
    aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA) ∧ Compat C0 CE1 CE2 X dl aTop := by
  simp only [cbox, Finset.mem_filter] at ha
  exact ha

/- English proof (translation)
Use `haveI : NeZero X.r := ⟨X.hm⟩`. Establish `hF` using `hS.hF`. Establish `hwin : ∀ i, X.L.a ≤ aTop' i` using `fun i => (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp (mem_cbox' ha').1 i)).1`. Establish `hp : (25:ℝ) ≤ X.L.p`. Establish `h1` using `hF.p_ge`.

Establish `h2 : (4:ℝ) ≤ X.L.m` using `by exact_mod_cast hF.m4`. Use the polynomial consequences of the given equalities and inequalities. Establish `hb0` using `hF.b0`. Establish `hblt` using `hF.b_lt`. Establish `h25 : 25 * X.L.b' < X.L.a` using `by nlinarith`.

Introduce and unpack `⟨b, x⟩ hbx`. Simplify using `only [idx, Finset.mem_sigma, Finset.mem_filter] at hbx ⊢`. Take `⟨⟨hk, hdl⟩, hx⟩` from `hbx`. Rewrite `hk`, the goal using `[mem_keptSet]`. Establish `hD'` using `digitsOK_of_compat (mem_cbox' ha').2 b hdl`.

Establish `hsum : ∀ i, ((∑ c, b.ry i c : ℕ) : ℝ) < X.L.b'`. Introduce `i`. Establish `h1 : ∑ c, b.ry i c < ∑ _c : Fin (X.r + 1), SegData.P X.p (X.S C0 CE1 CE2) i` using `Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun c _ => (hD'.1 i c).2)`. Rewrite `h1` using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]`. Establish `h2` using `hS.kP i`.

Establish `h3 : ((∑ c, b.ry i c : ℕ) : ℝ) < (((X.r + 1) * SegData.P X.p (X.S C0 CE1 CE2) i : ℕ) : ℝ)`. Conclude with `h1` after adjusting the coercions. Move the coercions through the operations in `at h3 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hC : ∀ i, (coarseC X.p (X.S C0 CE1 CE2) aTop' b i : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) = (aTop' i : ℝ) - ((∑ c, b.ry i c : ℕ) : ℝ)`.

Introduce `i`. Establish `h1` using `Nat.div_mul_cancel (hD'.2.2 i).2`. Establish `h2` using `(hD'.2.2 i).1`. Unfold `coarseC`. Rewrite using `[← Nat.cast_sub h2, ← Nat.cast_mul, h1]`.

Establish `hAC : ∀ i, coarseA X.p (X.S C0 CE1 CE2) b i ≤ coarseC X.p (X.S C0 CE1 CE2) aTop' b i`. Introduce `i`. Establish `h1` using `hS.bTop i`. Establish `h2` using `hsum i`. Establish `h3 : (X.L.a : ℝ) ≤ aTop' i` using `by exact_mod_cast hwin i`.

Establish `h4 : (((X.S C0 CE1 CE2).bTop i + ∑ c, b.ry i c : ℕ) : ℝ) < aTop' i`. Move the coercions through the operations in `at h2 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h5 : (X.S C0 CE1 CE2).bTop i + ∑ c, b.ry i c < aTop' i` using `by exact_mod_cast h4`. Unfold `coarseA coarseC`.

Conclude with `Nat.div_le_div_right (by omega)`. Establish `hSG : ∀ i, ((b.sg i : ℕ) : ℝ) ≤ 2 * (X.S C0 CE1 CE2).La * ((SegData.A0 X.p (X.S C0 CE1 CE2) : ℤ) : ℝ) / ((X.r : ℝ) + 1) → b.sg i ≤ coarseC X.p (X.S C0 CE1 CE2) aTop' b i`. Introduce `i h`. Establish `hP1 : (1:ℝ) ≤ (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ)` using `by exact_mod_cast hS.P1 i`. Establish `hPQ : (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) ≤ (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ)`.

Conclude with `hS.PQ i` after adjusting the coercions. Establish `hQ : (0:ℝ) < (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ)` using `by linarith`. Establish `hA : ((SegData.A0 X.p (X.S C0 CE1 CE2) : ℤ) : ℝ) ≤ (X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ)`. Establish `h1` using `Int.floor_le ((((X.S C0 CE1 CE2).a : ℝ) - (X.S C0 CE1 CE2).E0) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ))`. Establish `h2` using `hS.E0`.

Establish `h3 : (((X.S C0 CE1 CE2).a : ℝ) - (X.S C0 CE1 CE2).E0) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ) ≤ (X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ)`. Apply `div_le_div_of_nonneg_right _ hQ.le` to reduce the goal to its premises. Use `show (X.L.a : ℝ) - (X.S C0 CE1 CE2).E0 ≤ X.L.a`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `h1.trans h3`.

Establish `hLa0 : 0 ≤ (X.S C0 CE1 CE2).La` using `hF.La0`. Establish `hLa4 : 4 * (X.S C0 CE1 CE2).La < (X.r : ℝ) + 1` using `hS.La4`. Establish `hr : (0:ℝ) < (X.r : ℝ) + 1` using `by positivity`. Establish `hq0 : 0 ≤ (X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ)` using `by positivity`. Establish `e1 : 2 * (X.S C0 CE1 CE2).La * ((SegData.A0 X.p (X.S C0 CE1 CE2) : ℤ) : ℝ) / ((X.r : ℝ) + 1) ≤ 2 * (X.S C0 CE1 CE2).La * ((X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ)) / ((X.r : ℝ) + 1)` using `div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hA (by linarith)) hr.le`.

Establish `e2 : 2 * (X.S C0 CE1 CE2).La * ((X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ)) / ((X.r : ℝ) + 1) ≤ ((X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ)) / 2`. Rewrite using `[div_le_div_iff₀ hr (by norm_num)]`. Use the polynomial consequences of the given equalities and inequalities. Establish `e3 : ((b.sg i : ℕ) : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) ≤ (X.L.a : ℝ) / 2`. Establish `h0 : ((b.sg i : ℕ) : ℝ) ≤ ((X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ)) / 2` using `h.trans (e1.trans e2)`.

Combine the equalities or inequalities in the displayed calculation. Establish `e4 : (X.L.a : ℝ) - X.L.b' < (aTop' i : ℝ) - ((∑ c, b.ry i c : ℕ) : ℝ)`. Establish `h1` using `hsum i`. Establish `h2 : (X.L.a : ℝ) ≤ aTop' i` using `by exact_mod_cast hwin i`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `e5 : ((b.sg i : ℕ) : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) < (coarseC X.p (X.S C0 CE1 CE2) aTop' b i : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ)`. Rewrite using `[hC i]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e6 : ((b.sg i : ℕ) : ℝ) < (coarseC X.p (X.S C0 CE1 CE2) aTop' b i : ℝ)` using `lt_of_mul_lt_mul_right e5 (by linarith)`. Conclude with `e6.le` after adjusting the coercions.

Use `⟨⟨⟨hD', hk.2.1, fun i hi => ?_, hk.2.2.2⟩, hdl⟩, ?_⟩` and prove the remaining obligations. Take `⟨h1, h2, _, h4, h5⟩` from `hk.2.2.1 i hi`. Conclude with `⟨h1, h2, hSG i h5, h4, h5⟩`. Establish `hx'` using `(mem_lv aTop b x).mp hx`. Use `(mem_lv aTop' b x).mpr ⟨fun i => ⟨(hx'.1 i).1, ?_⟩, hx'.2⟩` and prove the remaining obligations.

Conclude with `(hx'.1 i).1.trans (((hk.2.1 _ (uTop_ge i)).1).trans (hAC _))`.
-/
theorem idx_sub (hS : SegFacts C0 CE1 CE2 X) (dl : DCl X) (aTop aTop' : Fin X.s → ℕ)
    (ha : aTop ∈ cbox C0 CE1 CE2 X dl) (ha' : aTop' ∈ cbox C0 CE1 CE2 X dl) :
    idx C0 CE1 CE2 X dl aTop ⊆ idx C0 CE1 CE2 X dl aTop' := by
  haveI : NeZero X.r := ⟨X.hm⟩
  have hF := hS.hF
  have hwin : ∀ i, X.L.a ≤ aTop' i := fun i =>
    (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp (mem_cbox' ha').1 i)).1
  have hp : (25:ℝ) ≤ X.L.p := by
    have h1 := hF.p_ge
    have h2 : (4:ℝ) ≤ X.L.m := by exact_mod_cast hF.m4
    nlinarith
  have hb0 := hF.b0
  have hblt := hF.b_lt
  have h25 : 25 * X.L.b' < X.L.a := by nlinarith
  rintro ⟨b, x⟩ hbx
  simp only [idx, Finset.mem_sigma, Finset.mem_filter] at hbx ⊢
  obtain ⟨⟨hk, hdl⟩, hx⟩ := hbx
  rw [mem_keptSet] at hk ⊢
  have hD' := digitsOK_of_compat (mem_cbox' ha').2 b hdl
  have hsum : ∀ i, ((∑ c, b.ry i c : ℕ) : ℝ) < X.L.b' := by
    intro i
    have h1 : ∑ c, b.ry i c < ∑ _c : Fin (X.r + 1), SegData.P X.p (X.S C0 CE1 CE2) i :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun c _ => (hD'.1 i c).2)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
    have h2 := hS.kP i
    have h3 : ((∑ c, b.ry i c : ℕ) : ℝ) < (((X.r + 1) * SegData.P X.p (X.S C0 CE1 CE2) i : ℕ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h3 ⊢
    linarith
  have hC : ∀ i, (coarseC X.p (X.S C0 CE1 CE2) aTop' b i : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) =
      (aTop' i : ℝ) - ((∑ c, b.ry i c : ℕ) : ℝ) := by
    intro i
    have h1 := Nat.div_mul_cancel (hD'.2.2 i).2
    have h2 := (hD'.2.2 i).1
    unfold coarseC
    rw [← Nat.cast_sub h2, ← Nat.cast_mul, h1]
  have hAC : ∀ i, coarseA X.p (X.S C0 CE1 CE2) b i ≤ coarseC X.p (X.S C0 CE1 CE2) aTop' b i := by
    intro i
    have h1 := hS.bTop i
    have h2 := hsum i
    have h3 : (X.L.a : ℝ) ≤ aTop' i := by exact_mod_cast hwin i
    have h4 : (((X.S C0 CE1 CE2).bTop i + ∑ c, b.ry i c : ℕ) : ℝ) < aTop' i := by
      push_cast at h2 ⊢
      linarith
    have h5 : (X.S C0 CE1 CE2).bTop i + ∑ c, b.ry i c < aTop' i := by exact_mod_cast h4
    unfold coarseA coarseC
    exact Nat.div_le_div_right (by omega)
  have hSG : ∀ i, ((b.sg i : ℕ) : ℝ) ≤ 2 * (X.S C0 CE1 CE2).La *
      ((SegData.A0 X.p (X.S C0 CE1 CE2) : ℤ) : ℝ) / ((X.r : ℝ) + 1) →
      b.sg i ≤ coarseC X.p (X.S C0 CE1 CE2) aTop' b i := by
    intro i h
    have hP1 : (1:ℝ) ≤ (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) := by exact_mod_cast hS.P1 i
    have hPQ : (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) ≤ (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ) := by
      exact_mod_cast hS.PQ i
    have hQ : (0:ℝ) < (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ) := by linarith
    have hA : ((SegData.A0 X.p (X.S C0 CE1 CE2) : ℤ) : ℝ) ≤ (X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ) := by
      have h1 := Int.floor_le ((((X.S C0 CE1 CE2).a : ℝ) - (X.S C0 CE1 CE2).E0) /
        (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ))
      have h2 := hS.E0
      have h3 : (((X.S C0 CE1 CE2).a : ℝ) - (X.S C0 CE1 CE2).E0) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ) ≤
          (X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ) := by
        apply div_le_div_of_nonneg_right _ hQ.le
        show (X.L.a : ℝ) - (X.S C0 CE1 CE2).E0 ≤ X.L.a
        linarith
      exact h1.trans h3
    have hLa0 : 0 ≤ (X.S C0 CE1 CE2).La := hF.La0
    have hLa4 : 4 * (X.S C0 CE1 CE2).La < (X.r : ℝ) + 1 := hS.La4
    have hr : (0:ℝ) < (X.r : ℝ) + 1 := by positivity
    have hq0 : 0 ≤ (X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ) := by positivity
    have e1 : 2 * (X.S C0 CE1 CE2).La * ((SegData.A0 X.p (X.S C0 CE1 CE2) : ℤ) : ℝ) / ((X.r : ℝ) + 1) ≤
        2 * (X.S C0 CE1 CE2).La * ((X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ)) / ((X.r : ℝ) + 1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hA (by linarith)) hr.le
    have e2 : 2 * (X.S C0 CE1 CE2).La * ((X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ)) / ((X.r : ℝ) + 1) ≤
        ((X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ)) / 2 := by
      rw [div_le_div_iff₀ hr (by norm_num)]
      nlinarith
    have e3 : ((b.sg i : ℕ) : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) ≤ (X.L.a : ℝ) / 2 := by
      have h0 : ((b.sg i : ℕ) : ℝ) ≤ ((X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ)) / 2 :=
        h.trans (e1.trans e2)
      calc ((b.sg i : ℕ) : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ)
          ≤ ((X.L.a : ℝ) / (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ)) / 2 * (SegData.Qj X.p (X.S C0 CE1 CE2) : ℝ) :=
            mul_le_mul h0 hPQ (by linarith) (by positivity)
        _ = (X.L.a : ℝ) / 2 := by field_simp
    have e4 : (X.L.a : ℝ) - X.L.b' < (aTop' i : ℝ) - ((∑ c, b.ry i c : ℕ) : ℝ) := by
      have h1 := hsum i
      have h2 : (X.L.a : ℝ) ≤ aTop' i := by exact_mod_cast hwin i
      linarith
    have e5 : ((b.sg i : ℕ) : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) <
        (coarseC X.p (X.S C0 CE1 CE2) aTop' b i : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) := by
      rw [hC i]
      linarith
    have e6 : ((b.sg i : ℕ) : ℝ) < (coarseC X.p (X.S C0 CE1 CE2) aTop' b i : ℝ) :=
      lt_of_mul_lt_mul_right e5 (by linarith)
    exact_mod_cast e6.le
  refine ⟨⟨⟨hD', hk.2.1, fun i hi => ?_, hk.2.2.2⟩, hdl⟩, ?_⟩
  · obtain ⟨h1, h2, _, h4, h5⟩ := hk.2.2.1 i hi
    exact ⟨h1, h2, hSG i h5, h4, h5⟩
  · have hx' := (mem_lv aTop b x).mp hx
    refine (mem_lv aTop' b x).mpr ⟨fun i => ⟨(hx'.1 i).1, ?_⟩, hx'.2⟩
    exact (hx'.1 i).1.trans (((hk.2.1 _ (uTop_ge i)).1).trans (hAC _))

/- English proof (translation)
Introduce `dl _ aTop ha aTop' ha'` and use `Finset.Subset.antisymm (idx_sub hS dl aTop aTop' ha ha') (idx_sub hS dl aTop' aTop ha' ha)`.
-/
theorem restFree_proved (hS : SegFacts C0 CE1 CE2 X) : RestFree C0 CE1 CE2 X := fun dl _ aTop ha aTop' ha' =>
  Finset.Subset.antisymm (idx_sub hS dl aTop aTop' ha ha') (idx_sub hS dl aTop' aTop ha' ha)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
