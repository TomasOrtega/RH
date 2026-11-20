import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.DimYOvr

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section TM

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def epsM (XM : flipOneThree.InstM) (i : Fin XM.T.t) : ℝ := XM.eps i

def RestTMHyp : Prop :=
  ∀ dl ∈ clSet C0 CE1 CE2 X, ∀ a ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl a,
    (XMof C0 CE1 CE2 X dl a x.1 x.2).Hyp

def RestTMEps (CM : ℝ) : Prop :=
  ∀ dl ∈ clSet C0 CE1 CE2 X, ∀ a ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl a,
    ∀ i, epsM (XMof C0 CE1 CE2 X dl a x.1 x.2) i ≤ (30 + CM) / X.L.Y

variable {C0 CE1 CE2 X}

/- English proof (translation)
Unfold `levels at h`. Conclude with `(Finset.mem_filter.1 h).2`.
-/
theorem mem_levels {N : ℕ} (G : Formalism.GM.M.BlockData N) (x : (Fin G.T.t → ℕ) × ℕ) (h : x ∈ levels G) :
    G.LevelOK x.1 x.2 := by
  classical
  unfold levels at h
  exact (Finset.mem_filter.1 h).2

/- English proof (translation)
Establish `hi : (X.S C0 CE1 CE2).sigma + (i : ℕ) < X.s`. Use `i.2` as an intermediate fact. Unfold `SegData.t at this`. Use linear arithmetic over natural numbers and integers. Establish `h1 : (q : ℕ) ≠ 2 * X.s` using `by omega`.

Establish `h2 : ¬ (q : ℕ) % 2 = 0` using `by omega`. Establish `h3 : topOf q h1 = uTop (X.S C0 CE1 CE2) i`. Unfold `topOf uTop`. Conclude with `Fin.ext (by simp only; omega)`. Establish `h4 : ¬ ((uTop (X.S C0 CE1 CE2) i : Fin X.s) : ℕ) < (X.S C0 CE1 CE2).sigma`.

Unfold `uTop`. Simplify using the standard rewrite rules. Unfold `segChain`. Simplify using `only`. Rewrite using `[dif_neg h1, if_neg h2, h3, if_neg h4]`.
-/
theorem chain_eta (aTop : Fin X.s → ℕ) (b : SegBlock X.s X.r) (i : Fin (X.S C0 CE1 CE2).t)
    (q : Fin (2 * X.s + 1)) (hq : (q : ℕ) = 2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) + 1) :
    (segChain X.p (X.S C0 CE1 CE2) aTop b).deg q = coarseC X.p (X.S C0 CE1 CE2) aTop b (uTop (X.S C0 CE1 CE2) i) := by
  have hi : (X.S C0 CE1 CE2).sigma + (i : ℕ) < X.s := by
    have := i.2
    unfold SegData.t at this
    omega
  have h1 : (q : ℕ) ≠ 2 * X.s := by omega
  have h2 : ¬ (q : ℕ) % 2 = 0 := by omega
  have h3 : topOf q h1 = uTop (X.S C0 CE1 CE2) i := by
    unfold topOf uTop
    exact Fin.ext (by simp only; omega)
  have h4 : ¬ ((uTop (X.S C0 CE1 CE2) i : Fin X.s) : ℕ) < (X.S C0 CE1 CE2).sigma := by
    unfold uTop; simp
  unfold segChain
  simp only
  rw [dif_neg h1, if_neg h2, h3, if_neg h4]

/- English proof (translation)
Introduce `i v hv`. Establish `ha' : Function.update a0 (uTop (X.S C0 CE1 CE2) i) v ∈ cbox C0 CE1 CE2 X dl`. Establish `hbox` using `cbox_eq C0 CE1 CE2 X dl a0 ha0`. Establish `ha0'` using `hbox ▸ ha0`. Rewrite using `[hbox]`.

Rewrite `ha0'`, the goal using `[Fintype.mem_piFinset]`. Introduce `l`. Distinguish the cases in `hl : l = uTop (X.S C0 CE1 CE2) i`. Substitute `hl` using the available equality. Rewrite using `[Function.update_self]`.

Conclude with `hv`. Rewrite using `[Function.update_of_ne hl]`. Conclude with `ha0' l`. Establish `h` using `hx _ ha'`. Unfold `idx at h`.

Rewrite `h` using `[Finset.mem_sigma]`. Establish `hl` using `h.2`. Establish `hOK` using `((mem_levels _ _ hl).1 i).2`. Establish `hi : (X.S C0 CE1 CE2).sigma + (i : ℕ) < X.s`. Use `i.2` as an intermediate fact.

Unfold `SegData.t at this`. Use linear arithmetic over natural numbers and integers. Establish `e` using `chain_eta (C0 := C0) (CE1 := CE1) (CE2 := CE2) (X := X) (Function.update a0 (uTop (X.S C0 CE1 CE2) i) v) x.1 i ⟨min ((gB C0 CE1 CE2 X (Function.update a0 (uTop (X.S C0 CE1 CE2) i) v) 0 x.1).T.pos i + 1) (2 * X.s + 1 - 1), by omega⟩ (by show min (2 * ((X.S C0 CE1 CE2).sigma + (i : …`. Establish `e2 : (gB C0 CE1 CE2 X (Function.update a0 (uTop (X.S C0 CE1 CE2) i) v) 0 x.1).LL.deg ⟨min ((gB C0 CE1 CE2 X (Function.update a0 (uTop (X.S C0 CE1 CE2) i) v) 0 x.1).T.pos i + 1) (2 * X.s + 1 - 1), by omega⟩ = (segChain X.p (X.S C0 CE1 CE2) (Function.update a0 (uTop (X.S C0 CE1 CE2 …` using `rfl`. Establish `hOK' : x.2.1 i ≤ (segChain X.p (X.S C0 CE1 CE2) (Function.update a0 (uTop (X.S C0 CE1 CE2) i) v) x.1).deg ⟨min ((gB C0 CE1 CE2 X (Function.update a0 (uTop (X.S C0 CE1 CE2) i) v) 0 x.1).T.pos i + 1) (2 * X.s + 1 - 1), by omega⟩`.

Rewrite using `[← e2]`. Conclude with `hOK`. Rewrite `hOK'` using `[e]`. Unfold `coarseC at hOK'`. Rewrite `hOK'` using `[Function.update_self, hb]`.

Conclude with `hOK'`.
-/
theorem lvlRoom_of {dl : DCl X} {a0 : Fin X.s → ℕ} (ha0 : a0 ∈ cbox C0 CE1 CE2 X dl) {x : Σ _ : SegBlock X.s X.r, Lv C0 CE1 CE2 X}
    (hb : x.1.ry = dl.2) (hx : ∀ a ∈ cbox C0 CE1 CE2 X dl, x ∈ idx C0 CE1 CE2 X dl a) :
    LvlRoom C0 CE1 CE2 X dl x.2 := by
  classical
  intro i v hv
  have ha' : Function.update a0 (uTop (X.S C0 CE1 CE2) i) v ∈ cbox C0 CE1 CE2 X dl := by
    have hbox := cbox_eq C0 CE1 CE2 X dl a0 ha0
    have ha0' := hbox ▸ ha0
    rw [hbox]
    rw [Fintype.mem_piFinset] at ha0' ⊢
    intro l
    by_cases hl : l = uTop (X.S C0 CE1 CE2) i
    · subst hl; rw [Function.update_self]; exact hv
    · rw [Function.update_of_ne hl]; exact ha0' l
  have h := hx _ ha'
  unfold idx at h
  rw [Finset.mem_sigma] at h
  have hl := h.2
  have hOK := ((mem_levels _ _ hl).1 i).2
  have hi : (X.S C0 CE1 CE2).sigma + (i : ℕ) < X.s := by
    have := i.2
    unfold SegData.t at this
    omega
  have e := chain_eta (C0 := C0) (CE1 := CE1) (CE2 := CE2) (X := X) (Function.update a0 (uTop (X.S C0 CE1 CE2) i) v) x.1 i
    ⟨min ((gB C0 CE1 CE2 X (Function.update a0 (uTop (X.S C0 CE1 CE2) i) v) 0 x.1).T.pos i + 1) (2 * X.s + 1 - 1),
      by omega⟩ (by show min (2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) + 1) (2 * X.s + 1 - 1) = _; omega)
  have e2 : (gB C0 CE1 CE2 X (Function.update a0 (uTop (X.S C0 CE1 CE2) i) v) 0 x.1).LL.deg
      ⟨min ((gB C0 CE1 CE2 X (Function.update a0 (uTop (X.S C0 CE1 CE2) i) v) 0 x.1).T.pos i + 1) (2 * X.s + 1 - 1),
        by omega⟩ = (segChain X.p (X.S C0 CE1 CE2) (Function.update a0 (uTop (X.S C0 CE1 CE2) i) v) x.1).deg
      ⟨min ((gB C0 CE1 CE2 X (Function.update a0 (uTop (X.S C0 CE1 CE2) i) v) 0 x.1).T.pos i + 1) (2 * X.s + 1 - 1),
        by omega⟩ := rfl
  have hOK' : x.2.1 i ≤ (segChain X.p (X.S C0 CE1 CE2) (Function.update a0 (uTop (X.S C0 CE1 CE2) i) v) x.1).deg
      ⟨min ((gB C0 CE1 CE2 X (Function.update a0 (uTop (X.S C0 CE1 CE2) i) v) 0 x.1).T.pos i + 1) (2 * X.s + 1 - 1),
        by omega⟩ := by
    rw [← e2]; exact hOK
  rw [e] at hOK'
  unfold coarseC at hOK'
  rw [Function.update_self, hb] at hOK'
  exact hOK'

/- English proof (translation)
Unfold `Nl`. Rewrite using `[Fintype.piFinset_image, Finset.sum_image]`. Introduce `n hn n' hn' h`. Use function extensionality and compare the values at `i`. Conclude with `cm_inj hr i (Fintype.mem_piFinset.1 hn i) (Fintype.mem_piFinset.1 hn' i) (congrFun h i)`.
-/
theorem reindex {dl : DCl X} {x : Lv C0 CE1 CE2 X} (hr : LvlRoom C0 CE1 CE2 X dl x) (f : (Fin (X.S C0 CE1 CE2).t → ℕ) → ℝ) :
    ∑ n ∈ Fintype.piFinset (fun i => Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)),
        f (fun i => cm C0 CE1 CE2 X dl x i (n i)) =
      ∑ n ∈ Fintype.piFinset (Nl C0 CE1 CE2 X dl x), f n := by
  classical
  unfold Nl
  rw [Fintype.piFinset_image, Finset.sum_image]
  intro n hn n' hn' h
  funext i
  exact cm_inj hr i (Fintype.mem_piFinset.1 hn i) (Fintype.mem_piFinset.1 hn' i) (congrFun h i)

/- English proof (translation)
Unfold `flipOneThree.InstM.prog`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `(interval_eq _ ((hne i).image _) (Nl_conv hr i)).symm`.
-/
theorem prog_eq {dl : DCl X} (a : Fin X.s → ℕ) (b : SegBlock X.s X.r) {x : Lv C0 CE1 CE2 X}
    (hr : LvlRoom C0 CE1 CE2 X dl x) (hne : ∀ i, (Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)).Nonempty) :
    (XMof C0 CE1 CE2 X dl a b x).prog = Fintype.piFinset (Nl C0 CE1 CE2 X dl x) := by
  unfold flipOneThree.InstM.prog
  congr 1
  funext i
  exact (interval_eq _ ((hne i).image _) (Nl_conv hr i)).symm

/- English proof (translation)
Rewrite using `[cm_top x i (hne i)]`. Establish `hmem : sInf ((Nl C0 CE1 CE2 X dl x i : Finset ℕ) : Set ℕ) ∈ Nl C0 CE1 CE2 X dl x i`. Use `Nat.sInf_mem (s := ((Nl C0 CE1 CE2 X dl x i : Finset ℕ) : Set ℕ)) (by` as an intermediate fact. Take `⟨v, hv⟩` from `(hne i).image (cm C0 CE1 CE2 X dl x i)`. Conclude with `⟨v, by exact_mod_cast hv⟩)`.

Conclude with `this` after adjusting the coercions. Establish `hle` using `Finset.le_sup (f := id) hmem`. Use `show sInf ((Nl C0 CE1 CE2 X dl x i : Finset ℕ) : Set ℕ) + 1 * ((Nl C0 CE1 CE2 X dl x i).sup id - sInf ((Nl C0 CE1 CE2 X dl x i : Finset ℕ) : Set ℕ) + 1 - 1) = _`. Simplify using `only [id] at hle ⊢`. Use linear arithmetic over natural numbers and integers.
-/
theorem top_eq {dl : DCl X} (a : Fin X.s → ℕ) (b : SegBlock X.s X.r) {x : Lv C0 CE1 CE2 X}
    (hne : ∀ i, (Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)).Nonempty) (i : Fin (X.S C0 CE1 CE2).t) :
    (XMof C0 CE1 CE2 X dl a b x).top i = cm C0 CE1 CE2 X dl x i (topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)) := by
  rw [cm_top x i (hne i)]
  have hmem : sInf ((Nl C0 CE1 CE2 X dl x i : Finset ℕ) : Set ℕ) ∈ Nl C0 CE1 CE2 X dl x i := by
    have := Nat.sInf_mem (s := ((Nl C0 CE1 CE2 X dl x i : Finset ℕ) : Set ℕ)) (by
      obtain ⟨v, hv⟩ := (hne i).image (cm C0 CE1 CE2 X dl x i)
      exact ⟨v, by exact_mod_cast hv⟩)
    exact_mod_cast this
  have hle := Finset.le_sup (f := id) hmem
  show sInf ((Nl C0 CE1 CE2 X dl x i : Finset ℕ) : Set ℕ) +
    1 * ((Nl C0 CE1 CE2 X dl x i).sup id - sInf ((Nl C0 CE1 CE2 X dl x i : Finset ℕ) : Set ℕ) + 1 - 1) = _
  simp only [id] at hle ⊢
  omega

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem kap_XMof (dl : DCl X) (a : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) :
    (XMof C0 CE1 CE2 X dl a b x).κ = kapS X := rfl

/- English proof (translation)
Use `show ((X.S C0 CE1 CE2).t : ℝ) * (X.L.Y * kapS X + kapS X) + kapS X = _`. Unfold `D1r`. Rewrite using `[one_mul]`.
-/
theorem exponent_matrix_first_depth_eq (dl : DCl X) (a : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) :
    (XMof C0 CE1 CE2 X dl a b x).D1 = D1r C0 CE1 CE2 X 1 := by
  show ((X.S C0 CE1 CE2).t : ℝ) * (X.L.Y * kapS X + kapS X) + kapS X = _
  unfold D1r
  rw [one_mul]

/- English proof (translation)
Establish `h1` using `hM hH`. Rewrite `h1` using `[prog_eq a b hr hne, exponent_matrix_first_depth_eq]`. Establish `hc : (0 : ℝ) < ((Fintype.piFinset (Nl C0 CE1 CE2 X dl x)).card : ℝ)`. Establish `: (Fintype.piFinset (Nl C0 CE1 CE2 X dl x)).Nonempty`. Rewrite using `[Fintype.piFinset_nonempty]`.

Introduce `i`. Conclude with `(hne i).image _`. Conclude with `this.card_pos` after adjusting the coercions. Establish `hL : ∑ n ∈ Fintype.piFinset (fun i => Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)), (bY C0 CE1 CE2 X (ovr (uTop (X.S C0 CE1 CE2)) a n) b x ⌊D1r C0 CE1 CE2 X 1⌋ : ℝ) = ∑ n ∈ Fintype.piFinset (Nl C0 CE1 CE2 X dl x), (BADf C0 CE1 CE2 X a b x ⌊D1r C0 CE1 CE2 X 1⌋ n : ℝ)`. Rewrite using `[← reindex hr (fun n => (BADf C0 CE1 CE2 X a b x ⌊D1r C0 CE1 CE2 X 1⌋ n : ℝ))]`.

Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Rewrite using `[bY_ovr C0 CE1 CE2 X dl a n b hb x]`. Establish `hR : ∀ i, ∑ n ∈ Fintype.piFinset (fun i => Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)), (dimY X.p (r` using `X.r) (gB C0 CE1 CE2 X (upd C0 CE1 CE2 X dl (ovr (uTop (X.S C0 CE1 CE2)) a n) i) 0 b) x.1 x.2 : ℝ) = ∑ n ∈ Fintype.piFinset (Nl C0 CE1 CE2 X dl x), (FRf C0 CE1 CE2 X a b x (Function.update n i ((XMof C0 CE1 CE2 X dl a b x).top i)) : ℝ) := by`. Introduce `i`. Rewrite using `[← reindex hr (fun n => (FRf C0 CE1 CE2 X a b x (Function.update n i ((XMof C0 CE1 CE2 X dl a b x).top i)) : ℝ))]`.

Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Unfold `upd`. Rewrite using `[ovr_update _ (uTop_inj C0 CE1 CE2 X), dimY_ovr C0 CE1 CE2 X dl a _ b hb x, top_eq a b hne i]`. Use `congr 2`. Use function extensionality and compare the values at `i'`.

Distinguish the cases in `hi : i' = i`. Substitute `hi` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Function.update_of_ne hi, Function.update_of_ne hi]`. Rewrite using `[hL]`.

Simplify using `only [hR]`. Establish `h2 : ∑ n ∈ Fintype.piFinset (Nl C0 CE1 CE2 X dl x), (BADf C0 CE1 CE2 X a b x ⌊D1r C0 CE1 CE2 X 1⌋ n : ℝ) ≤ ∑ i, epsM (XMof C0 CE1 CE2 X dl a b x) i * ∑ n ∈ Fintype.piFinset (Nl C0 CE1 CE2 X dl x), (FRf C0 CE1 CE2 X a b x (Function.update n i ((XMof C0 CE1 CE2 X dl a b x).top i)) …`. Establish `h3` using `(div_le_iff₀ hc).1 h1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `key : ∀ (e S c : ℝ), c ≠ 0 → e * (S / c * c) = e * S` using `fun e S c hc' => by`. Rewrite using `[div_mul_cancel₀ _ hc']`. Rewrite using `[mul_assoc]`. Conclude with `(key _ _ _ hc.ne').trans rfl`.

Use `h2.trans ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_right (hε i) (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)`.
-/
theorem fibre_ineq (D : Formalism.BasicNotions.D7) (ε : ℝ) {dl : DCl X} (a : Fin X.s → ℕ) (b : SegBlock X.s X.r)
    (hb : b.ry = dl.2) {x : Lv C0 CE1 CE2 X} (hr : LvlRoom C0 CE1 CE2 X dl x)
    (hne : ∀ i, (Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)).Nonempty)
    (hM : ModelLatticeRank D (XMof C0 CE1 CE2 X dl a b x)) (hH : (XMof C0 CE1 CE2 X dl a b x).Hyp)
    (hε : ∀ i, epsM (XMof C0 CE1 CE2 X dl a b x) i ≤ ε) :
    ∑ n ∈ Fintype.piFinset (fun i => Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)),
        (bY C0 CE1 CE2 X (ovr (uTop (X.S C0 CE1 CE2)) a n) b x ⌊D1r C0 CE1 CE2 X 1⌋ : ℝ) ≤
      ε * ∑ i, ∑ n ∈ Fintype.piFinset (fun i => Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)),
        (dimY X.p (r := X.r) (gB C0 CE1 CE2 X (upd C0 CE1 CE2 X dl (ovr (uTop (X.S C0 CE1 CE2)) a n) i) 0 b)
          x.1 x.2 : ℝ) := by
  classical
  have h1 := hM hH
  rw [prog_eq a b hr hne, exponent_matrix_first_depth_eq] at h1
  have hc : (0 : ℝ) < ((Fintype.piFinset (Nl C0 CE1 CE2 X dl x)).card : ℝ) := by
    have : (Fintype.piFinset (Nl C0 CE1 CE2 X dl x)).Nonempty := by
      rw [Fintype.piFinset_nonempty]
      intro i
      exact (hne i).image _
    exact_mod_cast this.card_pos

  have hL : ∑ n ∈ Fintype.piFinset (fun i => Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)),
        (bY C0 CE1 CE2 X (ovr (uTop (X.S C0 CE1 CE2)) a n) b x ⌊D1r C0 CE1 CE2 X 1⌋ : ℝ) =
      ∑ n ∈ Fintype.piFinset (Nl C0 CE1 CE2 X dl x), (BADf C0 CE1 CE2 X a b x ⌊D1r C0 CE1 CE2 X 1⌋ n : ℝ) := by
    rw [← reindex hr (fun n => (BADf C0 CE1 CE2 X a b x ⌊D1r C0 CE1 CE2 X 1⌋ n : ℝ))]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [bY_ovr C0 CE1 CE2 X dl a n b hb x]

  have hR : ∀ i, ∑ n ∈ Fintype.piFinset (fun i => Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)),
        (dimY X.p (r := X.r) (gB C0 CE1 CE2 X (upd C0 CE1 CE2 X dl (ovr (uTop (X.S C0 CE1 CE2)) a n) i) 0 b)
          x.1 x.2 : ℝ) =
      ∑ n ∈ Fintype.piFinset (Nl C0 CE1 CE2 X dl x),
        (FRf C0 CE1 CE2 X a b x (Function.update n i ((XMof C0 CE1 CE2 X dl a b x).top i)) : ℝ) := by
    intro i
    rw [← reindex hr (fun n => (FRf C0 CE1 CE2 X a b x (Function.update n i ((XMof C0 CE1 CE2 X dl a b x).top i)) : ℝ))]
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold upd
    rw [ovr_update _ (uTop_inj C0 CE1 CE2 X), dimY_ovr C0 CE1 CE2 X dl a _ b hb x, top_eq a b hne i]
    congr 2
    funext i'
    by_cases hi : i' = i
    · subst hi; simp
    · rw [Function.update_of_ne hi, Function.update_of_ne hi]
  rw [hL]
  simp only [hR]
  have h2 : ∑ n ∈ Fintype.piFinset (Nl C0 CE1 CE2 X dl x), (BADf C0 CE1 CE2 X a b x ⌊D1r C0 CE1 CE2 X 1⌋ n : ℝ) ≤
      ∑ i, epsM (XMof C0 CE1 CE2 X dl a b x) i * ∑ n ∈ Fintype.piFinset (Nl C0 CE1 CE2 X dl x),
        (FRf C0 CE1 CE2 X a b x (Function.update n i ((XMof C0 CE1 CE2 X dl a b x).top i)) : ℝ) := by
    have h3 := (div_le_iff₀ hc).1 h1
    calc _ ≤ _ := h3
      _ = _ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        have key : ∀ (e S c : ℝ), c ≠ 0 → e * (S / c * c) = e * S := fun e S c hc' => by
          rw [div_mul_cancel₀ _ hc']
        rw [mul_assoc]
        exact (key _ _ _ hc.ne').trans rfl
  refine h2.trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  exact mul_le_mul_of_nonneg_right (hε i) (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)

/- English proof (translation)
Introduce `dl hdl a0 ha0 x hx`. Establish `hxa : ∀ a ∈ cbox C0 CE1 CE2 X dl, x ∈ idx C0 CE1 CE2 X dl a` using `fun a ha => by`. Rewrite using `[← hF dl hdl a0 ha0 a ha]`. Conclude with `hx`. Establish `hb : x.1.ry = dl.2`.

Use `hx` as an intermediate fact. Unfold `idx at this`. Rewrite `this` using `[Finset.mem_sigma, Finset.mem_filter]`. Conclude with `(congrArg Prod.snd this.1.2 : _)`. Establish `hr` using `lvlRoom_of ha0 hb hxa`.

Establish `hbox` using `cbox_eq C0 CE1 CE2 X dl a0 ha0`. Establish `hne : ∀ i, (Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)).Nonempty` using `fun i => ⟨a0 (uTop (X.S C0 CE1 CE2) i), Fintype.mem_piFinset.1 (hbox ▸ ha0) _⟩`. Rewrite using `[hbox]`. Use `box_of_fibres (uTop (X.S C0 CE1 CE2)) (uTop_inj C0 CE1 CE2 X) (Wl C0 CE1 CE2 X dl) (fun a => (bY C0 CE1 CE2 X a x.1 x.2 ⌊D1r C0 CE1 CE2 X 1⌋ : ℝ)) (fun i a => (dimY X.p (r := X.r) (gB C0 CE1 CE2 X (upd C0 CE1 CE2 X dl a i) 0 x.1) x.2.1 x.2.2 : ℝ)) ((30 + 1) / X.L.Y) (hbox ▸ ⟨a0, …` and prove the remaining obligations. Introduce `a ha`.

Establish `ha' : a ∈ cbox C0 CE1 CE2 X dl` using `hbox ▸ ha`. Conclude with `fibre_ineq D _ a x.1 hb hr hne (hM _) (hH dl hdl a ha' x (hxa a ha')) (hE dl hdl a ha' x (hxa a ha'))`.
-/
theorem restTM_of_rests (D : Formalism.BasicNotions.D7) (hM : ∀ XM : flipOneThree.InstM, ModelLatticeRank D XM)
    (hF : RestFree C0 CE1 CE2 X) (hH : RestTMHyp C0 CE1 CE2 X) (hE : RestTMEps C0 CE1 CE2 X 1) :
    RestTM C0 CE1 CE2 X 1 := by
  classical
  intro dl hdl a0 ha0 x hx
  have hxa : ∀ a ∈ cbox C0 CE1 CE2 X dl, x ∈ idx C0 CE1 CE2 X dl a := fun a ha => by
    rw [← hF dl hdl a0 ha0 a ha]; exact hx
  have hb : x.1.ry = dl.2 := by
    have := hx
    unfold idx at this
    rw [Finset.mem_sigma, Finset.mem_filter] at this
    exact (congrArg Prod.snd this.1.2 : _)
  have hr := lvlRoom_of ha0 hb hxa
  have hbox := cbox_eq C0 CE1 CE2 X dl a0 ha0
  have hne : ∀ i, (Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)).Nonempty := fun i =>
    ⟨a0 (uTop (X.S C0 CE1 CE2) i), Fintype.mem_piFinset.1 (hbox ▸ ha0) _⟩
  rw [hbox]
  refine box_of_fibres (uTop (X.S C0 CE1 CE2)) (uTop_inj C0 CE1 CE2 X) (Wl C0 CE1 CE2 X dl)
    (fun a => (bY C0 CE1 CE2 X a x.1 x.2 ⌊D1r C0 CE1 CE2 X 1⌋ : ℝ))
    (fun i a => (dimY X.p (r := X.r) (gB C0 CE1 CE2 X (upd C0 CE1 CE2 X dl a i) 0 x.1) x.2.1 x.2.2 : ℝ))
    ((30 + 1) / X.L.Y) (hbox ▸ ⟨a0, ha0⟩) ?_
  intro a ha
  have ha' : a ∈ cbox C0 CE1 CE2 X dl := hbox ▸ ha
  exact fibre_ineq D _ a x.1 hb hr hne (hM _) (hH dl hdl a ha' x (hxa a ha'))
    (hE dl hdl a ha' x (hxa a ha'))

end TM

end Formalism.MainNotions.G.SymmetricFormBlocks

end
