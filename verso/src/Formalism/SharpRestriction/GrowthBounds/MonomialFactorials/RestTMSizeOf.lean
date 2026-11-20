import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.WindowEntryLeTwoMulA

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

variable (C0 CE1 CE2 X) in

def aTopPt (dl : DCl X) (a : Fin X.s → ℕ) : Fin X.s → ℕ :=
  ovr (uTop (X.S C0 CE1 CE2)) a (fun i => topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i))

/- English proof (translation)
Unfold `idx at hx`. Simplify using `only [Finset.mem_sigma, Finset.mem_filter, mem_keptSet] at hx`. Conclude with `⟨hx.1.1, hx.1.2, hx.2⟩`.
-/
theorem digits_of_idx {dl : DCl X} {a : Fin X.s → ℕ} {x : Σ _ : SegBlock X.s X.r, Lv C0 CE1 CE2 X}
    (hx : x ∈ idx C0 CE1 CE2 X dl a) :
    Kept X.p X.r (X.S C0 CE1 CE2) a x.1 ∧ (x.1.rz, x.1.ry) = dl ∧ x.2 ∈ lv C0 CE1 CE2 X a x.1 := by
  classical
  unfold idx at hx
  simp only [Finset.mem_sigma, Finset.mem_filter, mem_keptSet] at hx
  exact ⟨hx.1.1, hx.1.2, hx.2⟩

/- English proof (translation)
Establish `hbox` using `cbox_eq C0 CE1 CE2 X dl a ha`. Establish `hW : a ∈ Fintype.piFinset (Wl C0 CE1 CE2 X dl)` using `hbox ▸ ha`. Conclude with `⟨a l, Fintype.mem_piFinset.1 hW l⟩`.
-/
theorem Wl_ne {dl : DCl X} {a : Fin X.s → ℕ} (ha : a ∈ cbox C0 CE1 CE2 X dl) (l : Fin X.s) :
    (Wl C0 CE1 CE2 X dl l).Nonempty := by
  have hbox := cbox_eq C0 CE1 CE2 X dl a ha
  have hW : a ∈ Fintype.piFinset (Wl C0 CE1 CE2 X dl) := hbox ▸ ha
  exact ⟨a l, Fintype.mem_piFinset.1 hW l⟩

/- English proof (translation)
Take `⟨M, hM, hMe⟩` from `Finset.exists_mem_eq_sup _ (Wl_ne ha l) (id : ℕ → ℕ)`. Rewrite using `[topA_eq, hMe]`. Conclude with `hM`.
-/
theorem topA_mem_Wl {dl : DCl X} {a : Fin X.s → ℕ} (ha : a ∈ cbox C0 CE1 CE2 X dl) (l : Fin X.s) :
    topA C0 CE1 CE2 X dl l ∈ Wl C0 CE1 CE2 X dl l := by
  obtain ⟨M, hM, hMe⟩ := Finset.exists_mem_eq_sup _ (Wl_ne ha l) (id : ℕ → ℕ)
  rw [topA_eq, hMe]
  exact hM

/- English proof (translation)
Establish `hbox` using `cbox_eq C0 CE1 CE2 X dl a ha`. Establish `hW : a ∈ Fintype.piFinset (Wl C0 CE1 CE2 X dl)` using `hbox ▸ ha`. Rewrite using `[hbox]`. Conclude with `ovr_mem _ (uTop_inj C0 CE1 CE2 X) _ a _ hW (Fintype.mem_piFinset.2 fun i => topA_mem_Wl ha _)`.
-/
theorem aTopPt_mem {dl : DCl X} {a : Fin X.s → ℕ} (ha : a ∈ cbox C0 CE1 CE2 X dl) :
    aTopPt C0 CE1 CE2 X dl a ∈ cbox C0 CE1 CE2 X dl := by
  have hbox := cbox_eq C0 CE1 CE2 X dl a ha
  have hW : a ∈ Fintype.piFinset (Wl C0 CE1 CE2 X dl) := hbox ▸ ha
  rw [hbox]
  exact ovr_mem _ (uTop_inj C0 CE1 CE2 X) _ a _ hW (Fintype.mem_piFinset.2 fun i => topA_mem_Wl ha _)

/- English proof (translation)
Establish `hb : x.1.ry = dl.2` using `congrArg Prod.snd (digits_of_idx hx).2.1`. Establish `e1` using `lLL_ovr C0 CE1 CE2 X a (fun i => topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)) x.1 x.2`. Use `show (lLL C0 CE1 CE2 X a x.1 x.2).setTies (gT C0 CE1 CE2 X x.1) (XMof C0 CE1 CE2 X dl a x.1 x.2).top = _`. Unfold `aTopPt`. Rewrite using `[e1]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[top_eq (dl := dl) a x.1 (x := x.2) (fun i => Wl_ne ha _) i]`. Unfold `cm`. Rewrite using `[hb]`.
-/
theorem setTies_top {dl : DCl X} {a : Fin X.s → ℕ} (ha : a ∈ cbox C0 CE1 CE2 X dl)
    {x : Σ _ : SegBlock X.s X.r, Lv C0 CE1 CE2 X} (hx : x ∈ idx C0 CE1 CE2 X dl a) :
    (XMof C0 CE1 CE2 X dl a x.1 x.2).LL.setTies (XMof C0 CE1 CE2 X dl a x.1 x.2).T
        (XMof C0 CE1 CE2 X dl a x.1 x.2).top = lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2 := by
  have hb : x.1.ry = dl.2 := congrArg Prod.snd (digits_of_idx hx).2.1
  have e1 := lLL_ovr C0 CE1 CE2 X a (fun i => topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)) x.1 x.2
  show (lLL C0 CE1 CE2 X a x.1 x.2).setTies (gT C0 CE1 CE2 X x.1) (XMof C0 CE1 CE2 X dl a x.1 x.2).top = _
  unfold aTopPt
  rw [e1]
  congr 1
  funext i
  rw [top_eq (dl := dl) a x.1 (x := x.2) (fun i => Wl_ne ha _) i]
  unfold cm
  rw [hb]

def RestSI : Prop :=
  ∀ dl ∈ clSet C0 CE1 CE2 X, ∀ a ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl a,
    ∀ i, (XMof C0 CE1 CE2 X dl a x.1 x.2).T.S ((XMof C0 CE1 CE2 X dl a x.1 x.2).LL.setTies
        (XMof C0 CE1 CE2 X dl a x.1 x.2).T (XMof C0 CE1 CE2 X dl a x.1 x.2).top) i ≤
      (XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i

/- English proof (translation)
Introduce `dl hdl a ha x hx`. Establish `ha'` using `aTopPt_mem ha`. Establish `hx' : x ∈ idx C0 CE1 CE2 X dl (aTopPt C0 CE1 CE2 X dl a)`. Rewrite using `[← hFree dl hdl a ha _ ha']`. Conclude with `hx`.

Take `⟨hK', -, -⟩` from `digits_of_idx hx'`. Establish `hT'` using `(mem_cbox' ha').1`. Establish `e` using `setTies_top ha hx`. Use `⟨hSI dl hdl a ha x hx, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `y`.

Rewrite using `[e]`. Conclude with `lLL_deg_le hS _ hT' x.1 hK' x.2 y`. Introduce `i show coarseA X.p (X.S C0 CE1 CE2) x.1 (uTop (X.S C0 CE1 CE2) i) - x.1.o (uTop (X.S C0 CE1 CE2) i) ≤ 2 * X.L.a`. Establish `h1` using `coarseA_upper hS x.1 (uTop (X.S C0 CE1 CE2) i)`. Establish `h2` using `b_small hS`.

Establish `hP : (1 : ℝ) ≤ ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ)` using `by exact_mod_cast hS.P1 _`. Establish `h0 : (0 : ℝ) ≤ (coarseA X.p (X.S C0 CE1 CE2) x.1 (uTop (X.S C0 CE1 CE2) i) : ℝ)` using `Nat.cast_nonneg _`. Establish `ha0 : (0 : ℝ) ≤ X.L.a` using `Nat.cast_nonneg _`. Establish `h3 : (coarseA X.p (X.S C0 CE1 CE2) x.1 (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤ 2 * X.L.a` using `by nlinarith`. Establish `h4 : coarseA X.p (X.S C0 CE1 CE2) x.1 (uTop (X.S C0 CE1 CE2) i) ≤ 2 * X.L.a` using `by exact_mod_cast h3`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[e, Fin.sum_univ_castSucc]`. Establish `hs : 2 * X.s + 2 ≤ X.r` using `hS.hF.s_le`. Establish `hp : ((X.r : ℝ) + 1) ^ 2 ≤ (X.p : ℝ)` using `hS.hF.p_ge`. Establish `hr5` using `r5 hS`.

Establish `ha0 : (0 : ℝ) ≤ X.L.a` using `Nat.cast_nonneg _`. Establish `hp0 : (0 : ℝ) < (X.p : ℝ)` using `by nlinarith`. Establish `hlast` using `lLL_deg_le hS _ hT' x.1 hK' x.2 (Fin.last (2 * X.s))`. Establish `hone : ∀ q : Fin (2 * X.s), ((lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℝ) * X.p ≤ 2 * X.L.a`. Introduce `q`.

Establish `hq : ((q.castSucc : Fin (2 * X.s + 1)) : ℕ) ≠ 2 * X.s`. Use `q.2` as an intermediate fact. Simplify using `only [Fin.val_castSucc]`. Use linear arithmetic over natural numbers and integers. Establish `h1` using `chain_wt hS _ hT' x.1 hK' q.castSucc hq`.

Establish `h2 : ((lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℝ) ≤ ((segChain X.p (X.S C0 CE1 CE2) (aTopPt C0 CE1 CE2 X dl a) x.1).deg q.castSucc : ℝ)`. Conclude with `lLL_deg_le_chain hS _ x.1 x.2 q.castSucc` after adjusting the coercions. Establish `h3 : (X.p : ℝ) ≤ ((X.S C0 CE1 CE2).P X.p (topOf q.castSucc hq) : ℝ)`. Conclude with `p_le_P (C0 := C0) (CE1 := CE1) (CE2 := CE2) (X := X) (topOf q.castSucc hq)` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation.

Establish `hsum : ((∑ q : Fin (2 * X.s), (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℕ) : ℝ) * X.p ≤ (2 * X.s : ℕ) * (2 * X.L.a)`. Rewrite using `[Nat.cast_sum, Finset.sum_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Establish `hsp : ((2 * X.s : ℕ) : ℝ) ≤ X.p`.

Establish `h1 : ((2 * X.s : ℕ) : ℝ) ≤ (X.r : ℝ)` using `by exact_mod_cast (by omega : 2 * X.s ≤ X.r)`. Use the polynomial consequences of the given equalities and inequalities. Establish `hsum2 : ((∑ q : Fin (2 * X.s), (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℕ) : ℝ) ≤ 2 * X.L.a`. Establish `h1 : ((2 * X.s : ℕ) : ℝ) * (2 * X.L.a) ≤ (2 * X.L.a) * X.p` using `by nlinarith`. Conclude with `le_of_mul_le_mul_right (hsum.trans h1) hp0`.

Establish `hsum3 : (∑ q : Fin (2 * X.s), (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc) ≤ 2 * X.L.a` using `by exact_mod_cast hsum2`. Conclude with `(Nat.add_le_add hsum3 hlast).trans (by omega)`. Conclude with `hS.hF.a1` after adjusting the coercions.
-/
theorem restTMSize_of (hS : SegFacts C0 CE1 CE2 X) (hFree : RestFree C0 CE1 CE2 X) (hSI : RestSI (C0 := C0) (CE1 := CE1)
    (CE2 := CE2) (X := X)) : RestTMSize C0 CE1 CE2 X := by
  intro dl hdl a ha x hx
  have ha' := aTopPt_mem ha
  have hx' : x ∈ idx C0 CE1 CE2 X dl (aTopPt C0 CE1 CE2 X dl a) := by
    rw [← hFree dl hdl a ha _ ha']; exact hx
  obtain ⟨hK', -, -⟩ := digits_of_idx hx'
  have hT' := (mem_cbox' ha').1
  have e := setTies_top ha hx
  refine ⟨hSI dl hdl a ha x hx, ?_, ?_, ?_, ?_⟩
  · intro y
    rw [e]
    exact lLL_deg_le hS _ hT' x.1 hK' x.2 y
  · intro i
    show coarseA X.p (X.S C0 CE1 CE2) x.1 (uTop (X.S C0 CE1 CE2) i) - x.1.o (uTop (X.S C0 CE1 CE2) i) ≤ 2 * X.L.a
    have h1 := coarseA_upper hS x.1 (uTop (X.S C0 CE1 CE2) i)
    have h2 := b_small hS
    have hP : (1 : ℝ) ≤ ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by exact_mod_cast hS.P1 _
    have h0 : (0 : ℝ) ≤ (coarseA X.p (X.S C0 CE1 CE2) x.1 (uTop (X.S C0 CE1 CE2) i) : ℝ) := Nat.cast_nonneg _
    have ha0 : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
    have h3 : (coarseA X.p (X.S C0 CE1 CE2) x.1 (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤ 2 * X.L.a := by nlinarith
    have h4 : coarseA X.p (X.S C0 CE1 CE2) x.1 (uTop (X.S C0 CE1 CE2) i) ≤ 2 * X.L.a := by exact_mod_cast h3
    omega
  ·
    rw [e, Fin.sum_univ_castSucc]
    have hs : 2 * X.s + 2 ≤ X.r := hS.hF.s_le
    have hp : ((X.r : ℝ) + 1) ^ 2 ≤ (X.p : ℝ) := hS.hF.p_ge
    have hr5 := r5 hS
    have ha0 : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
    have hp0 : (0 : ℝ) < (X.p : ℝ) := by nlinarith
    have hlast := lLL_deg_le hS _ hT' x.1 hK' x.2 (Fin.last (2 * X.s))
    have hone : ∀ q : Fin (2 * X.s),
        ((lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℝ) * X.p ≤ 2 * X.L.a := by
      intro q
      have hq : ((q.castSucc : Fin (2 * X.s + 1)) : ℕ) ≠ 2 * X.s := by
        have := q.2
        simp only [Fin.val_castSucc]
        omega
      have h1 := chain_wt hS _ hT' x.1 hK' q.castSucc hq
      have h2 : ((lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℝ) ≤
          ((segChain X.p (X.S C0 CE1 CE2) (aTopPt C0 CE1 CE2 X dl a) x.1).deg q.castSucc : ℝ) := by
        exact_mod_cast lLL_deg_le_chain hS _ x.1 x.2 q.castSucc
      have h3 : (X.p : ℝ) ≤ ((X.S C0 CE1 CE2).P X.p (topOf q.castSucc hq) : ℝ) := by
        exact_mod_cast p_le_P (C0 := C0) (CE1 := CE1) (CE2 := CE2) (X := X) (topOf q.castSucc hq)
      calc ((lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℝ) * X.p
          ≤ ((segChain X.p (X.S C0 CE1 CE2) (aTopPt C0 CE1 CE2 X dl a) x.1).deg q.castSucc : ℝ) *
            ((X.S C0 CE1 CE2).P X.p (topOf q.castSucc hq) : ℝ) :=
            mul_le_mul h2 h3 hp0.le (Nat.cast_nonneg _)
        _ ≤ 2 * X.L.a := h1
    have hsum : ((∑ q : Fin (2 * X.s), (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℕ) : ℝ) *
        X.p ≤ (2 * X.s : ℕ) * (2 * X.L.a) := by
      rw [Nat.cast_sum, Finset.sum_mul]
      calc ∑ q : Fin (2 * X.s), ((lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℝ) * X.p
          ≤ ∑ _q : Fin (2 * X.s), 2 * (X.L.a : ℝ) := Finset.sum_le_sum fun q _ => hone q
        _ = (2 * X.s : ℕ) * (2 * X.L.a) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hsp : ((2 * X.s : ℕ) : ℝ) ≤ X.p := by
      have h1 : ((2 * X.s : ℕ) : ℝ) ≤ (X.r : ℝ) := by exact_mod_cast (by omega : 2 * X.s ≤ X.r)
      nlinarith
    have hsum2 : ((∑ q : Fin (2 * X.s), (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc : ℕ) : ℝ) ≤
        2 * X.L.a := by
      have h1 : ((2 * X.s : ℕ) : ℝ) * (2 * X.L.a) ≤ (2 * X.L.a) * X.p := by nlinarith
      exact le_of_mul_le_mul_right (hsum.trans h1) hp0
    have hsum3 : (∑ q : Fin (2 * X.s), (lLL C0 CE1 CE2 X (aTopPt C0 CE1 CE2 X dl a) x.1 x.2).deg q.castSucc) ≤
        2 * X.L.a := by exact_mod_cast hsum2
    exact (Nat.add_le_add hsum3 hlast).trans (by omega)
  · exact_mod_cast hS.hF.a1

end Formalism.MainNotions.G.SymmetricFormBlocks

end
