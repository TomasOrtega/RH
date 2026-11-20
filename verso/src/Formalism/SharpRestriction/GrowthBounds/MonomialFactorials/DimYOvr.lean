import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.LettersExt

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section Fibre

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

open Classical in

def Wl (dl : DCl X) (l : Fin X.s) : Finset ℕ :=
  X.winA.filter fun x => ∑ c, dl.2 l c ≤ x ∧ (X.S C0 CE1 CE2).P X.p l ∣ x - ∑ c, dl.2 l c

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem topA_eq (dl : DCl X) (l : Fin X.s) : topA C0 CE1 CE2 X dl l = (Wl C0 CE1 CE2 X dl l).sup id := rfl

/- English proof (translation)
Unfold `Wl`. Rewrite using `[Finset.mem_filter]`.
-/
private theorem mem_Wl_iff_mem_winA_and_dvd_sub (dl : DCl X) (l : Fin X.s) (v : ℕ) :
    v ∈ Wl C0 CE1 CE2 X dl l ↔
      v ∈ X.winA ∧ (∑ c, dl.2 l c ≤ v ∧ (X.S C0 CE1 CE2).P X.p l ∣ v - ∑ c, dl.2 l c) := by
  unfold Wl
  rw [Finset.mem_filter]

/- English proof (translation)
Unfold `cbox`. Simplify using `only [Finset.mem_filter]`.
-/
private theorem mem_cbox_iff_mem_piFinset_and_compat (dl : DCl X) (a : Fin X.s → ℕ) :
    a ∈ cbox C0 CE1 CE2 X dl ↔ a ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA) ∧ Compat C0 CE1 CE2 X dl a := by
  classical
  unfold cbox
  simp only [Finset.mem_filter]

/- English proof (translation)
Establish `h0'` using `((mem_cbox_iff_mem_piFinset_and_compat C0 CE1 CE2 X dl a0).1 h0).2`. Simplify using `only [Compat, DigitsOK, ColumnSystems.digitBlock] at h0'`. Use extensionality with `a`. Rewrite using `[mem_cbox_iff_mem_piFinset_and_compat, Fintype.mem_piFinset, Fintype.mem_piFinset]`. Simplify using `only [Compat, DigitsOK, ColumnSystems.digitBlock, mem_Wl_iff_mem_winA_and_dvd_sub]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨ha, -, -, h3⟩ i`. Conclude with `⟨ha i, h3 i⟩`. Introduce `h`. Conclude with `⟨fun i => (h i).1, h0'.1, h0'.2.1, fun i => (h i).2⟩`.
-/
theorem cbox_eq (dl : DCl X) (a0 : Fin X.s → ℕ) (h0 : a0 ∈ cbox C0 CE1 CE2 X dl) :
    cbox C0 CE1 CE2 X dl = Fintype.piFinset (Wl C0 CE1 CE2 X dl) := by
  have h0' := ((mem_cbox_iff_mem_piFinset_and_compat C0 CE1 CE2 X dl a0).1 h0).2
  simp only [Compat, DigitsOK, ColumnSystems.digitBlock] at h0'
  ext a
  rw [mem_cbox_iff_mem_piFinset_and_compat, Fintype.mem_piFinset, Fintype.mem_piFinset]
  simp only [Compat, DigitsOK, ColumnSystems.digitBlock, mem_Wl_iff_mem_winA_and_dvd_sub]
  constructor
  · rintro ⟨ha, -, -, h3⟩ i
    exact ⟨ha i, h3 i⟩
  · intro h
    exact ⟨fun i => (h i).1, h0'.1, h0'.2.1, fun i => (h i).2⟩

def cm (dl : DCl X) (x : Lv C0 CE1 CE2 X) (i : Fin (X.S C0 CE1 CE2).t) (v : ℕ) : ℕ :=
  (v - ∑ c, dl.2 (uTop (X.S C0 CE1 CE2) i) c) / (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) - x.1 i

def Nl (dl : DCl X) (x : Lv C0 CE1 CE2 X) (i : Fin (X.S C0 CE1 CE2).t) : Finset ℕ :=
  (Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)).image (cm C0 CE1 CE2 X dl x i)

/- English proof (translation)
Unfold `SegData.P`. Conclude with `pow_pos X.std.1.prime.pos _`.
-/
theorem twoPow_pos (l : Fin X.s) : 0 < (X.S C0 CE1 CE2).P X.p l := by
  unfold SegData.P
  exact pow_pos X.std.1.prime.pos _

def LvlRoom (dl : DCl X) (x : Lv C0 CE1 CE2 X) : Prop :=
  ∀ i, ∀ v ∈ Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i),
    x.1 i ≤ (v - ∑ c, dl.2 (uTop (X.S C0 CE1 CE2) i) c) / (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i)

variable {C0 CE1 CE2 X}

/- English proof (translation)
Introduce `v hv v' hv' he`. Establish `r1` using `hr i v hv`. Establish `r2` using `hr i v' hv'`. Simplify using `only [Finset.mem_coe, mem_Wl_iff_mem_winA_and_dvd_sub] at hv hv'`. Simplify using `only [cm] at he`.

Establish `hPp` using `twoPow_pos C0 CE1 CE2 X (uTop (X.S C0 CE1 CE2) i)`. Take `⟨k, hk⟩` from `hv.2.2`. Take `⟨k', hk'⟩` from `hv'.2.2`. Rewrite `r1` using `[hk, Nat.mul_div_cancel_left _ hPp]`. Rewrite `he` using `[hk, Nat.mul_div_cancel_left _ hPp]`.

Rewrite `r2` using `[hk', Nat.mul_div_cancel_left _ hPp]`. Rewrite `he` using `[hk', Nat.mul_div_cancel_left _ hPp]`. Establish `hkk : k = k'` using `by omega`. Substitute `hkk` using the available equality. Use linear arithmetic over natural numbers and integers.
-/
theorem cm_inj {dl : DCl X} {x : Lv C0 CE1 CE2 X} (hr : LvlRoom C0 CE1 CE2 X dl x) (i : Fin (X.S C0 CE1 CE2).t) :
    Set.InjOn (cm C0 CE1 CE2 X dl x i) (Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)) := by
  intro v hv v' hv' he
  have r1 := hr i v hv
  have r2 := hr i v' hv'
  simp only [Finset.mem_coe, mem_Wl_iff_mem_winA_and_dvd_sub] at hv hv'
  simp only [cm] at he
  have hPp := twoPow_pos C0 CE1 CE2 X (uTop (X.S C0 CE1 CE2) i)
  obtain ⟨k, hk⟩ := hv.2.2
  obtain ⟨k', hk'⟩ := hv'.2.2
  rw [hk, Nat.mul_div_cancel_left _ hPp] at r1
  rw [hk, Nat.mul_div_cancel_left _ hPp] at he
  rw [hk', Nat.mul_div_cancel_left _ hPp] at r2
  rw [hk', Nat.mul_div_cancel_left _ hPp] at he
  have hkk : k = k' := by omega
  subst hkk
  omega

/- English proof (translation)
Unfold `cm`. Conclude with `Nat.sub_le_sub_right (Nat.div_le_div_right (Nat.sub_le_sub_right h _)) _`.
-/
theorem cm_mono (dl : DCl X) (x : Lv C0 CE1 CE2 X) (i : Fin (X.S C0 CE1 CE2).t) {v v' : ℕ} (h : v ≤ v') :
    cm C0 CE1 CE2 X dl x i v ≤ cm C0 CE1 CE2 X dl x i v' := by
  unfold cm
  exact Nat.sub_le_sub_right (Nat.div_le_div_right (Nat.sub_le_sub_right h _)) _

/- English proof (translation)
Introduce `y hy y' hy' z hyz hzy'`. Simplify using `only [Nl, Finset.mem_image] at hy hy' ⊢`. Take `⟨v, hv, rfl⟩` from `hy`. Take `⟨v', hv', rfl⟩` from `hy'`. Establish `r1` using `hr i v hv`.

Establish `r2` using `hr i v' hv'`. Simplify using `only [mem_Wl_iff_mem_winA_and_dvd_sub, Formalism.MainNotions.flipOneThree.Inst.winA, Finset.mem_Icc] at hv hv' ⊢`. Simplify using `only [cm] at hyz hzy' ⊢`. Establish `hPp` using `twoPow_pos C0 CE1 CE2 X (uTop (X.S C0 CE1 CE2) i)`. Take `⟨k, hk⟩` from `hv.2.2`.

Take `⟨k', hk'⟩` from `hv'.2.2`. Rewrite `r1` using `[hk, Nat.mul_div_cancel_left _ hPp]`. Rewrite `hyz` using `[hk, Nat.mul_div_cancel_left _ hPp]`. Rewrite `r2` using `[hk', Nat.mul_div_cancel_left _ hPp]`. Rewrite `hzy'` using `[hk', Nat.mul_div_cancel_left _ hPp]`.

Establish `hle1 : k ≤ z + x.1 i` using `by omega`. Establish `hle2 : z + x.1 i ≤ k'` using `by omega`. Establish `m1` using `Nat.mul_le_mul_left ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i)) hle1`. Establish `m2` using `Nat.mul_le_mul_left ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i)) hle2`. Use `⟨(∑ c, dl.2 (uTop (X.S C0 CE1 CE2) i) c) + (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) * (z + x.1 i), ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Conclude with `⟨z + x.1 i, by omega⟩`. Rewrite using `[Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ hPp, Nat.add_sub_cancel]`.
-/
theorem Nl_conv {dl : DCl X} {x : Lv C0 CE1 CE2 X} (hr : LvlRoom C0 CE1 CE2 X dl x) (i : Fin (X.S C0 CE1 CE2).t) :
    ∀ y ∈ Nl C0 CE1 CE2 X dl x i, ∀ y' ∈ Nl C0 CE1 CE2 X dl x i, ∀ z, y ≤ z → z ≤ y' → z ∈ Nl C0 CE1 CE2 X dl x i := by
  intro y hy y' hy' z hyz hzy'
  simp only [Nl, Finset.mem_image] at hy hy' ⊢
  obtain ⟨v, hv, rfl⟩ := hy
  obtain ⟨v', hv', rfl⟩ := hy'
  have r1 := hr i v hv
  have r2 := hr i v' hv'
  simp only [mem_Wl_iff_mem_winA_and_dvd_sub, Formalism.MainNotions.flipOneThree.Inst.winA, Finset.mem_Icc] at hv hv' ⊢
  simp only [cm] at hyz hzy' ⊢
  have hPp := twoPow_pos C0 CE1 CE2 X (uTop (X.S C0 CE1 CE2) i)
  obtain ⟨k, hk⟩ := hv.2.2
  obtain ⟨k', hk'⟩ := hv'.2.2
  rw [hk, Nat.mul_div_cancel_left _ hPp] at r1
  rw [hk, Nat.mul_div_cancel_left _ hPp] at hyz
  rw [hk', Nat.mul_div_cancel_left _ hPp] at r2
  rw [hk', Nat.mul_div_cancel_left _ hPp] at hzy'
  have hle1 : k ≤ z + x.1 i := by omega
  have hle2 : z + x.1 i ≤ k' := by omega
  have m1 := Nat.mul_le_mul_left ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i)) hle1
  have m2 := Nat.mul_le_mul_left ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i)) hle2
  refine ⟨(∑ c, dl.2 (uTop (X.S C0 CE1 CE2) i) c) + (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) * (z + x.1 i), ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · omega
  · omega
  · omega
  · exact ⟨z + x.1 i, by omega⟩
  · rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ hPp, Nat.add_sub_cancel]

/- English proof (translation)
Rewrite using `[topA_eq]`. Take `⟨m, hm, hmax⟩` from `Finset.exists_max_image _ id hne`. Establish `hsup : (Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)).sup id = m` using `le_antisymm (Finset.sup_le fun v hv => hmax v hv) (Finset.le_sup (f := id) hm)`. Rewrite using `[hsup]`. Apply `le_antisymm` to reduce the goal to its premises.

Conclude with `Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hm)`. Apply `Finset.sup_le` to reduce the goal to its premises. Introduce `y hy`. Simplify using `only [Nl, Finset.mem_image] at hy`. Take `⟨v, hv, rfl⟩` from `hy`.

Conclude with `cm_mono dl x i (hmax v hv)`.
-/
theorem cm_top {dl : DCl X} (x : Lv C0 CE1 CE2 X) (i : Fin (X.S C0 CE1 CE2).t)
    (hne : (Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)).Nonempty) :
    cm C0 CE1 CE2 X dl x i (topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)) = (Nl C0 CE1 CE2 X dl x i).sup id := by
  rw [topA_eq]
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image _ id hne
  have hsup : (Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)).sup id = m :=
    le_antisymm (Finset.sup_le fun v hv => hmax v hv) (Finset.le_sup (f := id) hm)
  rw [hsup]
  apply le_antisymm
  · exact Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hm)
  · apply Finset.sup_le
    intro y hy
    simp only [Nl, Finset.mem_image] at hy
    obtain ⟨v, hv, rfl⟩ := hy
    exact cm_mono dl x i (hmax v hv)

variable (C0 CE1 CE2 X)

def XMof (dl : DCl X) (a : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) : flipOneThree.InstM where
  p := X.p
  hp := X.std.1.prime
  s := X.s
  r := X.r
  hr := X.hm
  LL := lLL C0 CE1 CE2 X a b x
  T := gT C0 CE1 CE2 X b
  a := X.L.a
  E := X.L.Y * kapS X
  Yl := fun i => (Nl C0 CE1 CE2 X dl x i).sup id - sInf ((Nl C0 CE1 CE2 X dl x i : Finset ℕ) : Set ℕ) + 1
  n₀ := fun i => sInf ((Nl C0 CE1 CE2 X dl x i : Finset ℕ) : Set ℕ)
  dd := fun _ => 1
  ρ := ⟨X.r - 1, Nat.sub_lt (Nat.pos_of_ne_zero X.hm) one_pos⟩

def BADf (a : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) (D : ℤ) (n : Fin (X.S C0 CE1 CE2).t → ℕ) : ℕ :=
  Formalism.GM.M.bad X.p (fun F G => Formalism.GM.M.fockN X.p ((lLL C0 CE1 CE2 X a b x).setTies (gT C0 CE1 CE2 X b) n)
            ((gT C0 CE1 CE2 X b).phis X.p (r := X.r) ((lLL C0 CE1 CE2 X a b x).setTies (gT C0 CE1 CE2 X b) n) F) G)
    (Formalism.GM.M.YZ X.p (r := X.r) ((lLL C0 CE1 CE2 X a b x).setTies (gT C0 CE1 CE2 X b) n) (gT C0 CE1 CE2 X b).J
      (gT C0 CE1 CE2 X b).thr) D

def FRf (a : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) (n : Fin (X.S C0 CE1 CE2).t → ℕ) : ℕ :=
  Module.finrank ℚ_[X.p] (Formalism.GM.M.Y X.p (r := X.r) ((lLL C0 CE1 CE2 X a b x).setTies (gT C0 CE1 CE2 X b) n)
    (gT C0 CE1 CE2 X b).J (gT C0 CE1 CE2 X b).thr)

/- English proof (translation)
Establish `h` using `lLL_ovr C0 CE1 CE2 X a n b x`. Establish `hf : (fun i => cm C0 CE1 CE2 X dl x i (n i)) = (fun i : Fin (X.S C0 CE1 CE2).t => (n i - ∑ c, b.ry (uTop (X.S C0 CE1 CE2) i) c) / (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) - x.1 i)`. Use function extensionality and compare the values at `i`. Simplify using `only [cm, hb]`. Unfold `BADf bY badY`.

Rewrite using `[hf, ← h]`. Both sides reduce to the same expression.
-/
theorem bY_ovr (dl : DCl X) (a : Fin X.s → ℕ) (n : Fin (X.S C0 CE1 CE2).t → ℕ) (b : SegBlock X.s X.r)
    (hb : b.ry = dl.2) (x : Lv C0 CE1 CE2 X) (D : ℤ) :
    bY C0 CE1 CE2 X (ovr (uTop (X.S C0 CE1 CE2)) a n) b x D =
      BADf C0 CE1 CE2 X a b x D (fun i => cm C0 CE1 CE2 X dl x i (n i)) := by
  have h := lLL_ovr C0 CE1 CE2 X a n b x
  have hf : (fun i => cm C0 CE1 CE2 X dl x i (n i)) = (fun i : Fin (X.S C0 CE1 CE2).t =>
      (n i - ∑ c, b.ry (uTop (X.S C0 CE1 CE2) i) c) / (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) - x.1 i) := by
    funext i
    simp only [cm, hb]
  unfold BADf bY badY
  rw [hf, ← h]
  rfl

/- English proof (translation)
Establish `h` using `lLL_ovr C0 CE1 CE2 X a n b x`. Establish `hf : (fun i => cm C0 CE1 CE2 X dl x i (n i)) = (fun i : Fin (X.S C0 CE1 CE2).t => (n i - ∑ c, b.ry (uTop (X.S C0 CE1 CE2) i) c) / (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) - x.1 i)`. Use function extensionality and compare the values at `i`. Simplify using `only [cm, hb]`. Unfold `FRf dimY`.

Rewrite using `[hf, ← h]`. Both sides reduce to the same expression.
-/
theorem dimY_ovr (dl : DCl X) (a : Fin X.s → ℕ) (n : Fin (X.S C0 CE1 CE2).t → ℕ) (b : SegBlock X.s X.r)
    (hb : b.ry = dl.2) (x : Lv C0 CE1 CE2 X) :
    dimY X.p (r := X.r) (gB C0 CE1 CE2 X (ovr (uTop (X.S C0 CE1 CE2)) a n) 0 b) x.1 x.2 =
      FRf C0 CE1 CE2 X a b x (fun i => cm C0 CE1 CE2 X dl x i (n i)) := by
  have h := lLL_ovr C0 CE1 CE2 X a n b x
  have hf : (fun i => cm C0 CE1 CE2 X dl x i (n i)) = (fun i : Fin (X.S C0 CE1 CE2).t =>
      (n i - ∑ c, b.ry (uTop (X.S C0 CE1 CE2) i) c) / (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) - x.1 i) := by
    funext i
    simp only [cm, hb]
  unfold FRf dimY
  rw [hf, ← h]
  rfl

end Fibre

end Formalism.MainNotions.G.SymmetricFormBlocks

end
