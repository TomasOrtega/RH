import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CountLow
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SegmentChainDegreeEven

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Finset

def KeptPairAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (m : ℝ), 0 ≤ m →
    (⌈m⌉₊ : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * X.N1 * X.La C0 / X.k →
    ∀ rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ,
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      ∀ t, TgtOK C0 CE1 CE2 X j m rz ry t →
        Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (pairMap C0 CE1 CE2 X j rz ry t).1

def KeptLevelAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (m : ℝ), 0 ≤ m →
    (⌈m⌉₊ : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * X.N1 * X.La C0 / X.k →
    ∀ rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ,
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      ∀ t, TgtOK C0 CE1 CE2 X j m rz ry t →
        (BD C0 CE1 CE2 X j m (pairMap C0 CE1 CE2 X j rz ry t).1).LevelOK (pairMap C0 CE1 CE2 X j rz ry t).2.1.1
          (pairMap C0 CE1 CE2 X j rz ry t).2.1.2

def KeptChainAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (m : ℝ), 0 ≤ m →
    (⌈m⌉₊ : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * X.N1 * X.La C0 / X.k →
    ∀ rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ,
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      ∀ t, TgtOK C0 CE1 CE2 X j m rz ry t →
        IsChain ((BD C0 CE1 CE2 X j m (pairMap C0 CE1 CE2 X j rz ry t).1).lettersAt (pairMap C0 CE1 CE2 X j rz ry t).2.1.1
          (pairMap C0 CE1 CE2 X j rz ry t).2.1.2) (pairMap C0 CE1 CE2 X j rz ry t).2.2

def KeptThresholdAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (m : ℝ), 0 ≤ m →
    (⌈m⌉₊ : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * X.N1 * X.La C0 / X.k →
    ∀ rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ,
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      ∀ t, TgtOK C0 CE1 CE2 X j m rz ry t →
        ChainOK (BD C0 CE1 CE2 X j m (pairMap C0 CE1 CE2 X j rz ry t).1).T.J
          (BD C0 CE1 CE2 X j m (pairMap C0 CE1 CE2 X j rz ry t).1).T.thr (pairMap C0 CE1 CE2 X j rz ry t).2.2

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Establish `hnn : 0 ≤ ∑ t : Fin r, nu t.succ - ∑ t : Fin r, mu t.succ`. Rewrite using `[← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_nonneg fun t _ => sub_nonneg.mpr (h1 t.succ)`. Use `⟨⟨fun t => h1 t.succ, fun i j hij => h2 i.succ j.succ (by simp only [Fin.val_succ]; omega), ?_⟩, hnn, ?_, h1 0, ?_⟩` and prove the remaining obligations.

Conclude with `(Int.toNat_of_nonneg hnn).symm`. Rewrite `h3` using `[Fin.sum_univ_succ, Fin.sum_univ_succ]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `t ht`. Conclude with `h2 0 t.succ (by simp only [Fin.val_succ, Fin.val_zero]; omega)`.
-/
theorem strip_tail {r : ℕ} {nu mu : Fin (r + 1) → ℤ} {g : ℕ} (h : Strip nu mu g) :
    Strip (fun t : Fin r => nu t.succ) (fun t : Fin r => mu t.succ)
        ((∑ t : Fin r, nu t.succ - ∑ t : Fin r, mu t.succ).toNat) ∧
      0 ≤ ∑ t : Fin r, nu t.succ - ∑ t : Fin r, mu t.succ ∧
      (nu 0 - mu 0) + (∑ t : Fin r, nu t.succ - ∑ t : Fin r, mu t.succ) = (g : ℤ) ∧ mu 0 ≤ nu 0 ∧
      ∀ t : Fin r, t.val = 0 → nu t.succ ≤ mu 0 := by
  obtain ⟨h1, h2, h3⟩ := h
  have hnn : 0 ≤ ∑ t : Fin r, nu t.succ - ∑ t : Fin r, mu t.succ := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg fun t _ => sub_nonneg.mpr (h1 t.succ)
  refine ⟨⟨fun t => h1 t.succ, fun i j hij => h2 i.succ j.succ (by simp only [Fin.val_succ]; omega), ?_⟩,
    hnn, ?_, h1 0, ?_⟩
  · exact (Int.toNat_of_nonneg hnn).symm
  · rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at h3
    linarith
  · intro t ht
    exact h2 0 t.succ (by simp only [Fin.val_succ, Fin.val_zero]; omega)

/- English proof (translation)
Establish `hnn : 0 ≤ ∑ t, lam t - ∑ t : Fin r, mu t.succ`. Rewrite using `[← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_nonneg fun t _ => sub_nonneg.mpr (h t).1`. Use `⟨⟨fun t => (h t).1, fun i j hij => (h j).2.trans (le_of_eq (congrArg mu (Fin.ext (by simp only [Fin.coe_castSucc, Fin.val_succ]; omega)))), ?_⟩, hnn, ?_⟩` and prove the remaining obligations. Conclude with `(Int.toNat_of_nonneg hnn).symm`.

Introduce `t ht`. Conclude with `(h t).2.trans (le_of_eq (congrArg mu (Fin.ext (by simp only [Fin.coe_castSucc, Fin.val_zero]; omega))))`.
-/
theorem inter_strip {r : ℕ} {mu : Fin (r + 1) → ℤ} {lam : Fin r → ℤ} (h : Inter mu lam) :
    Strip lam (fun t : Fin r => mu t.succ) ((∑ t, lam t - ∑ t : Fin r, mu t.succ).toNat) ∧
      0 ≤ ∑ t, lam t - ∑ t : Fin r, mu t.succ ∧ ∀ t : Fin r, t.val = 0 → lam t ≤ mu 0 := by
  have hnn : 0 ≤ ∑ t, lam t - ∑ t : Fin r, mu t.succ := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg fun t _ => sub_nonneg.mpr (h t).1
  refine ⟨⟨fun t => (h t).1, fun i j hij => (h j).2.trans (le_of_eq (congrArg mu
    (Fin.ext (by simp only [Fin.coe_castSucc, Fin.val_succ]; omega)))), ?_⟩, hnn, ?_⟩
  · exact (Int.toNat_of_nonneg hnn).symm
  · intro t ht
    exact (h t).2.trans (le_of_eq (congrArg mu (Fin.ext (by simp only [Fin.coe_castSucc, Fin.val_zero]; omega))))

/- English proof (translation)
Take `⟨h0, hs⟩` from `h`. Establish `h1` using `hs 0`. Rewrite `h1` using `[if_pos hv]`. Take `⟨a, b, _⟩` from `h1`. Establish `ha` using `a t.succ`.

Establish `hb` using `b t.castSucc t.succ (by simp only [Fin.coe_castSucc, Fin.val_succ])`. Simplify using `only [Fin.succ_zero_eq_one, Fin.castSucc_zero, h0, Pi.zero_apply] at ha hb`. Conclude with `le_antisymm hb ha`.
-/
theorem chain_first_tail {N r : ℕ} {LL : ChainLetters (N + 1)} {mu : Fin (N + 1 + 1) → Fin (r + 1) → ℤ}
    (h : IsChain LL mu) (hv : LL.vec 0 = true) (t : Fin r) : mu 1 t.succ = 0 := by
  obtain ⟨h0, hs⟩ := h
  have h1 := hs 0
  rw [if_pos hv] at h1
  obtain ⟨a, b, _⟩ := h1
  have ha := a t.succ
  have hb := b t.castSucc t.succ (by simp only [Fin.coe_castSucc, Fin.val_succ])
  simp only [Fin.succ_zero_eq_one, Fin.castSucc_zero, h0, Pi.zero_apply] at ha hb
  exact le_antisymm hb ha

/- English proof (translation)
Unfold `finPos`. Conclude with `Fin.ext (Nat.min_eq_left (by omega))`.
-/
theorem finPos_eq (N n : ℕ) (h : n < N + 1) : finPos N n = ⟨n, h⟩ := by
  unfold finPos
  exact Fin.ext (Nat.min_eq_left (by omega))

/- English proof (translation)
Unfold `pairChain`. Conclude with `dif_pos h`.
-/
theorem pairChain_lt {s r : ℕ} (mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ) (lam : Fin r → ℤ) (n : ℕ) (h : n < 2 * s + 1) :
    pairChain mu lam ⟨n, by omega⟩ = fun t : Fin r => mu ⟨n + 1, by omega⟩ t.succ := by
  unfold pairChain
  exact dif_pos h

/- English proof (translation)
Unfold `pairChain`. Conclude with `dif_neg (Nat.lt_irrefl _)`.
-/
theorem pairChain_last {s r : ℕ} (mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ) (lam : Fin r → ℤ) :
    pairChain mu lam ⟨2 * s + 1, by omega⟩ = lam := by
  unfold pairChain
  exact dif_neg (Nat.lt_irrefl _)

/- English proof (translation)
Establish `hi` using `i.2`. Establish `hV : Strip (mu ⟨2 * i.val + 2, by omega⟩) (mu ⟨2 * i.val + 1, by omega⟩) (Ai i)`. Use `h.2 ⟨2 * i.val + 1, by omega⟩` as an intermediate fact. Rewrite `this` using `[if_pos (show (kLetters A Ai Ci).vec ⟨2 * i.val + 1, by omega⟩ = true from decide_eq_true (Or.inr (by show (2 * i.val + 1) % 2 = 1; omega))), kLetters_deg_odd]`. Conclude with `this`.

Establish `hC : Strip (mu ⟨2 * i.val + 2, by omega⟩) (mu ⟨2 * i.val + 3, by omega⟩) (Ci i)`. Use `h.2 ⟨2 * i.val + 2, by omega⟩` as an intermediate fact. Rewrite using `[if_neg (show ¬ (kLetters A Ai Ci).vec ⟨2 * i.val + 2, by omega⟩ = true from by`. Introduce `hh`. Break down `of_decide_eq_true hh with h1 | h1` into its components or cases.

Establish `: 2 * i.val + 2 = 0` using `h1`. Use linear arithmetic over natural numbers and integers. Establish `: (2 * i.val + 2) % 2 = 1` using `h1 omega), kLetters_deg_even] at this`. Conclude with `this`. Take `⟨v1, v2, v3, v4, v5⟩` from `strip_tail hV`.

Take `⟨c1, c2, c3, c4, c5⟩` from `strip_tail hC`. Establish `eW : pairW mu i.val = ∑ t : Fin r, mu ⟨2 * i.val + 2, by omega⟩ t.succ - ∑ t : Fin r, mu ⟨2 * i.val + 1, by omega⟩ t.succ`. Unfold `pairW pairTail`. Rewrite using `[finPos_eq (2 * s + 1) (2 * i.val + 2) (by omega), finPos_eq (2 * s + 1) (2 * i.val + 1) (by omega)]`. Establish `eC0 : pairC mu i.val = mu ⟨2 * i.val + 1, by omega⟩ 0`.

Unfold `pairC`. Rewrite using `[finPos_eq (2 * s + 1) (2 * i.val + 1) (by omega)]`. Establish `eC1 : pairC mu (i.val + 1) = mu ⟨2 * i.val + 3, by omega⟩ 0`. Unfold `pairC`. Rewrite using `[finPos_eq (2 * s + 1) (2 * (i.val + 1) + 1) (by omega)]`.

Both sides reduce to the same expression. Establish `eS : pairSg mu Ai i = mu ⟨2 * i.val + 2, by omega⟩ 0 - mu ⟨2 * i.val + 3, by omega⟩ 0`. Unfold `pairSg pairO`. Rewrite using `[eW, eC0, eC1]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hS0 : 0 ≤ pairSg mu Ai i` using `by rw [eS]; linarith`. Establish `hSC : pairSg mu Ai i ≤ Ci i` using `by rw [eS]; linarith`. Use `⟨by rw [eW]; exact v1, ?_, by rw [eW]; exact v2, by rw [eW]; linarith, hS0, hSC, fun t ht => by rw [eC0]; exact v5 t ht, fun t ht => by rw [eC1]; exact c5 t ht⟩` and prove the remaining obligations. Establish `e : Ci i - (pairSg mu Ai i).toNat = (∑ t : Fin r, mu ⟨2 * i.val + 2, by omega⟩ t.succ - ∑ t : Fin r, mu ⟨2 * i.val + 3, by omega⟩ t.succ).toNat`. Use `Int.toNat_of_nonneg hS0` as an intermediate fact.

Use `Int.toNat_of_nonneg c2` as an intermediate fact. Rewrite `*` using `[eS]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[e]`. Conclude with `c1`.
-/
theorem pair_top {s r : ℕ} {A : ℕ} {Ai Ci : Fin s → ℕ} {mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ}
    (h : IsChain (kLetters A Ai Ci) mu) (i : Fin s) :
    Strip (fun t : Fin r => mu ⟨2 * i.val + 2, by omega⟩ t.succ) (fun t : Fin r => mu ⟨2 * i.val + 1, by omega⟩ t.succ)
        (pairW mu i.val).toNat ∧
      Strip (fun t : Fin r => mu ⟨2 * i.val + 2, by omega⟩ t.succ) (fun t : Fin r => mu ⟨2 * i.val + 3, by omega⟩ t.succ)
        (Ci i - (pairSg mu Ai i).toNat) ∧
      0 ≤ pairW mu i.val ∧ pairW mu i.val ≤ Ai i ∧ 0 ≤ pairSg mu Ai i ∧ pairSg mu Ai i ≤ Ci i ∧
      (∀ t : Fin r, t.val = 0 → mu ⟨2 * i.val + 2, by omega⟩ t.succ ≤ pairC mu i.val) ∧
      (∀ t : Fin r, t.val = 0 → mu ⟨2 * i.val + 2, by omega⟩ t.succ ≤ pairC mu (i.val + 1)) := by
  have hi := i.2
  have hV : Strip (mu ⟨2 * i.val + 2, by omega⟩) (mu ⟨2 * i.val + 1, by omega⟩) (Ai i) := by
    have := h.2 ⟨2 * i.val + 1, by omega⟩
    rw [if_pos (show (kLetters A Ai Ci).vec ⟨2 * i.val + 1, by omega⟩ = true from
      decide_eq_true (Or.inr (by show (2 * i.val + 1) % 2 = 1; omega))), kLetters_deg_odd] at this
    exact this
  have hC : Strip (mu ⟨2 * i.val + 2, by omega⟩) (mu ⟨2 * i.val + 3, by omega⟩) (Ci i) := by
    have := h.2 ⟨2 * i.val + 2, by omega⟩
    rw [if_neg (show ¬ (kLetters A Ai Ci).vec ⟨2 * i.val + 2, by omega⟩ = true from by
      intro hh
      rcases of_decide_eq_true hh with h1 | h1
      · have : 2 * i.val + 2 = 0 := h1
        omega
      · have : (2 * i.val + 2) % 2 = 1 := h1
        omega), kLetters_deg_even] at this
    exact this
  obtain ⟨v1, v2, v3, v4, v5⟩ := strip_tail hV
  obtain ⟨c1, c2, c3, c4, c5⟩ := strip_tail hC
  have eW : pairW mu i.val = ∑ t : Fin r, mu ⟨2 * i.val + 2, by omega⟩ t.succ -
      ∑ t : Fin r, mu ⟨2 * i.val + 1, by omega⟩ t.succ := by
    unfold pairW pairTail
    rw [finPos_eq (2 * s + 1) (2 * i.val + 2) (by omega), finPos_eq (2 * s + 1) (2 * i.val + 1) (by omega)]
  have eC0 : pairC mu i.val = mu ⟨2 * i.val + 1, by omega⟩ 0 := by
    unfold pairC
    rw [finPos_eq (2 * s + 1) (2 * i.val + 1) (by omega)]
  have eC1 : pairC mu (i.val + 1) = mu ⟨2 * i.val + 3, by omega⟩ 0 := by
    unfold pairC
    rw [finPos_eq (2 * s + 1) (2 * (i.val + 1) + 1) (by omega)]
    rfl
  have eS : pairSg mu Ai i = mu ⟨2 * i.val + 2, by omega⟩ 0 - mu ⟨2 * i.val + 3, by omega⟩ 0 := by
    unfold pairSg pairO
    rw [eW, eC0, eC1]
    linarith
  have hS0 : 0 ≤ pairSg mu Ai i := by rw [eS]; linarith
  have hSC : pairSg mu Ai i ≤ Ci i := by rw [eS]; linarith
  refine ⟨by rw [eW]; exact v1, ?_, by rw [eW]; exact v2, by rw [eW]; linarith, hS0, hSC,
    fun t ht => by rw [eC0]; exact v5 t ht, fun t ht => by rw [eC1]; exact c5 t ht⟩
  have e : Ci i - (pairSg mu Ai i).toNat = (∑ t : Fin r, mu ⟨2 * i.val + 2, by omega⟩ t.succ -
      ∑ t : Fin r, mu ⟨2 * i.val + 3, by omega⟩ t.succ).toNat := by
    have := Int.toNat_of_nonneg hS0
    have := Int.toNat_of_nonneg c2
    rw [eS] at *
    omega
  rw [e]
  exact c1

/- English proof (translation)
Unfold `jE`. Rewrite using `[dif_pos ⟨h, i.2⟩]`. Simplify using `only [pairLevel]`. Use `congr 2`. Conclude with `Fin.ext (by simp only [uTop]; omega)`.
-/
theorem jE_pair {s r : ℕ} (S : SegData s) (Ai : Fin s → ℕ) (mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ) (i : Fin s)
    (h : S.sigma ≤ i.val) : jE S (pairLevel S Ai mu) i.val = (pairSg mu Ai i).toNat := by
  unfold jE
  rw [dif_pos ⟨h, i.2⟩]
  simp only [pairLevel]
  congr 2
  exact Fin.ext (by simp only [uTop]; omega)

/- English proof (translation)
Use `set Ai : Fin s → ℕ := fun i => coarseA p S (digitBlock rz ry) i with hAi`. Use `set Ci : Fin s → ℕ := fun i => coarseC p S aTop (digitBlock rz ry) i with hCi`. Establish `hU : Strip (pairChain mu lam ⟨2 * s + 1, by omega⟩) (pairChain mu lam ⟨2 * s, by omega⟩) (((blockData p S aTop aPlus m (pairBlock S rz ry Ai mu lam jp)).lettersAt (pairLevel S Ai mu) jp).deg ⟨2 * s, by omega⟩)`. Rewrite using `[levU, pairChain_last, pairChain_lt mu lam (2 * s) (by omega)]`. Establish `h1` using `(inter_strip hP.2).1`.

Establish `e : (pairBlock S rz ry Ai mu lam jp).oPlus - jp = (∑ t, lam t - ∑ t : Fin r, mu (Fin.last _) t.succ).toNat` using `by show (pairD mu lam).toNat + jp - jp = _`. Rewrite using `[Nat.add_sub_cancel]`. Unfold `pairD pairTail`. Rewrite using `[finPos_eq (2 * s + 1) (2 * s + 1) (by omega)]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `h1`. Establish `hW : ∀ i : Fin s, Strip (pairChain mu lam ⟨2 * i.val + 1, by omega⟩) (pairChain mu lam ⟨2 * i.val, by omega⟩) (((blockData p S aTop aPlus m (pairBlock S rz ry Ai mu lam jp)).lettersAt (pairLevel S Ai mu) jp).deg ⟨2 * i.val, by omega⟩)`. Introduce `i`. Take `⟨t1, t2, t3, t4, t5, t6, -, -⟩` from `pair_top hP.1 i`.

Establish `n3` using `Int.toNat_of_nonneg t3`. Establish `n5` using `Int.toNat_of_nonneg t5`. Establish `eO : pairO mu Ai i = pairW mu i.val + pairSg mu Ai i` using `by unfold pairSg; ring`. Rewrite using `[levW, pairChain_lt mu lam (2 * i.val + 1) (by have := i.2; omega), pairChain_lt mu lam (2 * i.val) (by have := i.2; omega)]`. Establish `e : (if i.val < S.sigma then (pairBlock S rz ry Ai mu lam jp).w i else (pairBlock S rz ry Ai mu lam jp).o i) - jE S (pairLevel S Ai mu) i.val = (pairW mu i.val).toNat`.

Distinguish the cases in `hσ : i.val < S.sigma`. Rewrite using `[if_pos hσ, jE_S S _ hσ, Nat.sub_zero] show (if i.val < S.sigma then (pairW mu i.val).toNat else 0) = _`. Rewrite using `[if_pos hσ]`. Rewrite using `[if_neg hσ, jE_pair S Ai mu i (by omega)] show (if i.val < S.sigma then 0 else (pairO mu Ai i).toNat) - _ = _`. Rewrite using `[if_neg hσ]`.

Use `Int.toNat_of_nonneg (show 0 ≤ pairO mu Ai i by rw [eO]; omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[e]`. Conclude with `t1`. Establish `hE : ∀ i : Fin s, Strip (pairChain mu lam ⟨2 * i.val + 1, by omega⟩) (pairChain mu lam ⟨2 * i.val + 2, by omega⟩) (((blockData p S aTop aPlus m (pairBlock S rz ry Ai mu lam jp)).lettersAt (pairLevel S Ai mu) jp).deg ⟨2 * i.val + 1, by omega⟩)`.

Introduce `i`. Take `⟨t1, t2, t3, t4, t5, t6, -, -⟩` from `pair_top hP.1 i`. Rewrite using `[levE, pairChain_lt mu lam (2 * i.val + 1) (by have := i.2; omega), pairChain_lt mu lam (2 * i.val + 2) (by have := i.2; omega)]`. Establish `e : (if i.val < S.sigma then coarseC p S aTop (pairBlock S rz ry Ai mu lam jp) i - (pairBlock S rz ry Ai mu lam jp).sg i else coarseC p S aTop (pairBlock S rz ry Ai mu lam jp) i) - jE S (pairLevel S Ai mu) i.val = Ci i - (pairSg mu Ai i).toNat`. Establish `hcc : coarseC p S aTop (pairBlock S rz ry Ai mu lam jp) i = Ci i` using `rfl`.

Distinguish the cases in `hσ : i.val < S.sigma`. Rewrite using `[if_pos hσ, jE_S S _ hσ, Nat.sub_zero, hcc] show Ci i - (if i.val < S.sigma then (pairSg mu Ai i).toNat else 0) = _`. Rewrite using `[if_pos hσ]`. Rewrite using `[if_neg hσ, jE_pair S Ai mu i (by omega), hcc]`. Rewrite using `[e]`.

Conclude with `t2`. Prove the components needed by the constructor for the conclusion. Use function extensionality and compare the values at `t show pairChain mu lam ⟨0, by omega⟩ t = 0`. Rewrite using `[pairChain_lt mu lam 0 (by omega)]`. Conclude with `chain_first_tail (N := 2 * s) hP.1 (by simp [kLetters]) t`.

Introduce and unpack `⟨xv, hxv⟩`. Take `⟨i, rfl | rfl⟩ : ∃ i, xv = 2 * i ∨ xv = 2 * i + 1` from `⟨xv / 2, by omega⟩`. Rewrite using `[if_pos (by show decide ((2 * i) % 2 = 0) = true; exact decide_eq_true (by omega))]`. Distinguish the cases in `hi : i = s`. Substitute `hi` using the available equality.

Conclude with `hU`. Conclude with `hW ⟨i, by omega⟩`. Rewrite using `[if_neg (by show ¬ decide ((2 * i + 1) % 2 = 0) = true`. Introduce `hh`. Use `of_decide_eq_true hh` as an intermediate fact.

Use the proof step `omega)]`. Conclude with `hE ⟨i, by omega⟩`.
-/
theorem pair_chain (p : ℕ) {s r : ℕ} (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ)
    (rz ry : Fin s → Fin (r + 1) → ℕ) (A : ℕ) (mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ) (lam : Fin r → ℤ) (jp : ℕ)
    (hP : IsPair A (fun i => coarseA p S (digitBlock rz ry) i) (fun i => coarseC p S aTop (digitBlock rz ry) i) mu lam) :
    IsChain ((blockData p S aTop aPlus m
        (pairBlock S rz ry (fun i => coarseA p S (digitBlock rz ry) i) mu lam jp)).lettersAt
        (pairLevel S (fun i => coarseA p S (digitBlock rz ry) i) mu) jp) (pairChain mu lam) := by
  set Ai : Fin s → ℕ := fun i => coarseA p S (digitBlock rz ry) i with hAi
  set Ci : Fin s → ℕ := fun i => coarseC p S aTop (digitBlock rz ry) i with hCi
  have hU : Strip (pairChain mu lam ⟨2 * s + 1, by omega⟩) (pairChain mu lam ⟨2 * s, by omega⟩)
      (((blockData p S aTop aPlus m (pairBlock S rz ry Ai mu lam jp)).lettersAt (pairLevel S Ai mu) jp).deg
        ⟨2 * s, by omega⟩) := by
    rw [levU, pairChain_last, pairChain_lt mu lam (2 * s) (by omega)]
    have h1 := (inter_strip hP.2).1
    have e : (pairBlock S rz ry Ai mu lam jp).oPlus - jp =
        (∑ t, lam t - ∑ t : Fin r, mu (Fin.last _) t.succ).toNat := by
      show (pairD mu lam).toNat + jp - jp = _
      rw [Nat.add_sub_cancel]
      unfold pairD pairTail
      rw [finPos_eq (2 * s + 1) (2 * s + 1) (by omega)]
      rfl
    rw [e]
    exact h1
  have hW : ∀ i : Fin s, Strip (pairChain mu lam ⟨2 * i.val + 1, by omega⟩) (pairChain mu lam ⟨2 * i.val, by omega⟩)
      (((blockData p S aTop aPlus m (pairBlock S rz ry Ai mu lam jp)).lettersAt (pairLevel S Ai mu) jp).deg
        ⟨2 * i.val, by omega⟩) := by
    intro i
    obtain ⟨t1, t2, t3, t4, t5, t6, -, -⟩ := pair_top hP.1 i
    have n3 := Int.toNat_of_nonneg t3
    have n5 := Int.toNat_of_nonneg t5
    have eO : pairO mu Ai i = pairW mu i.val + pairSg mu Ai i := by unfold pairSg; ring
    rw [levW, pairChain_lt mu lam (2 * i.val + 1) (by have := i.2; omega),
      pairChain_lt mu lam (2 * i.val) (by have := i.2; omega)]
    have e : (if i.val < S.sigma then (pairBlock S rz ry Ai mu lam jp).w i else (pairBlock S rz ry Ai mu lam jp).o i) -
        jE S (pairLevel S Ai mu) i.val = (pairW mu i.val).toNat := by
      by_cases hσ : i.val < S.sigma
      · rw [if_pos hσ, jE_S S _ hσ, Nat.sub_zero]
        show (if i.val < S.sigma then (pairW mu i.val).toNat else 0) = _
        rw [if_pos hσ]
      · rw [if_neg hσ, jE_pair S Ai mu i (by omega)]
        show (if i.val < S.sigma then 0 else (pairO mu Ai i).toNat) - _ = _
        rw [if_neg hσ]
        have := Int.toNat_of_nonneg (show 0 ≤ pairO mu Ai i by rw [eO]; omega)
        omega
    rw [e]
    exact t1
  have hE : ∀ i : Fin s, Strip (pairChain mu lam ⟨2 * i.val + 1, by omega⟩) (pairChain mu lam ⟨2 * i.val + 2, by omega⟩)
      (((blockData p S aTop aPlus m (pairBlock S rz ry Ai mu lam jp)).lettersAt (pairLevel S Ai mu) jp).deg
        ⟨2 * i.val + 1, by omega⟩) := by
    intro i
    obtain ⟨t1, t2, t3, t4, t5, t6, -, -⟩ := pair_top hP.1 i
    rw [levE, pairChain_lt mu lam (2 * i.val + 1) (by have := i.2; omega),
      pairChain_lt mu lam (2 * i.val + 2) (by have := i.2; omega)]
    have e : (if i.val < S.sigma then coarseC p S aTop (pairBlock S rz ry Ai mu lam jp) i -
          (pairBlock S rz ry Ai mu lam jp).sg i else coarseC p S aTop (pairBlock S rz ry Ai mu lam jp) i) -
        jE S (pairLevel S Ai mu) i.val = Ci i - (pairSg mu Ai i).toNat := by
      have hcc : coarseC p S aTop (pairBlock S rz ry Ai mu lam jp) i = Ci i := rfl
      by_cases hσ : i.val < S.sigma
      · rw [if_pos hσ, jE_S S _ hσ, Nat.sub_zero, hcc]
        show Ci i - (if i.val < S.sigma then (pairSg mu Ai i).toNat else 0) = _
        rw [if_pos hσ]
      · rw [if_neg hσ, jE_pair S Ai mu i (by omega), hcc]
    rw [e]
    exact t2
  constructor
  · funext t
    show pairChain mu lam ⟨0, by omega⟩ t = 0
    rw [pairChain_lt mu lam 0 (by omega)]
    exact chain_first_tail (N := 2 * s) hP.1 (by simp [kLetters]) t
  · rintro ⟨xv, hxv⟩
    obtain ⟨i, rfl | rfl⟩ : ∃ i, xv = 2 * i ∨ xv = 2 * i + 1 := ⟨xv / 2, by omega⟩
    · rw [if_pos (by show decide ((2 * i) % 2 = 0) = true; exact decide_eq_true (by omega))]
      by_cases hi : i = s
      · subst hi
        exact hU
      · exact hW ⟨i, by omega⟩
    · rw [if_neg (by
        show ¬ decide ((2 * i + 1) % 2 = 0) = true
        intro hh
        have := of_decide_eq_true hh
        omega)]
      exact hE ⟨i, by omega⟩

/- English proof (translation)
Introduce `X _ _ _ _ j m _ _ rz ry _ t ht`. Conclude with `pair_chain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) m rz ry _ t.1 t.2.1 t.2.2 ht.1.1`.
-/
theorem kept_chain_at (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : KeptChainAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ _ _ _ j m _ _ rz ry _ t ht
  exact pair_chain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) m rz ry _ t.1 t.2.1 t.2.2 ht.1.1

def KeptPairsBeyond : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => KeptPairAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc
def KeptLevelsBeyond : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => KeptLevelAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc
def KeptChainsBeyond : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => KeptChainAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc
def KeptThresholdsBeyond : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => KeptThresholdAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

/- English proof (translation)
Introduce `X _inst hD hH hC j m hm hcm rz ry hd t ht`. Conclude with `⟨⟨h1 X hD hH hC j m hm hcm rz ry hd t ht, rfl, rfl⟩, h2 X hD hH hC j m hm hcm rz ry hd t ht, h3 X hD hH hC j m hm hcm rz ry hd t ht, h4 X hD hH hC j m hm hcm rz ry hd t ht⟩`.
-/
theorem kept_block_at_of_pair_level_chain_threshold {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (h1 : KeptPairAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc)
    (h2 : KeptLevelAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) (h3 : KeptChainAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc)
    (h4 : KeptThresholdAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) : KeptBlockAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _inst hD hH hC j m hm hcm rz ry hd t ht
  exact ⟨⟨h1 X hD hH hC j m hm hcm rz ry hd t ht, rfl, rfl⟩, h2 X hD hH hC j m hm hcm rz ry hd t ht,
    h3 X hD hH hC j m hm hcm rz ry hd t ht, h4 X hD hH hC j m hm hcm rz ry hd t ht⟩

/- English proof (translation)
Introduce `Cc _` and use `⟨1, one_pos, fun C0 _ => ⟨1, one_pos, fun CE1 CE2 _ _ _ _ => ⟨1, one_pos, fun CYb Cde Ck CD Cb _ _ _ _ _ => kept_chain_at C0 CYb Cde Ck CD Cb CE1 CE2 Cc⟩⟩⟩`.
-/
theorem kept_chain_holds : KeptChainsBeyond := fun Cc _ => ⟨1, one_pos, fun C0 _ => ⟨1, one_pos, fun CE1 CE2 _ _ _ _ =>
  ⟨1, one_pos, fun CYb Cde Ck CD Cb _ _ _ _ _ => kept_chain_at C0 CYb Cde Ck CD Cb CE1 CE2 Cc⟩⟩⟩

/- English proof (translation)
Use `set Ai : Fin s → ℕ := fun i => coarseA p S (digitBlock rz ry) i with hAi`. Use `set Ci : Fin s → ℕ := fun i => coarseC p S aTop (digitBlock rz ry) i with hCi`. Use `set b := pairBlock S rz ry Ai mu lam jp with hb`. Use `⟨fun l => ?_, le_min ?_ hjp⟩` and prove the remaining obligations. Establish `hl : l.val < s - S.sigma` using `l.2`.

Take `⟨-, -, t3, -, t5, t6, -, -⟩` from `pair_top hP.1 (uTop S l)`. Establish `hσ : ¬ (uTop S l).val < S.sigma` using `by show ¬ S.sigma + l.val < S.sigma; omega`. Establish `e1` using `segment_chain_degree_even p S aTop b ((blockData p S aTop aPlus m b).letterAt ((blockData p S aTop aPlus m b).T.pos l)) (uTop S l) (by show min (2 * (S.sigma + l.val)) (2 * s + 1 - 1) = 2 * (S.sigma + l.val); omega)`. Establish `e2` using `chain_deg_E p S aTop b ((blockData p S aTop aPlus m b).letterAt ((blockData p S aTop aPlus m b).T.pos l + 1)) (uTop S l) (by show min (2 * (S.sigma + l.val) + 1) (2 * s + 1 - 1) = 2 * (S.sigma + l.val) + 1; omega)`. Rewrite `e1`, `e2` using `[if_neg hσ]`.

Establish `eO : pairO mu Ai (uTop S l) = pairW mu (uTop S l).val + pairSg mu Ai (uTop S l)` using `by unfold pairSg; ring`. Establish `n5` using `Int.toNat_of_nonneg t5`. Establish `g1 : pairLevel S Ai mu l ≤ b.o (uTop S l)` using `by show (pairSg mu Ai (uTop S l)).toNat ≤ (if (uTop S l).val < S.sigma then 0 else (pairO mu Ai (uTop S l)).toNat)`. Rewrite using `[if_neg hσ]`. Use `Int.toNat_of_nonneg (show 0 ≤ pairO mu Ai (uTop S l) by rw [eO]; omega)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `g2 : pairLevel S Ai mu l ≤ coarseC p S aTop b (uTop S l)` using `by show (pairSg mu Ai (uTop S l)).toNat ≤ Ci (uTop S l)`. Use linear arithmetic over natural numbers and integers. Conclude with `⟨le_of_le_of_eq g1 e1.symm, le_of_le_of_eq g2 e2.symm⟩`. Establish `e` using `chain_deg_U p S aTop b (blockData p S aTop aPlus m b).uPos rfl`.

Conclude with `le_of_le_of_eq (Nat.le_add_left jp _) e.symm`.
-/
theorem pair_level (p : ℕ) {s r : ℕ} (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ)
    (rz ry : Fin s → Fin (r + 1) → ℕ) (A : ℕ) (mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ) (lam : Fin r → ℤ) (jp : ℕ)
    (hP : IsPair A (fun i => coarseA p S (digitBlock rz ry) i) (fun i => coarseC p S aTop (digitBlock rz ry) i) mu lam)
    (hjp : jp ≤ S.bPlus) :
    (blockData p S aTop aPlus m
        (pairBlock S rz ry (fun i => coarseA p S (digitBlock rz ry) i) mu lam jp)).LevelOK
        (pairLevel S (fun i => coarseA p S (digitBlock rz ry) i) mu) jp := by
  set Ai : Fin s → ℕ := fun i => coarseA p S (digitBlock rz ry) i with hAi
  set Ci : Fin s → ℕ := fun i => coarseC p S aTop (digitBlock rz ry) i with hCi
  set b := pairBlock S rz ry Ai mu lam jp with hb
  refine ⟨fun l => ?_, le_min ?_ hjp⟩
  · have hl : l.val < s - S.sigma := l.2
    obtain ⟨-, -, t3, -, t5, t6, -, -⟩ := pair_top hP.1 (uTop S l)
    have hσ : ¬ (uTop S l).val < S.sigma := by show ¬ S.sigma + l.val < S.sigma; omega
    have e1 := segment_chain_degree_even p S aTop b
      ((blockData p S aTop aPlus m b).letterAt ((blockData p S aTop aPlus m b).T.pos l)) (uTop S l)
      (by show min (2 * (S.sigma + l.val)) (2 * s + 1 - 1) = 2 * (S.sigma + l.val); omega)
    have e2 := chain_deg_E p S aTop b
      ((blockData p S aTop aPlus m b).letterAt ((blockData p S aTop aPlus m b).T.pos l + 1)) (uTop S l)
      (by show min (2 * (S.sigma + l.val) + 1) (2 * s + 1 - 1) = 2 * (S.sigma + l.val) + 1; omega)
    rw [if_neg hσ] at e1 e2
    have eO : pairO mu Ai (uTop S l) = pairW mu (uTop S l).val + pairSg mu Ai (uTop S l) := by unfold pairSg; ring
    have n5 := Int.toNat_of_nonneg t5
    have g1 : pairLevel S Ai mu l ≤ b.o (uTop S l) := by
      show (pairSg mu Ai (uTop S l)).toNat ≤ (if (uTop S l).val < S.sigma then 0 else (pairO mu Ai (uTop S l)).toNat)
      rw [if_neg hσ]
      have := Int.toNat_of_nonneg (show 0 ≤ pairO mu Ai (uTop S l) by rw [eO]; omega)
      omega
    have g2 : pairLevel S Ai mu l ≤ coarseC p S aTop b (uTop S l) := by
      show (pairSg mu Ai (uTop S l)).toNat ≤ Ci (uTop S l)
      omega
    exact ⟨le_of_le_of_eq g1 e1.symm, le_of_le_of_eq g2 e2.symm⟩
  · have e := chain_deg_U p S aTop b (blockData p S aTop aPlus m b).uPos rfl
    exact le_of_le_of_eq (Nat.le_add_left jp _) e.symm

/- English proof (translation)
The claim follows from `TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1) fun C0 _ _ _ _ _ CE1 CE2 _ _ hCc hC0 _ h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 => by intro X _ hD hI hc j m _ _ rz ry _ t ht have hs := std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI h …`.
-/
theorem kept_levels_hold : KeptLevelsBeyond :=
  TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1)
    fun C0 _ _ _ _ _ CE1 CE2 _ _ hCc hC0 _ h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 => by
      intro X _ hD hI hc j m _ _ rz ry _ t ht
      have hs := std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc
      have hk : 0 < X.k := by unfold Loc.k; positivity
      have hLa : X.La C0 ≤ X.k := by
        have a1 := hs.LaN
        have a2 := hs.N2
        have a3 := hs.La1
        nlinarith
      have hB : (0 : ℝ) ≤ ((X.seg C0 CE1 CE2 j).bPlus : ℝ) := Nat.cast_nonneg _
      have hjp : t.2.2 ≤ (X.seg C0 CE1 CE2 j).bPlus := by
        refine le_trans ht.2 (Nat.floor_le_of_le ?_)
        rw [div_le_iff₀ hk]
        nlinarith
      exact pair_level X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) m rz ry _ t.1 t.2.1 t.2.2
        ht.1.1 hjp

/- English proof (translation)
Introduce `Cc hCc`. Take `⟨T0, hT0, hP0⟩` from `hP Cc hCc`. Take `⟨U0, _, hQ0⟩` from `hQ Cc hCc`. Use `⟨max T0 U0, lt_max_of_lt_left hT0, fun C0 hC0 => ?_⟩` and prove the remaining obligations. Take `⟨T1, hT1, hP1⟩` from `hP0 C0 (le_trans (le_max_left _ _) hC0)`.

Take `⟨U1, _, hQ1⟩` from `hQ0 C0 (le_trans (le_max_right _ _) hC0)`. Use `⟨max T1 U1, lt_max_of_lt_left hT1, fun CE1 CE2 Cm a1 a2 a3 => ?_⟩` and prove the remaining obligations. Take `⟨T2, hT2, hP2⟩` from `hP1 CE1 CE2 Cm (le_trans (le_max_left _ _) a1) (le_trans (le_max_left _ _) a2) (le_trans (le_max_left _ _) a3)`. Take `⟨U2, _, hQ2⟩` from `hQ1 CE1 CE2 Cm (le_trans (le_max_right _ _) a1) (le_trans (le_max_right _ _) a2) (le_trans (le_max_right _ _) a3)`. Use `⟨max T2 U2, lt_max_of_lt_left hT2, fun CYb Cde Ck CD Cb b1 b2 b3 b4 b5 => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Conclude with `hP2 CYb Cde Ck CD Cb (le_trans (le_max_left _ _) b1) (le_trans (le_max_left _ _) b2) (le_trans (le_max_left _ _) b3) (le_trans (le_max_left _ _) b4) (le_trans (le_max_left _ _) b5)`. Conclude with `hQ2 CYb Cde Ck CD Cb (le_trans (le_max_right _ _) b1) (le_trans (le_max_right _ _) b2) (le_trans (le_max_right _ _) b3) (le_trans (le_max_right _ _) b4) (le_trans (le_max_right _ _) b5)`.
-/
private theorem transported_and {P Q : (ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop)} (hP : TransportedAlt P) (hQ : TransportedAlt Q) :
    TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc =>
      P C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc ∧ Q C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc := by
  intro Cc hCc
  obtain ⟨T0, hT0, hP0⟩ := hP Cc hCc
  obtain ⟨U0, _, hQ0⟩ := hQ Cc hCc
  refine ⟨max T0 U0, lt_max_of_lt_left hT0, fun C0 hC0 => ?_⟩
  obtain ⟨T1, hT1, hP1⟩ := hP0 C0 (le_trans (le_max_left _ _) hC0)
  obtain ⟨U1, _, hQ1⟩ := hQ0 C0 (le_trans (le_max_right _ _) hC0)
  refine ⟨max T1 U1, lt_max_of_lt_left hT1, fun CE1 CE2 Cm a1 a2 a3 => ?_⟩
  obtain ⟨T2, hT2, hP2⟩ := hP1 CE1 CE2 Cm (le_trans (le_max_left _ _) a1) (le_trans (le_max_left _ _) a2)
    (le_trans (le_max_left _ _) a3)
  obtain ⟨U2, _, hQ2⟩ := hQ1 CE1 CE2 Cm (le_trans (le_max_right _ _) a1) (le_trans (le_max_right _ _) a2)
    (le_trans (le_max_right _ _) a3)
  refine ⟨max T2 U2, lt_max_of_lt_left hT2, fun CYb Cde Ck CD Cb b1 b2 b3 b4 b5 => ⟨?_, ?_⟩⟩
  · exact hP2 CYb Cde Ck CD Cb (le_trans (le_max_left _ _) b1) (le_trans (le_max_left _ _) b2)
      (le_trans (le_max_left _ _) b3) (le_trans (le_max_left _ _) b4) (le_trans (le_max_left _ _) b5)
  · exact hQ2 CYb Cde Ck CD Cb (le_trans (le_max_right _ _) b1) (le_trans (le_max_right _ _) b2)
      (le_trans (le_max_right _ _) b3) (le_trans (le_max_right _ _) b4) (le_trans (le_max_right _ _) b5)

/- English proof (translation)
Introduce `Cc hCc`. Take `⟨T0, hT0, h0⟩` from `hP Cc hCc`. Use `⟨T0, hT0, fun C0 hC0 => ?_⟩` and prove the remaining obligations. Take `⟨T1, hT1, h1⟩` from `h0 C0 hC0`. Use `⟨T1, hT1, fun CE1 CE2 Cm a1 a2 a3 => ?_⟩` and prove the remaining obligations.

Take `⟨T2, hT2, h2⟩` from `h1 CE1 CE2 Cm a1 a2 a3`. Conclude with `⟨T2, hT2, fun CYb Cde Ck CD Cb b1 b2 b3 b4 b5 => h _ _ _ _ _ _ _ _ _ _ (h2 CYb Cde Ck CD Cb b1 b2 b3 b4 b5)⟩`.
-/
private theorem transported_mono {P Q : (ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop)}
    (h : ∀ C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc, P C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc → Q C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc)
    (hP : TransportedAlt P) : TransportedAlt Q := by
  intro Cc hCc
  obtain ⟨T0, hT0, h0⟩ := hP Cc hCc
  refine ⟨T0, hT0, fun C0 hC0 => ?_⟩
  obtain ⟨T1, hT1, h1⟩ := h0 C0 hC0
  refine ⟨T1, hT1, fun CE1 CE2 Cm a1 a2 a3 => ?_⟩
  obtain ⟨T2, hT2, h2⟩ := h1 CE1 CE2 Cm a1 a2 a3
  exact ⟨T2, hT2, fun CYb Cde Ck CD Cb b1 b2 b3 b4 b5 => h _ _ _ _ _ _ _ _ _ _ (h2 CYb Cde Ck CD Cb b1 b2 b3 b4 b5)⟩

/- English proof (translation)
The claim follows from `transported_mono (fun _ _ _ _ _ _ _ _ _ _ h => kept_block_at_of_pair_level_chain_threshold h.1 h.2.1 h.2.2.1 h.2.2.2) (transported_and h1 (transported_and h2 (transported_and kept_chain_holds h4)))`.
-/
theorem kept_blocks_of_parts (h1 : KeptPairsBeyond) (h2 : KeptLevelsBeyond) (h4 : KeptThresholdsBeyond) : KeptBlocksBeyondThreshold := transported_mono (fun _ _ _ _ _ _ _ _ _ _ h => kept_block_at_of_pair_level_chain_threshold h.1 h.2.1 h.2.2.1 h.2.2.2)
  (transported_and h1 (transported_and h2 (transported_and kept_chain_holds h4)))

/- English proof (translation)
Take `⟨h0, hs⟩` from `h`. Establish `h1` using `hs 0`. Rewrite `h1` using `[if_pos (by simp [kLetters])]`. Take `⟨ha, hb, h3⟩` from `h1`. Simplify using `only [Fin.castSucc_zero, h0, Pi.zero_apply, Finset.sum_const_zero, sub_zero] at ha hb h3`.

Establish `ht : ∀ t : Fin r, mu (0 : Fin (2 * s + 1)).succ t.succ = 0` using `fun t => le_antisymm (hb t.castSucc t.succ (by simp only [Fin.coe_castSucc, Fin.val_succ])) (ha t.succ)`. Rewrite `h3` using `[Fin.sum_univ_succ]`. Simplify using `only [ht, Finset.sum_const_zero, add_zero] at h3`. Establish `e : finPos (2 * s + 1) (2 * 0 + 1) = (0 : Fin (2 * s + 1)).succ` using `Fin.ext (by simp only [finPos, Fin.val_succ, Fin.val_zero]; omega)`. Unfold `pairC`.

Rewrite using `[e, h3]`. Simplify using `[kLetters]`.
-/
theorem pairC_zero {s r : ℕ} {A : ℕ} {Ai Ci : Fin s → ℕ} {mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ}
    (h : IsChain (kLetters A Ai Ci) mu) : pairC mu 0 = A := by
  obtain ⟨h0, hs⟩ := h
  have h1 := hs 0
  rw [if_pos (by simp [kLetters])] at h1
  obtain ⟨ha, hb, h3⟩ := h1
  simp only [Fin.castSucc_zero, h0, Pi.zero_apply, Finset.sum_const_zero, sub_zero] at ha hb h3
  have ht : ∀ t : Fin r, mu (0 : Fin (2 * s + 1)).succ t.succ = 0 := fun t =>
    le_antisymm (hb t.castSucc t.succ (by simp only [Fin.coe_castSucc, Fin.val_succ])) (ha t.succ)
  rw [Fin.sum_univ_succ] at h3
  simp only [ht, Finset.sum_const_zero, add_zero] at h3
  have e : finPos (2 * s + 1) (2 * 0 + 1) = (0 : Fin (2 * s + 1)).succ :=
    Fin.ext (by simp only [finPos, Fin.val_succ, Fin.val_zero]; omega)
  unfold pairC
  rw [e, h3]
  simp [kLetters]

/- English proof (translation)
Take `⟨-, -, hw0, -, hs0, -, -, -⟩` from `pair_top h i`. Establish `hO : pairO mu Ai i = pairW mu i.val + pairSg mu Ai i`. Simplify using `only [pairSg]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [oEff, pairBlock]`.

Use `split_ifs with hi`. Rewrite using `[Nat.cast_add, Int.toNat_of_nonneg hw0, Int.toNat_of_nonneg hs0]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `Int.toNat_of_nonneg (by rw [hO]; linarith)`.
-/
theorem oEff_pair {s r : ℕ} (S : SegData s) (rz ry : Fin s → Fin (r + 1) → ℕ) {A : ℕ} {Ai Ci : Fin s → ℕ}
    {mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ} (lam : Fin r → ℤ) (jp : ℕ) (h : IsChain (kLetters A Ai Ci) mu) (i : Fin s) :
    (oEff S (pairBlock S rz ry Ai mu lam jp) i : ℤ) = pairO mu Ai i := by
  obtain ⟨-, -, hw0, -, hs0, -, -, -⟩ := pair_top h i
  have hO : pairO mu Ai i = pairW mu i.val + pairSg mu Ai i := by
    simp only [pairSg]; ring
  simp only [oEff, pairBlock]
  split_ifs with hi
  · rw [Nat.cast_add, Int.toNat_of_nonneg hw0, Int.toNat_of_nonneg hs0]
    linarith
  · exact Int.toNat_of_nonneg (by rw [hO]; linarith)

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `zero => rw [cap_zero, pairC_zero h]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `succ l ih`. Establish `ih'` using `ih (by omega)`.

Establish `hc` using `cap_succ p S (pairBlock S rz ry (fun i => coarseA p S (digitBlock rz ry) i) mu lam jp) ⟨l, by omega⟩`. Establish `ho` using `oEff_pair S rz ry lam jp h ⟨l, by omega⟩`. Establish `ha : coarseA p S (pairBlock S rz ry (fun i => coarseA p S (digitBlock rz ry) i) mu lam jp) ⟨l, by omega⟩ = coarseA p S (digitBlock rz ry) ⟨l, by omega⟩` using `rfl`. Establish `hO : pairO mu (fun i => coarseA p S (digitBlock rz ry) i) ⟨l, by omega⟩ = pairC mu l + (coarseA p S (digitBlock rz ry) ⟨l, by omega⟩ : ℤ) - pairC mu (l + 1)` using `rfl`. Simplify using `only at hc`.

Rewrite using `[hc, ih', ho, ha, hO]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cap_pair (p : ℕ) {s r : ℕ} (S : SegData s) (aTop : Fin s → ℕ) (rz ry : Fin s → Fin (r + 1) → ℕ) {A : ℕ}
    {mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ} (lam : Fin r → ℤ) (jp : ℕ)
    (h : IsChain (kLetters A (fun i => coarseA p S (digitBlock rz ry) i) (fun i => coarseC p S aTop (digitBlock rz ry) i)) mu)
    (l : ℕ) (hl : l ≤ s) :
    cap p S (pairBlock S rz ry (fun i => coarseA p S (digitBlock rz ry) i) mu lam jp) l = S.A0 p - A + pairC mu l := by
  induction l with
  | zero => rw [cap_zero, pairC_zero h]; ring
  | succ l ih =>
    have ih' := ih (by omega)
    have hc := cap_succ p S (pairBlock S rz ry (fun i => coarseA p S (digitBlock rz ry) i) mu lam jp) ⟨l, by omega⟩
    have ho := oEff_pair S rz ry lam jp h ⟨l, by omega⟩
    have ha : coarseA p S (pairBlock S rz ry (fun i => coarseA p S (digitBlock rz ry) i) mu lam jp) ⟨l, by omega⟩ =
        coarseA p S (digitBlock rz ry) ⟨l, by omega⟩ := rfl
    have hO : pairO mu (fun i => coarseA p S (digitBlock rz ry) i) ⟨l, by omega⟩ =
        pairC mu l + (coarseA p S (digitBlock rz ry) ⟨l, by omega⟩ : ℤ) - pairC mu (l + 1) := rfl
    simp only at hc
    rw [hc, ih', ho, ha, hO]
    ring

/- English proof (translation)
Use `set Ai : Fin s → ℕ := fun i => coarseA p S (digitBlock rz ry) i with hAi`. Use `set b := pairBlock S rz ry Ai mu lam jp with hb`. Establish `h0 : ((0 : Fin r) : ℕ) = 0` using `by simp`. Introduce `k`. Establish `hfl : ∀ l, l ≤ s → pairC mu l ≤ ⌊((cap p S b l : ℤ) : ℝ) - m⌋`.

Introduce `l hl`. Rewrite using `[Int.le_floor, cap_pair p S aTop rz ry lam jp hP.1 l hl]`. Use `push_cast`. Move the coercions through the operations in `at hm`. Combine the linear equalities and inequalities to obtain the conclusion.

Distinguish the cases in `hk : k.val < S.t`. Establish `hks : k.val < s - S.sigma` using `hk`. Establish `eJ : (blockData p S aTop aPlus m b).T.J k = 2 * (S.sigma + k.val) + 1` using `by show (if h : (k : ℕ) < S.t then 2 * (uTop S ⟨k, h⟩ : ℕ) + 1 else 2 * s + 1) = _`. Rewrite using `[dif_pos hk]`. Both sides reduce to the same expression.

Establish `eT : (blockData p S aTop aPlus m b).T.thr k = ((⌊((cap p S b (S.sigma + k.val) : ℤ) : ℝ) - m⌋ : ℤ) : WithTop ℤ)` using `by show (segmentCapacities p S b k).map (fun x : ℤ => ⌊(x : ℝ) - m⌋) = _`. Unfold `segmentCapacities`. Rewrite using `[dif_pos hk]`. Both sides reduce to the same expression. Rewrite using `[eJ, eT, WithTop.coe_le_coe, finPos_eq (2 * s + 1) (2 * (S.sigma + k.val) + 1) (by omega), pairChain_lt mu lam (2 * (S.sigma + k.val) + 1) (by omega)]`.

Take `⟨-, -, -, -, -, -, t7, -⟩` from `pair_top hP.1 (⟨S.sigma + k.val, by omega⟩ : Fin s)`. Conclude with `le_trans (t7 0 h0) (hfl _ (by omega))`. Establish `eJ : (blockData p S aTop aPlus m b).T.J k = 2 * s + 1` using `by show (if h : (k : ℕ) < S.t then 2 * (uTop S ⟨k, h⟩ : ℕ) + 1 else 2 * s + 1) = _`. Rewrite using `[dif_neg hk]`. Establish `eT : (blockData p S aTop aPlus m b).T.thr k = ((⌊((cap p S b s : ℤ) : ℝ) - m⌋ : ℤ) : WithTop ℤ)` using `by show (segmentCapacities p S b k).map (fun x : ℤ => ⌊(x : ℝ) - m⌋) = _`.

Unfold `segmentCapacities`. Rewrite using `[dif_neg hk]`. Both sides reduce to the same expression. Rewrite using `[eJ, eT, WithTop.coe_le_coe, finPos_eq (2 * s + 1) (2 * s + 1) (by omega), pairChain_last]`. Establish `h3` using `(inter_strip hP.2).2.2 0 h0`.

Establish `eC : pairC mu s = mu (Fin.last _) 0`. Unfold `pairC`. Rewrite using `[finPos_eq (2 * s + 1) (2 * s + 1) (by omega)]`. Both sides reduce to the same expression. Conclude with `le_trans (eC ▸ h3) (hfl s le_rfl)`.
-/
theorem pair_thr (p : ℕ) {s r : ℕ} [NeZero r] (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ)
    (rz ry : Fin s → Fin (r + 1) → ℕ) (A : ℕ) (mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ) (lam : Fin r → ℤ) (jp : ℕ)
    (hP : IsPair A (fun i => coarseA p S (digitBlock rz ry) i) (fun i => coarseC p S aTop (digitBlock rz ry) i) mu lam)
    (hm : m ≤ ((S.A0 p - A : ℤ) : ℝ)) :
    ChainOK (blockData p S aTop aPlus m
        (pairBlock S rz ry (fun i => coarseA p S (digitBlock rz ry) i) mu lam jp)).T.J
      (blockData p S aTop aPlus m
        (pairBlock S rz ry (fun i => coarseA p S (digitBlock rz ry) i) mu lam jp)).T.thr (pairChain mu lam) := by
  set Ai : Fin s → ℕ := fun i => coarseA p S (digitBlock rz ry) i with hAi
  set b := pairBlock S rz ry Ai mu lam jp with hb
  have h0 : ((0 : Fin r) : ℕ) = 0 := by simp
  intro k
  have hfl : ∀ l, l ≤ s → pairC mu l ≤ ⌊((cap p S b l : ℤ) : ℝ) - m⌋ := by
    intro l hl
    rw [Int.le_floor, cap_pair p S aTop rz ry lam jp hP.1 l hl]
    push_cast
    push_cast at hm
    linarith
  by_cases hk : k.val < S.t
  · have hks : k.val < s - S.sigma := hk
    have eJ : (blockData p S aTop aPlus m b).T.J k = 2 * (S.sigma + k.val) + 1 := by
      show (if h : (k : ℕ) < S.t then 2 * (uTop S ⟨k, h⟩ : ℕ) + 1 else 2 * s + 1) = _
      rw [dif_pos hk]
      rfl
    have eT : (blockData p S aTop aPlus m b).T.thr k =
        ((⌊((cap p S b (S.sigma + k.val) : ℤ) : ℝ) - m⌋ : ℤ) : WithTop ℤ) := by
      show (segmentCapacities p S b k).map (fun x : ℤ => ⌊(x : ℝ) - m⌋) = _
      unfold segmentCapacities
      rw [dif_pos hk]
      rfl
    rw [eJ, eT, WithTop.coe_le_coe, finPos_eq (2 * s + 1) (2 * (S.sigma + k.val) + 1) (by omega),
      pairChain_lt mu lam (2 * (S.sigma + k.val) + 1) (by omega)]
    obtain ⟨-, -, -, -, -, -, t7, -⟩ := pair_top hP.1 (⟨S.sigma + k.val, by omega⟩ : Fin s)
    exact le_trans (t7 0 h0) (hfl _ (by omega))
  · have eJ : (blockData p S aTop aPlus m b).T.J k = 2 * s + 1 := by
      show (if h : (k : ℕ) < S.t then 2 * (uTop S ⟨k, h⟩ : ℕ) + 1 else 2 * s + 1) = _
      rw [dif_neg hk]
    have eT : (blockData p S aTop aPlus m b).T.thr k = ((⌊((cap p S b s : ℤ) : ℝ) - m⌋ : ℤ) : WithTop ℤ) := by
      show (segmentCapacities p S b k).map (fun x : ℤ => ⌊(x : ℝ) - m⌋) = _
      unfold segmentCapacities
      rw [dif_neg hk]
      rfl
    rw [eJ, eT, WithTop.coe_le_coe, finPos_eq (2 * s + 1) (2 * s + 1) (by omega), pairChain_last]
    have h3 := (inter_strip hP.2).2.2 0 h0
    have eC : pairC mu s = mu (Fin.last _) 0 := by
      unfold pairC
      rw [finPos_eq (2 * s + 1) (2 * s + 1) (by omega)]
      rfl
    exact le_trans (eC ▸ h3) (hfl s le_rfl)

/- English proof (translation)
The claim follows from `TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1) fun C0 _ _ _ _ _ CE1 CE2 _ _ hCc hC0 _ h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 => by intro X _ hD hI hc j m _ hmA rz ry _ t ht have hs := std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI …`.
-/
theorem kept_thresholds_hold : KeptThresholdsBeyond :=
  TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1)
    fun C0 _ _ _ _ _ CE1 CE2 _ _ hCc hC0 _ h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 => by
      intro X _ hD hI hc j m _ hmA rz ry _ t ht
      have hs := std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc
      have hA0 : (0 : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) := by
        refine le_trans ?_ (hs.half_ratio_le_segment_base_of_std j)
        have := hs.apos
        have := hs.Q1
        positivity
      have he : (X.N1 : ℝ) * X.La C0 / X.k ≤ 1 := by
        have a1 := hs.LaK
        have a2 := hs.de6
        have e : 40 * (X.N1 : ℝ) * X.La C0 / X.k = 40 * ((X.N1 : ℝ) * X.La C0 / X.k) := by ring
        rw [e] at a1
        linarith
      have hle : (⌈m⌉₊ : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) := by
        refine le_trans hmA ?_
        have e : ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * X.N1 * X.La C0 / X.k =
            ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * ((X.N1 : ℝ) * X.La C0 / X.k) := by ring
        rw [e]
        nlinarith
      have hleZ : ((⌈m⌉₊ : ℕ) : ℤ) ≤ (X.seg C0 CE1 CE2 j).A0 X.p := by exact_mod_cast hle
      refine pair_thr X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) m rz ry _ t.1 t.2.1 t.2.2
        ht.1.1 ?_
      rw [Int.toNat_of_nonneg (by omega)]
      have := Nat.le_ceil m
      push_cast
      linarith

/- English proof (translation)
The claim follows from `kept_blocks_of_parts h1 kept_levels_hold kept_thresholds_hold`.
-/
theorem kept_blocks_of_kept_pairs (h1 : KeptPairsBeyond) : KeptBlocksBeyondThreshold := kept_blocks_of_parts h1 kept_levels_hold kept_thresholds_hold

def PairUAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ),
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      ∀ A : ℕ, ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * (1 - X.N1 * X.La C0 / X.k) ≤ (A : ℝ) →
        (A : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) →
      ∀ (mu : Fin (2 * segS X.TT j + 1 + 1) → Fin (X.m + 1) → ℤ) (lam : Fin X.m → ℤ),
        IsPair A (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) mu lam →
        KeptPair X.p (X.La C0) (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) mu lam →
        ∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).sigma ≤ i.val →
          pairO mu (clA C0 CE1 CE2 X j rz ry) i ≤ (clA C0 CE1 CE2 X j rz ry i : ℤ) ∧
          ((pairO mu (clA C0 CE1 CE2 X j rz ry) i : ℤ) : ℝ) ≤
            ((pairC mu i.val : ℤ) : ℝ) + X.La C0 * (clA C0 CE1 CE2 X j rz ry i : ℝ) / X.k

def PairSAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ),
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      ∀ A : ℕ, ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * (1 - X.N1 * X.La C0 / X.k) ≤ (A : ℝ) →
        (A : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) →
      ∀ (mu : Fin (2 * segS X.TT j + 1 + 1) → Fin (X.m + 1) → ℤ) (lam : Fin X.m → ℤ),
        IsPair A (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) mu lam →
        KeptPair X.p (X.La C0) (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) mu lam →
        ∀ i : Fin (segS X.TT j), i.val < (X.seg C0 CE1 CE2 j).sigma →
          ((pairO mu (clA C0 CE1 CE2 X j rz ry) i : ℤ) : ℝ) ≤
            (clA C0 CE1 CE2 X j rz ry i : ℝ) * (1 + 4 / (X.p : ℝ) ^ 2) + X.La C0 * ((pairC mu i.val : ℤ) : ℝ) / X.k ∧
          ((pairSg mu (clA C0 CE1 CE2 X j rz ry) i : ℤ) : ℝ) ≤
            2 * X.La C0 * ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) / X.k

def PairXAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ),
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      ∀ A : ℕ, ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * (1 - X.N1 * X.La C0 / X.k) ≤ (A : ℝ) →
        (A : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) →
      ∀ (mu : Fin (2 * segS X.TT j + 1 + 1) → Fin (X.m + 1) → ℤ) (lam : Fin X.m → ℤ),
        IsPair A (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) mu lam →
        KeptPair X.p (X.La C0) (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) mu lam →
        ((pairD mu lam : ℤ) : ℝ) ≤ ((pairC mu (segS X.TT j) : ℤ) : ℝ) +
          X.La C0 / X.k * ∑ i, (clC C0 CE1 CE2 X j rz ry i : ℝ)

def RestPairU : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => PairUAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc
def RestPairS : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => PairSAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc
def RestPairX : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => PairXAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

/- English proof (translation)
Introduce `X _ hD hI hc j m hm hmA rz ry hd t ht`. Establish `hs` using `hstd X hD hI hc`. Take `⟨⟨hP, hK⟩, hjp⟩` from `ht`. Establish `hk : 0 < X.k` using `by unfold Loc.k; positivity`. Establish `hkk : X.k = (X.m : ℝ) + 1` using `rfl`.

Establish `hLa0 : 0 ≤ X.La C0` using `le_trans zero_le_one hs.La1`. Establish `hA0 : (0 : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ)`. Use `le_trans ?_ (hs.half_ratio_le_segment_base_of_std j)` and prove the remaining obligations. Use `hs.apos` as an intermediate fact. Use `hs.Q1` as an intermediate fact.

Check the signs of the components of the expression. Establish `he : (X.N1 : ℝ) * X.La C0 / X.k ≤ 1`. Establish `a1` using `hs.LaK`. Establish `a2` using `hs.de6`. Establish `e : 40 * (X.N1 : ℝ) * X.La C0 / X.k = 40 * ((X.N1 : ℝ) * X.La C0 / X.k)` using `by ring`.

Rewrite `a1` using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e2 : ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * X.N1 * X.La C0 / X.k = ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * ((X.N1 : ℝ) * X.La C0 / X.k)` using `by ring`. Establish `hle : (⌈m⌉₊ : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ)`. Use `le_trans hmA ?_` and prove the remaining obligations.

Rewrite using `[e2]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hleZ : ((⌈m⌉₊ : ℕ) : ℤ) ≤ (X.seg C0 CE1 CE2 j).A0 X.p` using `by exact_mod_cast hle`. Use `set A : ℕ := ((X.seg C0 CE1 CE2 j).A0 X.p - (⌈m⌉₊ : ℤ)).toNat with hA`. Establish `hAz : (A : ℤ) = (X.seg C0 CE1 CE2 j).A0 X.p - (⌈m⌉₊ : ℤ)` using `Int.toNat_of_nonneg (by omega)`.

Establish `hAr : (A : ℝ) = ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) - (⌈m⌉₊ : ℝ)` using `by exact_mod_cast hAz`. Establish `hA1 : ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * (1 - X.N1 * X.La C0 / X.k) ≤ (A : ℝ)`. Rewrite using `[hAr]`. Rewrite `hmA` using `[e2]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hA2 : (A : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ)`. Rewrite using `[hAr]`. Establish `: (0 : ℝ) ≤ (⌈m⌉₊ : ℝ)` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hUi` using `hU X hD hI hc j rz ry hd A hA1 hA2 t.1 t.2.1 hP hK`.

Establish `hSi` using `hS X hD hI hc j rz ry hd A hA1 hA2 t.1 t.2.1 hP hK`. Establish `hXi` using `hX X hD hI hc j rz ry hd A hA1 hA2 t.1 t.2.1 hP hK`. Establish `hcap : ∀ l, l ≤ segS X.TT j → ((pairC t.1 l : ℤ) : ℝ) ≤ ((cap X.p (X.seg C0 CE1 CE2 j) (pairMap C0 CE1 CE2 X j rz ry t).1 l : ℤ) : ℝ)`. Introduce `l hl`. Use `cap_pair X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) rz ry t.2.1 t.2.2 hP.1 l hl` as an intermediate fact.

Establish `h2 : cap X.p (X.seg C0 CE1 CE2 j) (pairMap C0 CE1 CE2 X j rz ry t).1 l = (X.seg C0 CE1 CE2 j).A0 X.p - A + pairC t.1 l` using `this`. Rewrite using `[h2]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨hd, fun i hi => ?_, fun i hi => ?_, ?_⟩` and prove the remaining obligations.

Take `⟨-, -, t3, -, t5, -, -, -⟩` from `pair_top hP.1 i`. Establish `eO : pairO t.1 (clA C0 CE1 CE2 X j rz ry) i = pairW t.1 i.val + pairSg t.1 (clA C0 CE1 CE2 X j rz ry) i`. Unfold `pairSg`. Expand and normalize the polynomial expressions, which then agree. Establish `n0` using `Int.toNat_of_nonneg (show 0 ≤ pairO t.1 (clA C0 CE1 CE2 X j rz ry) i by rw [eO]; omega)`.

Establish `hσ : ¬ i.val < (X.seg C0 CE1 CE2 j).sigma` using `by omega`. Establish `eo : (pairMap C0 CE1 CE2 X j rz ry t).1.o i = (pairO t.1 (clA C0 CE1 CE2 X j rz ry) i).toNat` using `if_neg hσ`. Establish `ew : (pairMap C0 CE1 CE2 X j rz ry t).1.w i = 0` using `if_neg hσ`. Establish `esg : (pairMap C0 CE1 CE2 X j rz ry t).1.sg i = 0` using `if_neg hσ`. Take `⟨u1, u2⟩` from `hUi i hi`.

Use `⟨?_, ?_, ew, esg⟩` and prove the remaining obligations. Rewrite using `[eo] show _ ≤ clA C0 CE1 CE2 X j rz ry i`. Use linear arithmetic over natural numbers and integers. Rewrite using `[eo]`. Establish `c1 : (((pairO t.1 (clA C0 CE1 CE2 X j rz ry) i).toNat : ℕ) : ℝ) = ((pairO t.1 (clA C0 CE1 CE2 X j rz ry) i : ℤ) : ℝ)` using `by exact_mod_cast n0`.

Rewrite using `[c1]`. Use `hcap i.val i.2.le` as an intermediate fact. Use `show _ ≤ _ + X.La C0 * (clA C0 CE1 CE2 X j rz ry i : ℝ) / X.k`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨-, -, t3, t4, t5, t6, -, -⟩` from `pair_top hP.1 i`.

Establish `n3` using `Int.toNat_of_nonneg t3`. Establish `n5` using `Int.toNat_of_nonneg t5`. Establish `eO : pairO t.1 (clA C0 CE1 CE2 X j rz ry) i = pairW t.1 i.val + pairSg t.1 (clA C0 CE1 CE2 X j rz ry) i`. Unfold `pairSg`. Expand and normalize the polynomial expressions, which then agree.

Establish `eo : (pairMap C0 CE1 CE2 X j rz ry t).1.o i = 0` using `if_pos hi`. Establish `ew : (pairMap C0 CE1 CE2 X j rz ry t).1.w i = (pairW t.1 i.val).toNat` using `if_pos hi`. Establish `esg : (pairMap C0 CE1 CE2 X j rz ry t).1.sg i = (pairSg t.1 (clA C0 CE1 CE2 X j rz ry) i).toNat` using `if_pos hi`. Take `⟨s1, s2⟩` from `hSi i hi`. Establish `c5 : (((pairSg t.1 (clA C0 CE1 CE2 X j rz ry) i).toNat : ℕ) : ℝ) = ((pairSg t.1 (clA C0 CE1 CE2 X j rz ry) i : ℤ) : ℝ)` using `by exact_mod_cast n5`.

Establish `c3 : (((pairW t.1 i.val).toNat : ℕ) : ℝ) = ((pairW t.1 i.val : ℤ) : ℝ)` using `by exact_mod_cast n3`. Use `⟨eo, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[ew] show _ ≤ clA C0 CE1 CE2 X j rz ry i`. Use linear arithmetic over natural numbers and integers. Rewrite using `[esg] show _ ≤ clC C0 CE1 CE2 X j rz ry i`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[ew, esg]`. Use `push_cast`. Rewrite using `[c3, c5]`. Establish `e3 : ((pairO t.1 (clA C0 CE1 CE2 X j rz ry) i : ℤ) : ℝ) = ((pairW t.1 i.val : ℤ) : ℝ) + ((pairSg t.1 (clA C0 CE1 CE2 X j rz ry) i : ℤ) : ℝ)` using `by exact_mod_cast eO`.

Establish `h4` using `hcap i.val i.2.le`. Establish `h5 : X.La C0 * ((pairC t.1 i.val : ℤ) : ℝ) / X.k ≤ X.La C0 * ((cap X.p (X.seg C0 CE1 CE2 j) (pairMap C0 CE1 CE2 X j rz ry t).1 i.val : ℤ) : ℝ) / X.k` using `div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h4 hLa0) hk.le`. Use `show _ ≤ (clA C0 CE1 CE2 X j rz ry i : ℝ) * (1 + 4 / (X.p : ℝ) ^ 2) + X.La C0 * ((cap X.p (X.seg C0 CE1 CE2 j) (pairMap C0 CE1 CE2 X j rz ry t).1 i.val : ℤ) : ℝ) / X.k`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[esg, c5]`.

Conclude with `s2`. Establish `hd0` using `(inter_strip hP.2).2.1`. Establish `eD : pairD t.1 t.2.1 = ∑ x, t.2.1 x - ∑ x : Fin X.m, t.1 (Fin.last _) x.succ`. Unfold `pairD pairTail`. Rewrite using `[finPos_eq (2 * segS X.TT j + 1) (2 * segS X.TT j + 1) (by omega)]`.

Both sides reduce to the same expression. Establish `nD` using `Int.toNat_of_nonneg (show 0 ≤ pairD t.1 t.2.1 by rw [eD]; exact hd0)`. Establish `cD : (((pairD t.1 t.2.1).toNat : ℕ) : ℝ) = ((pairD t.1 t.2.1 : ℤ) : ℝ)` using `by exact_mod_cast nD`. Establish `hB : (0 : ℝ) ≤ ((X.seg C0 CE1 CE2 j).bPlus : ℝ)` using `Nat.cast_nonneg _`. Establish `hj : (t.2.2 : ℝ) ≤ X.La C0 * ((X.seg C0 CE1 CE2 j).bPlus : ℝ) / X.k` using `le_trans (by exact_mod_cast hjp) (Nat.floor_le (by positivity))`.

Establish `hC : ∀ i : Fin (segS X.TT j), (clC C0 CE1 CE2 X j rz ry i : ℝ) ≤ 2 * (X.a : ℝ) / ((X.seg C0 CE1 CE2 j).P X.p i : ℝ)`. Introduce `i`. Take `⟨hP0, -, -, -, -⟩` from `hs.levels j i`. Establish `hcb` using `(coarse_bounds (X.aT (segPos X.TT j i)) (X.p ^ (segG X.TT j - (segDists X.TT j).get i)) (ry i) (fun c => (hd.1 i c).2) (hd.2.2 i).1 (hd.2.2 i).2).1`. Establish `hw` using `(hs.winA _ (pos_mem X.TT j i).1).2`.

Establish `hkY : 2 / (X.k * X.Y) ≤ 1`. Rewrite using `[div_le_one (by have := hs.Y1; positivity)]`. Use `hs.k5` as an intermediate fact. Use `hs.Y1` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Establish `ha` using `hs.apos`. Use `show (clC C0 CE1 CE2 X j rz ry i : ℝ) ≤ 2 * (X.a : ℝ) / ((X.p ^ (segG X.TT j - (segDists X.TT j).get i) : ℕ) : ℝ)`. Rewrite using `[le_div_iff₀ hP0]`. Use `le_trans hcb (le_trans hw ?_)` and prove the remaining obligations. Use the polynomial consequences of the given equalities and inequalities.

Establish `hsum : ∑ i, (clC C0 CE1 CE2 X j rz ry i : ℝ) ≤ ∑ i, 2 * (X.a : ℝ) / ((X.seg C0 CE1 CE2 j).P X.p i : ℝ)` using `Finset.sum_le_sum fun i _ => hC i`. Establish `hsum0 : (0 : ℝ) ≤ ∑ i, 2 * (X.a : ℝ) / ((X.seg C0 CE1 CE2 j).P X.p i : ℝ)` using `Finset.sum_nonneg fun i _ => by positivity`. Establish `hq : X.La C0 / X.k * ∑ i, (clC C0 CE1 CE2 X j rz ry i : ℝ) ≤ (X.La C0 / X.k + 4 / (X.p : ℝ) ^ 2) * ∑ i, 2 * (X.a : ℝ) / ((X.seg C0 CE1 CE2 j).P X.p i : ℝ)`. Establish `a1 : X.La C0 / X.k * ∑ i, (clC C0 CE1 CE2 X j rz ry i : ℝ) ≤ X.La C0 / X.k * ∑ i, 2 * (X.a : ℝ) / ((X.seg C0 CE1 CE2 j).P X.p i : ℝ)` using `mul_le_mul_of_nonneg_left hsum (by positivity)`. Establish `a2 : (0 : ℝ) ≤ 4 / (X.p : ℝ) ^ 2 * ∑ i, 2 * (X.a : ℝ) / ((X.seg C0 CE1 CE2 j).P X.p i : ℝ)` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities. Establish `h4` using `hcap (segS X.TT j) le_rfl`. Use `show (((pairD t.1 t.2.1).toNat + t.2.2 : ℕ) : ℝ) ≤ ((cap X.p (X.seg C0 CE1 CE2 j) (pairMap C0 CE1 CE2 X j rz ry t).1 (segS X.TT j) : ℤ) : ℝ) + (X.La C0 / X.k + 4 / (X.p : ℝ) ^ 2) * ∑ i, 2 * (X.a : ℝ) / ((X.seg C0 CE1 CE2 j).P X.p i : ℝ) + X.La C0 * ((X.seg C0 CE1 CE2 j).bPlus : ℝ …`. Use `push_cast`. Rewrite using `[cD]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem kept_pair_of_three_lines {C0 CYb Cde Ck CD Cb CE1 CE2 Cc H : ℝ}
    (hstd : ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 H X)
    (hU : PairUAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) (hS : PairSAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc)
    (hX : PairXAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) : KeptPairAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ hD hI hc j m hm hmA rz ry hd t ht
  have hs := hstd X hD hI hc
  obtain ⟨⟨hP, hK⟩, hjp⟩ := ht
  have hk : 0 < X.k := by unfold Loc.k; positivity
  have hkk : X.k = (X.m : ℝ) + 1 := rfl
  have hLa0 : 0 ≤ X.La C0 := le_trans zero_le_one hs.La1
  have hA0 : (0 : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) := by
    refine le_trans ?_ (hs.half_ratio_le_segment_base_of_std j)
    have := hs.apos
    have := hs.Q1
    positivity
  have he : (X.N1 : ℝ) * X.La C0 / X.k ≤ 1 := by
    have a1 := hs.LaK
    have a2 := hs.de6
    have e : 40 * (X.N1 : ℝ) * X.La C0 / X.k = 40 * ((X.N1 : ℝ) * X.La C0 / X.k) := by ring
    rw [e] at a1
    linarith
  have e2 : ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * X.N1 * X.La C0 / X.k =
      ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * ((X.N1 : ℝ) * X.La C0 / X.k) := by ring
  have hle : (⌈m⌉₊ : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) := by
    refine le_trans hmA ?_
    rw [e2]
    nlinarith
  have hleZ : ((⌈m⌉₊ : ℕ) : ℤ) ≤ (X.seg C0 CE1 CE2 j).A0 X.p := by exact_mod_cast hle
  set A : ℕ := ((X.seg C0 CE1 CE2 j).A0 X.p - (⌈m⌉₊ : ℤ)).toNat with hA
  have hAz : (A : ℤ) = (X.seg C0 CE1 CE2 j).A0 X.p - (⌈m⌉₊ : ℤ) := Int.toNat_of_nonneg (by omega)
  have hAr : (A : ℝ) = ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) - (⌈m⌉₊ : ℝ) := by exact_mod_cast hAz
  have hA1 : ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * (1 - X.N1 * X.La C0 / X.k) ≤ (A : ℝ) := by
    rw [hAr]
    rw [e2] at hmA
    linarith
  have hA2 : (A : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) := by
    rw [hAr]
    have : (0 : ℝ) ≤ (⌈m⌉₊ : ℝ) := Nat.cast_nonneg _
    linarith
  have hUi := hU X hD hI hc j rz ry hd A hA1 hA2 t.1 t.2.1 hP hK
  have hSi := hS X hD hI hc j rz ry hd A hA1 hA2 t.1 t.2.1 hP hK
  have hXi := hX X hD hI hc j rz ry hd A hA1 hA2 t.1 t.2.1 hP hK
  have hcap : ∀ l, l ≤ segS X.TT j → ((pairC t.1 l : ℤ) : ℝ) ≤
      ((cap X.p (X.seg C0 CE1 CE2 j) (pairMap C0 CE1 CE2 X j rz ry t).1 l : ℤ) : ℝ) := by
    intro l hl
    have := cap_pair X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) rz ry t.2.1 t.2.2 hP.1 l hl
    have h2 : cap X.p (X.seg C0 CE1 CE2 j) (pairMap C0 CE1 CE2 X j rz ry t).1 l =
        (X.seg C0 CE1 CE2 j).A0 X.p - A + pairC t.1 l := this
    rw [h2]
    push_cast
    linarith
  refine ⟨hd, fun i hi => ?_, fun i hi => ?_, ?_⟩
  ·
    obtain ⟨-, -, t3, -, t5, -, -, -⟩ := pair_top hP.1 i
    have eO : pairO t.1 (clA C0 CE1 CE2 X j rz ry) i = pairW t.1 i.val + pairSg t.1 (clA C0 CE1 CE2 X j rz ry) i := by
      unfold pairSg; ring
    have n0 := Int.toNat_of_nonneg (show 0 ≤ pairO t.1 (clA C0 CE1 CE2 X j rz ry) i by rw [eO]; omega)
    have hσ : ¬ i.val < (X.seg C0 CE1 CE2 j).sigma := by omega
    have eo : (pairMap C0 CE1 CE2 X j rz ry t).1.o i = (pairO t.1 (clA C0 CE1 CE2 X j rz ry) i).toNat := if_neg hσ
    have ew : (pairMap C0 CE1 CE2 X j rz ry t).1.w i = 0 := if_neg hσ
    have esg : (pairMap C0 CE1 CE2 X j rz ry t).1.sg i = 0 := if_neg hσ
    obtain ⟨u1, u2⟩ := hUi i hi
    refine ⟨?_, ?_, ew, esg⟩
    · rw [eo]
      show _ ≤ clA C0 CE1 CE2 X j rz ry i
      omega
    · rw [eo]
      have c1 : (((pairO t.1 (clA C0 CE1 CE2 X j rz ry) i).toNat : ℕ) : ℝ) =
          ((pairO t.1 (clA C0 CE1 CE2 X j rz ry) i : ℤ) : ℝ) := by exact_mod_cast n0
      rw [c1]
      have := hcap i.val i.2.le
      show _ ≤ _ + X.La C0 * (clA C0 CE1 CE2 X j rz ry i : ℝ) / X.k
      linarith
  ·
    obtain ⟨-, -, t3, t4, t5, t6, -, -⟩ := pair_top hP.1 i
    have n3 := Int.toNat_of_nonneg t3
    have n5 := Int.toNat_of_nonneg t5
    have eO : pairO t.1 (clA C0 CE1 CE2 X j rz ry) i = pairW t.1 i.val + pairSg t.1 (clA C0 CE1 CE2 X j rz ry) i := by
      unfold pairSg; ring
    have eo : (pairMap C0 CE1 CE2 X j rz ry t).1.o i = 0 := if_pos hi
    have ew : (pairMap C0 CE1 CE2 X j rz ry t).1.w i = (pairW t.1 i.val).toNat := if_pos hi
    have esg : (pairMap C0 CE1 CE2 X j rz ry t).1.sg i = (pairSg t.1 (clA C0 CE1 CE2 X j rz ry) i).toNat := if_pos hi
    obtain ⟨s1, s2⟩ := hSi i hi
    have c5 : (((pairSg t.1 (clA C0 CE1 CE2 X j rz ry) i).toNat : ℕ) : ℝ) =
        ((pairSg t.1 (clA C0 CE1 CE2 X j rz ry) i : ℤ) : ℝ) := by exact_mod_cast n5
    have c3 : (((pairW t.1 i.val).toNat : ℕ) : ℝ) = ((pairW t.1 i.val : ℤ) : ℝ) := by exact_mod_cast n3
    refine ⟨eo, ?_, ?_, ?_, ?_⟩
    · rw [ew]
      show _ ≤ clA C0 CE1 CE2 X j rz ry i
      omega
    · rw [esg]
      show _ ≤ clC C0 CE1 CE2 X j rz ry i
      omega
    · rw [ew, esg]
      push_cast
      rw [c3, c5]
      have e3 : ((pairO t.1 (clA C0 CE1 CE2 X j rz ry) i : ℤ) : ℝ) =
          ((pairW t.1 i.val : ℤ) : ℝ) + ((pairSg t.1 (clA C0 CE1 CE2 X j rz ry) i : ℤ) : ℝ) := by exact_mod_cast eO
      have h4 := hcap i.val i.2.le
      have h5 : X.La C0 * ((pairC t.1 i.val : ℤ) : ℝ) / X.k ≤
          X.La C0 * ((cap X.p (X.seg C0 CE1 CE2 j) (pairMap C0 CE1 CE2 X j rz ry t).1 i.val : ℤ) : ℝ) / X.k :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h4 hLa0) hk.le
      show _ ≤ (clA C0 CE1 CE2 X j rz ry i : ℝ) * (1 + 4 / (X.p : ℝ) ^ 2) +
        X.La C0 * ((cap X.p (X.seg C0 CE1 CE2 j) (pairMap C0 CE1 CE2 X j rz ry t).1 i.val : ℤ) : ℝ) / X.k
      linarith
    · rw [esg, c5]
      exact s2
  ·
    have hd0 := (inter_strip hP.2).2.1
    have eD : pairD t.1 t.2.1 = ∑ x, t.2.1 x - ∑ x : Fin X.m, t.1 (Fin.last _) x.succ := by
      unfold pairD pairTail
      rw [finPos_eq (2 * segS X.TT j + 1) (2 * segS X.TT j + 1) (by omega)]
      rfl
    have nD := Int.toNat_of_nonneg (show 0 ≤ pairD t.1 t.2.1 by rw [eD]; exact hd0)
    have cD : (((pairD t.1 t.2.1).toNat : ℕ) : ℝ) = ((pairD t.1 t.2.1 : ℤ) : ℝ) := by exact_mod_cast nD
    have hB : (0 : ℝ) ≤ ((X.seg C0 CE1 CE2 j).bPlus : ℝ) := Nat.cast_nonneg _
    have hj : (t.2.2 : ℝ) ≤ X.La C0 * ((X.seg C0 CE1 CE2 j).bPlus : ℝ) / X.k :=
      le_trans (by exact_mod_cast hjp) (Nat.floor_le (by positivity))
    have hC : ∀ i : Fin (segS X.TT j), (clC C0 CE1 CE2 X j rz ry i : ℝ) ≤
        2 * (X.a : ℝ) / ((X.seg C0 CE1 CE2 j).P X.p i : ℝ) := by
      intro i
      obtain ⟨hP0, -, -, -, -⟩ := hs.levels j i
      have hcb := (coarse_bounds (X.aT (segPos X.TT j i)) (X.p ^ (segG X.TT j - (segDists X.TT j).get i)) (ry i)
        (fun c => (hd.1 i c).2) (hd.2.2 i).1 (hd.2.2 i).2).1
      have hw := (hs.winA _ (pos_mem X.TT j i).1).2
      have hkY : 2 / (X.k * X.Y) ≤ 1 := by
        rw [div_le_one (by have := hs.Y1; positivity)]
        have := hs.k5
        have := hs.Y1
        nlinarith
      have ha := hs.apos
      show (clC C0 CE1 CE2 X j rz ry i : ℝ) ≤ 2 * (X.a : ℝ) / ((X.p ^ (segG X.TT j - (segDists X.TT j).get i) : ℕ) : ℝ)
      rw [le_div_iff₀ hP0]
      refine le_trans hcb (le_trans hw ?_)
      nlinarith
    have hsum : ∑ i, (clC C0 CE1 CE2 X j rz ry i : ℝ) ≤
        ∑ i, 2 * (X.a : ℝ) / ((X.seg C0 CE1 CE2 j).P X.p i : ℝ) := Finset.sum_le_sum fun i _ => hC i
    have hsum0 : (0 : ℝ) ≤ ∑ i, 2 * (X.a : ℝ) / ((X.seg C0 CE1 CE2 j).P X.p i : ℝ) :=
      Finset.sum_nonneg fun i _ => by positivity
    have hq : X.La C0 / X.k * ∑ i, (clC C0 CE1 CE2 X j rz ry i : ℝ) ≤
        (X.La C0 / X.k + 4 / (X.p : ℝ) ^ 2) * ∑ i, 2 * (X.a : ℝ) / ((X.seg C0 CE1 CE2 j).P X.p i : ℝ) := by
      have a1 : X.La C0 / X.k * ∑ i, (clC C0 CE1 CE2 X j rz ry i : ℝ) ≤
          X.La C0 / X.k * ∑ i, 2 * (X.a : ℝ) / ((X.seg C0 CE1 CE2 j).P X.p i : ℝ) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      have a2 : (0 : ℝ) ≤ 4 / (X.p : ℝ) ^ 2 * ∑ i, 2 * (X.a : ℝ) / ((X.seg C0 CE1 CE2 j).P X.p i : ℝ) := by positivity
      nlinarith
    have h4 := hcap (segS X.TT j) le_rfl
    show (((pairD t.1 t.2.1).toNat + t.2.2 : ℕ) : ℝ) ≤
      ((cap X.p (X.seg C0 CE1 CE2 j) (pairMap C0 CE1 CE2 X j rz ry t).1 (segS X.TT j) : ℤ) : ℝ) +
        (X.La C0 / X.k + 4 / (X.p : ℝ) ^ 2) * ∑ i, 2 * (X.a : ℝ) / ((X.seg C0 CE1 CE2 j).P X.p i : ℝ) +
        X.La C0 * ((X.seg C0 CE1 CE2 j).bPlus : ℝ) / X.k
    push_cast
    rw [cD]
    linarith

/- English proof (translation)
Establish `hstd : TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X` using `TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1) fun _ _ _ _ _ _ _ _ _ _ hCc hC0 _ h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 => fun _ hD hI hc => std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc`. Conclude with `TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h => kept_pair_of_three_lines h.1.1.1 h.1.1.2 h.1.2 h.2) (((hstd.and hU).and hS).and hX)`.
-/
theorem kept_pairs_of_three_lines (hU : RestPairU) (hS : RestPairS) (hX : RestPairX) : KeptPairsBeyond := by
  have hstd : TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc =>
      ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X :=
    TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1)
      fun _ _ _ _ _ _ _ _ _ _ hCc hC0 _ h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 =>
        fun _ hD hI hc => std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc
  exact TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h => kept_pair_of_three_lines h.1.1.1 h.1.1.2 h.1.2 h.2) (((hstd.and hU).and hS).and hX)

/- English proof (translation)
The claim follows from `kept_blocks_of_kept_pairs (kept_pairs_of_three_lines hU hS hX)`.
-/
theorem kept_blocks_of_three_lines (hU : RestPairU) (hS : RestPairS) (hX : RestPairX) : KeptBlocksBeyondThreshold := kept_blocks_of_kept_pairs (kept_pairs_of_three_lines hU hS hX)

/- English proof (translation)
Establish `hm` using `dist_strictMono X.TT j (show l < l' from Fin.lt_def.mpr (by omega))`. Establish `ho1` using `dist_odd hs.nEven X.TT j l`. Establish `ho2` using `dist_odd hs.nEven X.TT j l'`. Establish `hlt` using `(dist_pos_lt X.TT j l').2`. Take `⟨k1, hk1⟩` from `ho1`.

Take `⟨k2, hk2⟩` from `ho2`. Establish `hdd : (segDists X.TT j).get l + 2 ≤ (segDists X.TT j).get l'` using `by omega`. Use `set P := X.p ^ (segG X.TT j - (segDists X.TT j).get l) with hP`. Use `set P' := X.p ^ (segG X.TT j - (segDists X.TT j).get l') with hP'`. Establish `hp1 : 1 ≤ X.p` using `by have := hs.p5; omega`.

Establish `hPP : X.p ^ 2 * P' ≤ P`. Rewrite using `[hP, hP', ← pow_add]`. Conclude with `Nat.pow_le_pow_right hp1 (by omega)`. Establish `hPPr : (X.p : ℝ) ^ 2 * (P' : ℝ) ≤ (P : ℝ)` using `by exact_mod_cast hPP`. Take `⟨hP0, -, -, hQ, hPQ⟩` from `hs.levels j l`.

Take `⟨hP0', -, -, -, hPQ'⟩` from `hs.levels j l'`. Establish `cb` using `coarse_bounds (X.bT (segPos X.TT j l)) P (rz l) (fun c => (hd.1 l c).1) (hd.2.1 l).1 (hd.2.1 l).2`. Establish `cb'` using `coarse_bounds (X.bT (segPos X.TT j l')) P' (rz l') (fun c => (hd.1 l' c).1) (hd.2.1 l').1 (hd.2.1 l').2`. Establish `wb` using `hs.winB _ (pos_mem X.TT j l).1`. Establish `wb'` using `hs.winB _ (pos_mem X.TT j l').1`.

Establish `hbe` using `hs.beLe`. Establish `hbe0` using `hs.be0`. Establish `hde` using `hs.de6`. Establish `hLK` using `hs.LaK`. Establish `hk5` using `hs.k5`.

Establish `hkQ` using `hs.kQ hH`. Establish `hb` using `hs.bpos`. Establish `hQ1` using `hs.Q1`. Establish `eA : (clA C0 CE1 CE2 X j rz ry l : ℝ) = (((X.bT (segPos X.TT j l) - ∑ c, rz l c) / P : ℕ) : ℝ)` using `rfl`. Establish `eA' : (clA C0 CE1 CE2 X j rz ry l' : ℝ) = (((X.bT (segPos X.TT j l') - ∑ c, rz l' c) / P' : ℕ) : ℝ)` using `rfl`.

Rewrite using `[eA, eA']`. Establish `hA0 : (0 : ℝ) ≤ (((X.bT (segPos X.TT j l) - ∑ c, rz l c) / P : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Generalize the expression as in `(((X.bT (segPos X.TT j l) - ∑ c, rz l c) / P : ℕ) : ℝ) = A at cb hA0 ⊢`. Generalize the expression as in `(((X.bT (segPos X.TT j l') - ∑ c, rz l' c) / P' : ℕ) : ℝ) = A' at cb' ⊢`. Establish `hbe1 : be X C0 ≤ 1 / 12`.

Establish `: 0 ≤ 18 * (X.N1 : ℝ) * X.La C0 / X.k`. Use `hs.La1; have : (0 : ℝ) < X.k := by linarith` as an intermediate fact. Check the signs of the components of the expression. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hkP : X.k * (P' : ℝ) ≤ X.b' / 12`.

Establish `h1 : X.k * (P' : ℝ) ≤ X.k * X.Q` using `mul_le_mul_of_nonneg_left (le_trans hPQ' hQ) (by linarith)`. Establish `h2 : X.k ^ 3 * X.Q ≤ X.b'` using `hkQ`. Establish `h3 : 12 * (X.k * X.Q) ≤ X.k ^ 3 * X.Q`. Establish `h12 : (12 : ℝ) ≤ X.k ^ 2` using `by nlinarith`. Use polynomial arithmetic with `[mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ X.k) (by linarith : (0:ℝ) ≤ X.Q)) (by linarith : (0:ℝ) ≤ X.k ^ 2 - 12)]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hkk : ((X.m : ℝ) + 1) = X.k` using `rfl`. Rewrite `cb'` using `[hkk]`. Establish `e1 : (X.p : ℝ) ^ 2 * A * P' ≤ X.b' * (1 + be X C0)`. Combine the equalities or inequalities in the displayed calculation.

Establish `e2 : X.b' * (1 - be X C0) - X.k * P' < A' * P'` using `by linarith [cb'.2, wb'.1]`. Establish `hP'pos : (0 : ℝ) < P'` using `hP0'`. Establish `hbb` using `mul_le_mul_of_nonneg_left hbe1 hb.le`. Establish `key : (X.p : ℝ) ^ 2 * A * P' ≤ 2 * A' * P'` using `by linarith`. Use `le_of_mul_le_mul_right (show (X.p : ℝ) ^ 2 * A * P' ≤ 2 * A' * P' from key) hP'pos` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem coarse_degree_ratio_consecutive {C0 Cde CE1 CE2 H : ℝ} {X : Loc} (hs : Std C0 Cde CE1 CE2 H X) (hH : 1 ≤ H) (j : Fin (numSeg X.TT))
    (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ)
    (hd : DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry))
    (l l' : Fin (segS X.TT j)) (hll : l.val + 1 = l'.val) :
    (X.p : ℝ) ^ 2 * (clA C0 CE1 CE2 X j rz ry l : ℝ) ≤ 2 * (clA C0 CE1 CE2 X j rz ry l' : ℝ) := by
  have hm := dist_strictMono X.TT j (show l < l' from Fin.lt_def.mpr (by omega))
  have ho1 := dist_odd hs.nEven X.TT j l
  have ho2 := dist_odd hs.nEven X.TT j l'
  have hlt := (dist_pos_lt X.TT j l').2
  obtain ⟨k1, hk1⟩ := ho1
  obtain ⟨k2, hk2⟩ := ho2
  have hdd : (segDists X.TT j).get l + 2 ≤ (segDists X.TT j).get l' := by omega
  set P := X.p ^ (segG X.TT j - (segDists X.TT j).get l) with hP
  set P' := X.p ^ (segG X.TT j - (segDists X.TT j).get l') with hP'
  have hp1 : 1 ≤ X.p := by have := hs.p5; omega
  have hPP : X.p ^ 2 * P' ≤ P := by
    rw [hP, hP', ← pow_add]
    exact Nat.pow_le_pow_right hp1 (by omega)
  have hPPr : (X.p : ℝ) ^ 2 * (P' : ℝ) ≤ (P : ℝ) := by exact_mod_cast hPP
  obtain ⟨hP0, -, -, hQ, hPQ⟩ := hs.levels j l
  obtain ⟨hP0', -, -, -, hPQ'⟩ := hs.levels j l'
  have cb := coarse_bounds (X.bT (segPos X.TT j l)) P (rz l) (fun c => (hd.1 l c).1) (hd.2.1 l).1 (hd.2.1 l).2
  have cb' := coarse_bounds (X.bT (segPos X.TT j l')) P' (rz l') (fun c => (hd.1 l' c).1) (hd.2.1 l').1 (hd.2.1 l').2
  have wb := hs.winB _ (pos_mem X.TT j l).1
  have wb' := hs.winB _ (pos_mem X.TT j l').1
  have hbe := hs.beLe
  have hbe0 := hs.be0
  have hde := hs.de6
  have hLK := hs.LaK
  have hk5 := hs.k5
  have hkQ := hs.kQ hH
  have hb := hs.bpos
  have hQ1 := hs.Q1
  have eA : (clA C0 CE1 CE2 X j rz ry l : ℝ) = (((X.bT (segPos X.TT j l) - ∑ c, rz l c) / P : ℕ) : ℝ) := rfl
  have eA' : (clA C0 CE1 CE2 X j rz ry l' : ℝ) = (((X.bT (segPos X.TT j l') - ∑ c, rz l' c) / P' : ℕ) : ℝ) := rfl
  rw [eA, eA']
  have hA0 : (0 : ℝ) ≤ (((X.bT (segPos X.TT j l) - ∑ c, rz l c) / P : ℕ) : ℝ) := Nat.cast_nonneg _
  generalize (((X.bT (segPos X.TT j l) - ∑ c, rz l c) / P : ℕ) : ℝ) = A at cb hA0 ⊢
  generalize (((X.bT (segPos X.TT j l') - ∑ c, rz l' c) / P' : ℕ) : ℝ) = A' at cb' ⊢
  have hbe1 : be X C0 ≤ 1 / 12 := by
    have : 0 ≤ 18 * (X.N1 : ℝ) * X.La C0 / X.k := by
      have := hs.La1; have : (0 : ℝ) < X.k := by linarith
      positivity
    linarith

  have hkP : X.k * (P' : ℝ) ≤ X.b' / 12 := by
    have h1 : X.k * (P' : ℝ) ≤ X.k * X.Q := mul_le_mul_of_nonneg_left (le_trans hPQ' hQ) (by linarith)
    have h2 : X.k ^ 3 * X.Q ≤ X.b' := hkQ
    have h3 : 12 * (X.k * X.Q) ≤ X.k ^ 3 * X.Q := by
      have h12 : (12 : ℝ) ≤ X.k ^ 2 := by nlinarith
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ X.k) (by linarith : (0:ℝ) ≤ X.Q)) (by linarith : (0:ℝ) ≤ X.k ^ 2 - 12)]
    linarith
  have hkk : ((X.m : ℝ) + 1) = X.k := rfl
  rw [hkk] at cb'

  have e1 : (X.p : ℝ) ^ 2 * A * P' ≤ X.b' * (1 + be X C0) := by
    calc (X.p : ℝ) ^ 2 * A * P' = A * ((X.p : ℝ) ^ 2 * P') := by ring
      _ ≤ A * P := mul_le_mul_of_nonneg_left hPPr hA0
      _ ≤ _ := le_trans cb.1 wb.2
  have e2 : X.b' * (1 - be X C0) - X.k * P' < A' * P' := by linarith [cb'.2, wb'.1]
  have hP'pos : (0 : ℝ) < P' := hP0'
  have hbb := mul_le_mul_of_nonneg_left hbe1 hb.le
  have key : (X.p : ℝ) ^ 2 * A * P' ≤ 2 * A' * P' := by linarith
  have := le_of_mul_le_mul_right (show (X.p : ℝ) ^ 2 * A * P' ≤ 2 * A' * P' from key) hP'pos
  linarith

/- English proof (translation)
Establish `hp : (25 : ℝ) ≤ (X.p : ℝ) ^ 2`. Establish `: (5 : ℝ) ≤ X.p` using `by exact_mod_cast hs.p5`. Use the polynomial consequences of the given equalities and inequalities. Introduce `⟨i, hi⟩`. Proceed by induction on `i with`.

Consider the case `zero`. Simplify using `only [Nat.not_lt_zero, if_false, Finset.sum_const_zero]`. Check the signs of the components of the expression. Consider the case `succ i ih`. Establish `ih'` using `ih (by omega)`.

Establish `hstep` using `coarse_degree_ratio_consecutive hs hH j rz ry hd ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl`. Establish `e : (∑ l : Fin (segS X.TT j), if l.val < i + 1 then (clA C0 CE1 CE2 X j rz ry l : ℝ) else 0) = (∑ l : Fin (segS X.TT j), if l.val < i then (clA C0 CE1 CE2 X j rz ry l : ℝ) else 0) + (clA C0 CE1 CE2 X j rz ry ⟨i, by omega⟩ : ℝ)`. Establish `h2 : (∑ l : Fin (segS X.TT j), if l = (⟨i, by omega⟩ : Fin (segS X.TT j)) then (clA C0 CE1 CE2 X j rz ry l : ℝ) else 0) = (clA C0 CE1 CE2 X j rz ry ⟨i, by omega⟩ : ℝ)` using `by simp`. Rewrite using `[← h2, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Distinguish the cases in `h1 : l.val < i`. Rewrite using `[if_pos (by omega), if_pos h1, if_neg (fun h => by rw [h] at h1; simp at h1)]; ring`. Distinguish the cases in `h3 : l.val = i`. Rewrite using `[if_pos (by omega), if_neg h1, if_pos (Fin.ext h3)]; ring`. Rewrite using `[if_neg (by omega), if_neg h1, if_neg (fun h => h3 (by rw [h]))]; ring`.

Rewrite using `[e]`. Establish `hA : (0 : ℝ) ≤ (clA C0 CE1 CE2 X j rz ry ⟨i, by omega⟩ : ℝ)` using `Nat.cast_nonneg _`. Establish `hp0 : (0 : ℝ) < (X.p : ℝ) ^ 2` using `by linarith`. Rewrite `ih'`, the goal using `[div_eq_mul_inv]`. Establish `hinv : (X.p : ℝ) ^ 2 * ((X.p : ℝ) ^ 2)⁻¹ = 1` using `mul_inv_cancel₀ hp0.ne'`.

Establish `hinv0 : ((X.p : ℝ) ^ 2)⁻¹ ≤ 1 / 25`. Rewrite using `[one_div]; exact inv_anti₀ (by norm_num) hp`. Use polynomial arithmetic with `[inv_pos.mpr hp0]`.
-/
theorem coarse_degree_prefix_sum {C0 Cde CE1 CE2 H : ℝ} {X : Loc} (hs : Std C0 Cde CE1 CE2 H X) (hH : 1 ≤ H) (j : Fin (numSeg X.TT))
    (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ)
    (hd : DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry)) :
    ∀ i : Fin (segS X.TT j), (∑ l : Fin (segS X.TT j), if l.val < i.val then (clA C0 CE1 CE2 X j rz ry l : ℝ) else 0) ≤
      4 * (clA C0 CE1 CE2 X j rz ry i : ℝ) / (X.p : ℝ) ^ 2 := by
  have hp : (25 : ℝ) ≤ (X.p : ℝ) ^ 2 := by
    have : (5 : ℝ) ≤ X.p := by exact_mod_cast hs.p5
    nlinarith
  intro ⟨i, hi⟩
  induction i with
  | zero =>
    simp only [Nat.not_lt_zero, if_false, Finset.sum_const_zero]
    positivity
  | succ i ih =>
    have ih' := ih (by omega)
    have hstep := coarse_degree_ratio_consecutive hs hH j rz ry hd ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl
    have e : (∑ l : Fin (segS X.TT j), if l.val < i + 1 then (clA C0 CE1 CE2 X j rz ry l : ℝ) else 0) =
        (∑ l : Fin (segS X.TT j), if l.val < i then (clA C0 CE1 CE2 X j rz ry l : ℝ) else 0) +
          (clA C0 CE1 CE2 X j rz ry ⟨i, by omega⟩ : ℝ) := by
      have h2 : (∑ l : Fin (segS X.TT j), if l = (⟨i, by omega⟩ : Fin (segS X.TT j)) then
          (clA C0 CE1 CE2 X j rz ry l : ℝ) else 0) = (clA C0 CE1 CE2 X j rz ry ⟨i, by omega⟩ : ℝ) := by simp
      rw [← h2, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases h1 : l.val < i
      · rw [if_pos (by omega), if_pos h1, if_neg (fun h => by rw [h] at h1; simp at h1)]; ring
      · by_cases h3 : l.val = i
        · rw [if_pos (by omega), if_neg h1, if_pos (Fin.ext h3)]; ring
        · rw [if_neg (by omega), if_neg h1, if_neg (fun h => h3 (by rw [h]))]; ring
    rw [e]
    have hA : (0 : ℝ) ≤ (clA C0 CE1 CE2 X j rz ry ⟨i, by omega⟩ : ℝ) := Nat.cast_nonneg _
    have hp0 : (0 : ℝ) < (X.p : ℝ) ^ 2 := by linarith
    rw [div_eq_mul_inv] at ih' ⊢
    have hinv : (X.p : ℝ) ^ 2 * ((X.p : ℝ) ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hp0.ne'
    have hinv0 : ((X.p : ℝ) ^ 2)⁻¹ ≤ 1 / 25 := by
      rw [one_div]; exact inv_anti₀ (by norm_num) hp
    nlinarith [inv_pos.mpr hp0]

end Formalism.MainNotions.ColumnSystems.Pf
