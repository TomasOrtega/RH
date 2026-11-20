import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.RestPathFrom
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.DividedPowerZeroOfGlActionZero

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

/- English proof (translation)
Unfold `Formalism.InvariantFactorPaths.GelfandTsetlinBases.HStrip Formalism.MainNotions.G.HStrip`. Use `and_congr Iff.rfl (and_congr ?_ ?_)` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce `h a ha`. Conclude with `h a ⟨a.1 + 1, ha⟩ rfl`.

Introduce `h m m' hm`. Establish `hlt : m.1 + 1 < n` using `by rw [hm]; exact m'.2`. Establish `: m' = ⟨m.1 + 1, hlt⟩` using `Fin.ext hm.symm`. Rewrite using `[this]`. Conclude with `h m hlt`.

Rewrite using `[Finset.sum_sub_distrib]`.
-/
theorem hstrip_iff {n : ℕ} (nu mu : Fin n → ℤ) (b : ℕ) :
    Formalism.InvariantFactorPaths.GelfandTsetlinBases.HStrip mu nu b ↔ Formalism.MainNotions.G.HStrip nu mu b := by
  unfold Formalism.InvariantFactorPaths.GelfandTsetlinBases.HStrip Formalism.MainNotions.G.HStrip
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · constructor
    · intro h a ha
      exact h a ⟨a.1 + 1, ha⟩ rfl
    · intro h m m' hm
      have hlt : m.1 + 1 < n := by rw [hm]; exact m'.2
      have : m' = ⟨m.1 + 1, hlt⟩ := Fin.ext hm.symm
      rw [this]; exact h m hlt
  · rw [Finset.sum_sub_distrib]

/- English proof (translation)
Unfold `ext`. Rewrite using `[dif_pos h]`.
-/
theorem ext_of_lt {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) {i : ℕ} (h : i < N + 1) : ext mu i = mu ⟨i, h⟩ := by
  unfold ext; rw [dif_pos h]

/- English proof (translation)
Unfold `ext; rw [dif_neg (by omega)]`.
-/
theorem ext_of_ge {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) {i : ℕ} (h : N < i) : ext mu i = 0 := by
  unfold ext; rw [dif_neg (by omega)]

/- English proof (translation)
Unfold `isV`. Rewrite using `[dif_pos h]`.
-/
theorem isV_of_lt {N : ℕ} (LL : Letters (Fin N)) {i : ℕ} (h : i < N) : isV LL i = LL.vec ⟨i, h⟩ := by
  unfold isV; rw [dif_pos h]

/- English proof (translation)
Unfold `Bn`. Rewrite using `[dif_pos h]`.
-/
theorem Bn_of_lt {N : ℕ} (B : Fin N → ℕ) {i : ℕ} (h : i < N) : Bn B i = B ⟨i, h⟩ := by
  unfold Bn; rw [dif_pos h]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Unfold `res`. Rewrite using `[ext_of_lt mu i.2]`.
-/
theorem res_ext {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) : res N (ext mu) = mu := by
  funext i
  unfold res
  rw [ext_of_lt mu i.2]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i < N + 1`. Rewrite using `[ext_of_lt _ hi]`. Both sides reduce to the same expression. Rewrite using `[ext_of_ge _ (by omega), h i (by omega)]`.
-/
theorem ext_res {N n : ℕ} (μ : ℕ → Fin n → ℤ) (h : ∀ i, N < i → μ i = 0) : ext (res N μ) = μ := by
  funext i
  by_cases hi : i < N + 1
  · rw [ext_of_lt _ hi]; rfl
  · rw [ext_of_ge _ (by omega), h i (by omega)]

/- English proof (translation)
Introduce `n N LL B P`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[ext_of_lt _ (Nat.succ_pos N)]`. Conclude with `P.zero`. Introduce `i hi`.

Rewrite using `[ext_of_lt _ (Nat.lt_succ_of_le hi)]`. Conclude with `P.dom _`. Introduce `i hi`. Establish `hs` using `P.step ⟨i, hi⟩`. Rewrite using `[isV_of_lt LL hi, Bn_of_lt B hi, ext_of_lt P.mu (show i < N + 1 by omega), ext_of_lt P.mu (show i + 1 < N + 1 by omega)]`.

Establish `e1 : (⟨i, hi⟩ : Fin N).castSucc = ⟨i, by omega⟩` using `rfl`. Establish `e2 : (⟨i, hi⟩ : Fin N).succ = ⟨i + 1, by omega⟩` using `rfl`. Rewrite `hs` using `[e1, e2]`. Use `split_ifs at hs ⊢ with hv`. Conclude with `(hstrip_iff _ _ _).2 hs`.

Conclude with `(hstrip_iff _ _ _).2 hs`.
-/
theorem restPathTo : RestPathTo := by
  intro n N LL B P
  refine ⟨?_, ?_, ?_⟩
  · rw [ext_of_lt _ (Nat.succ_pos N)]; exact P.zero
  · intro i hi
    rw [ext_of_lt _ (Nat.lt_succ_of_le hi)]; exact P.dom _
  · intro i hi
    have hs := P.step ⟨i, hi⟩
    rw [isV_of_lt LL hi, Bn_of_lt B hi, ext_of_lt P.mu (show i < N + 1 by omega),
      ext_of_lt P.mu (show i + 1 < N + 1 by omega)]
    have e1 : (⟨i, hi⟩ : Fin N).castSucc = ⟨i, by omega⟩ := rfl
    have e2 : (⟨i, hi⟩ : Fin N).succ = ⟨i + 1, by omega⟩ := rfl
    rw [e1, e2] at hs
    split_ifs at hs ⊢ with hv
    · exact (hstrip_iff _ _ _).2 hs
    · exact (hstrip_iff _ _ _).2 hs

/- English proof (translation)
Introduce `n N LL B μ hμ`. Take `⟨h0, hd, hs⟩` from `hμ`. Use `⟨⟨res N μ, ?_, ?_, ?_⟩, rfl⟩` and prove the remaining obligations. Conclude with `h0`. Introduce `i`.

Conclude with `hd i.val (Nat.le_of_lt_succ i.2)`. Introduce `i`. Establish `h` using `hs i.val i.2`. Rewrite `h` using `[isV_of_lt LL i.2, Bn_of_lt B i.2]`. Establish `e1 : res N μ i.castSucc = μ i.val` using `rfl`.

Establish `e2 : res N μ i.succ = μ (i.val + 1)` using `rfl`. Rewrite using `[e1, e2]`. Establish `e3 : (⟨i.val, i.2⟩ : Fin N) = i` using `rfl`. Rewrite `h` using `[e3]`. Use `split_ifs at h ⊢ with hv`.

Conclude with `(hstrip_iff _ _ _).1 h`. Conclude with `(hstrip_iff _ _ _).1 h`.
-/
theorem restPathFrom : RestPathFrom := by
  intro n N LL B μ hμ
  obtain ⟨h0, hd, hs⟩ := hμ
  refine ⟨⟨res N μ, ?_, ?_, ?_⟩, rfl⟩
  · exact h0
  · intro i
    exact hd i.val (Nat.le_of_lt_succ i.2)
  · intro i
    have h := hs i.val i.2
    rw [isV_of_lt LL i.2, Bn_of_lt B i.2] at h
    have e1 : res N μ i.castSucc = μ i.val := rfl
    have e2 : res N μ i.succ = μ (i.val + 1) := rfl
    rw [e1, e2]
    have e3 : (⟨i.val, i.2⟩ : Fin N) = i := rfl
    rw [e3] at h
    split_ifs at h ⊢ with hv
    · exact (hstrip_iff _ _ _).1 h
    · exact (hstrip_iff _ _ _).1 h

/- English proof (translation)
Unfold `tabCol Formalism.InvariantFactorPaths.GelfandTsetlinBases.hatIdx`. Use `split_ifs`. Both sides reduce to the same expression. Conclude with `(Finset.compl_eq_univ_sdiff _).symm`.
-/
theorem tabCol_eq {n : ℕ} (I : ℤ → Finset (Fin n)) (c : ℤ) : tabCol I c = Formalism.InvariantFactorPaths.GelfandTsetlinBases.hatIdx I c := by
  unfold tabCol Formalism.InvariantFactorPaths.GelfandTsetlinBases.hatIdx
  split_ifs
  · rfl
  · exact (Finset.compl_eq_univ_sdiff _).symm

/- English proof (translation)
Unfold `Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.cnt`. Use `congr 1`. Use extensionality with `a`. Simplify using `only [mem_filter, Fin.le_def, Nat.lt_succ_iff]`.
-/
theorem cnt_succ {n : ℕ} (A : Finset (Fin n)) (t : Fin n) :
    Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.cnt A (t.val + 1) = (A.filter (· ≤ t)).card := by
  unfold Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.cnt
  congr 1
  ext a
  simp only [mem_filter, Fin.le_def, Nat.lt_succ_iff]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h t`. Rewrite using `[← cnt_succ, ← cnt_succ]`. Conclude with `h _`. Introduce `h x`.

Break down `x with _ | y` into its components or cases. Simplify using `[Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.cnt]`. Distinguish the cases in `hy : y < n`. Use `h ⟨y, hy⟩` as an intermediate fact. Rewrite `this` using `[← cnt_succ, ← cnt_succ]`.

Conclude with `this`. Establish `hn : n ≤ y + 1` using `by omega`. Rewrite using `[Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.cnt_of_le A hn, Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.cnt_of_le B hn]`. Break down `Nat.eq_zero_or_pos n with h0 | hpos` into its components or cases. Substitute `h0` using the available equality.

Establish `: B = ∅` using `by ext a; exact a.elim0`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Use `h ⟨n - 1, by omega⟩` as an intermediate fact. Rewrite `this` using `[← cnt_succ, ← cnt_succ]`.

Establish `e : n - 1 + 1 = n` using `by omega`. Simplify using `only [e] at this`. Rewrite `this` using `[Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.cnt_of_le A le_rfl, Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.cnt_of_le B le_rfl]`. Then use the resulting hypothesis.
-/
theorem dom_iff_le {n : ℕ} (A B : Finset (Fin n)) :
    Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.Dom A B ↔ ∀ t : Fin n, (B.filter (· ≤ t)).card ≤ (A.filter (· ≤ t)).card := by
  constructor
  · intro h t
    rw [← cnt_succ, ← cnt_succ]; exact h _
  · intro h x
    rcases x with _ | y
    · simp [Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.cnt]
    · by_cases hy : y < n
      · have := h ⟨y, hy⟩
        rw [← cnt_succ, ← cnt_succ] at this
        exact this
      · have hn : n ≤ y + 1 := by omega
        rw [Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.cnt_of_le A hn, Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.cnt_of_le B hn]
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0
          have : B = ∅ := by ext a; exact a.elim0
          rw [this]; simp
        · have := h ⟨n - 1, by omega⟩
          rw [← cnt_succ, ← cnt_succ] at this
          have e : n - 1 + 1 = n := by omega
          simp only [e] at this
          rwa [Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.cnt_of_le A le_rfl, Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.cnt_of_le B le_rfl] at this

/- English proof (translation)
Rewrite using `[← Finset.card_eq_zero, h c]`. Establish `hT : ∀ m, |pEnd mu m| ≤ ∑ i, ∑ m, |mu i m|` using `fun m => Formalism.MainNotions.LemmaBAlt.abs_entry_le_total mu (Fin.last N) m`. Establish `hT0 : (0 : ℤ) ≤ ∑ i, ∑ m, |mu i m|` using `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _`. Simplify using `only [colRange, Finset.mem_Icc, not_and_or, not_le] at hc`. Break down `hc with hc | hc` into its components or cases.

Rewrite using `[if_neg (by omega)]`. Establish `: colH (pEnd mu) c = n`. Unfold `colH`. Rewrite using `[Finset.filter_true_of_mem]`. Simplify using the standard rewrite rules.

Introduce `m _`. Use `neg_abs_le (pEnd mu m)` as an intermediate fact. Use `hT m` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers.

Rewrite using `[if_pos (by omega)]`. Unfold `colH`. Rewrite using `[Finset.card_eq_zero, Finset.filter_eq_empty_iff]`. Introduce `m _`. Use `le_abs_self (pEnd mu m)` as an intermediate fact.

Use `hT m` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem index_off_range {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) (I : ℤ → Finset (Fin n))
    (h : ∀ c, (I c).card = if 1 ≤ c then colH (pEnd mu) c else n - colH (pEnd mu) c) (c : ℤ)
    (hc : c ∉ colRange mu) : I c = ∅ := by
  rw [← Finset.card_eq_zero, h c]
  have hT : ∀ m, |pEnd mu m| ≤ ∑ i, ∑ m, |mu i m| := fun m => Formalism.MainNotions.LemmaBAlt.abs_entry_le_total mu (Fin.last N) m
  have hT0 : (0 : ℤ) ≤ ∑ i, ∑ m, |mu i m| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  simp only [colRange, Finset.mem_Icc, not_and_or, not_le] at hc
  rcases hc with hc | hc
  · rw [if_neg (by omega)]
    have : colH (pEnd mu) c = n := by
      unfold colH
      rw [Finset.filter_true_of_mem]
      · simp
      · intro m _
        have := neg_abs_le (pEnd mu m)
        have := hT m
        omega
    omega
  · rw [if_pos (by omega)]
    unfold colH
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro m _
    have := le_abs_self (pEnd mu m)
    have := hT m
    omega

/- English proof (translation)
Introduce `n N mu I`. Unfold `IsSt Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsStd`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, h2, h3⟩`. Use `⟨h2, fun c => ?_⟩` and prove the remaining obligations.

Rewrite using `[Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.dom_iff, dom_iff_le]`. Introduce `t`. Rewrite using `[← tabCol_eq, ← tabCol_eq]`. Conclude with `h3 c t`. Introduce and unpack `⟨h2, h3⟩`.

Use `⟨index_off_range mu I h2, h2, fun c t => ?_⟩` and prove the remaining obligations. Use `(dom_iff_le _ _).1 ((Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.dom_iff _ _).1 (h3 c)) t` as an intermediate fact. Rewrite `this` using `[← tabCol_eq, ← tabCol_eq]`. Conclude with `this`.
-/
theorem restStd : RestStd := by
  intro n N mu I
  unfold IsSt Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsStd
  constructor
  · rintro ⟨_, h2, h3⟩
    refine ⟨h2, fun c => ?_⟩
    rw [Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.dom_iff, dom_iff_le]
    intro t
    rw [← tabCol_eq, ← tabCol_eq]
    exact h3 c t
  · rintro ⟨h2, h3⟩
    refine ⟨index_off_range mu I h2, h2, fun c t => ?_⟩
    have := (dom_iff_le _ _).1 ((Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.dom_iff _ _).1 (h3 c)) t
    rw [← tabCol_eq, ← tabCol_eq] at this
    exact this

end Formalism.MainNotions.G.ColumnFamilies
