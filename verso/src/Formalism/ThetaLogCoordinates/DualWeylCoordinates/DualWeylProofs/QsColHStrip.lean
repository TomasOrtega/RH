import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QsColHHigh

noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
/- English proof (translation)
Introduce `x y hxy`. Break down `eq_or_lt_of_le hxy with rfl | hlt` into its components or cases. Conclude with `le_rfl`. Establish `hy : y.1 - 1 < n` using `by have := y.2; omega`. Establish `h1 : (⟨y.1 - 1, hy⟩ : Fin n).1 + 1 < n`.

Use `y.2` as an intermediate fact. Use `Fin.lt_def.1 hlt` as an intermediate fact. Simplify using `only`. Use linear arithmetic over natural numbers and integers. Establish `h2` using `hs.2.1 ⟨y.1 - 1, hy⟩ h1`.

Establish `h3 : (⟨(⟨y.1 - 1, hy⟩ : Fin n).1 + 1, h1⟩ : Fin n) = y`. Apply `Fin.ext` to reduce the goal to its premises. Use `Fin.lt_def.1 hlt` as an intermediate fact. Simplify using `only`. Use linear arithmetic over natural numbers and integers.

Rewrite `h2` using `[h3]`. Establish `h4 : lam ⟨y.1 - 1, hy⟩ ≤ lam x` using `hl (by`. Apply `Fin.le_def.2` to reduce the goal to its premises. Use `Fin.lt_def.1 hlt` as an intermediate fact. Simplify using `only`.

Use the proof step `omega)`. Conclude with `h2.trans (h4.trans (hs.1 x))`.
-/
lemma qs_dom_up {lam kap : Fin n → ℤ} {b : ℕ} (hl : Dominant lam) (hs : HStrip lam kap b) : Dominant kap := by
  intro x y hxy
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  · have hy : y.1 - 1 < n := by have := y.2; omega
    have h1 : (⟨y.1 - 1, hy⟩ : Fin n).1 + 1 < n := by
      have := y.2; have := Fin.lt_def.1 hlt; simp only; omega
    have h2 := hs.2.1 ⟨y.1 - 1, hy⟩ h1
    have h3 : (⟨(⟨y.1 - 1, hy⟩ : Fin n).1 + 1, h1⟩ : Fin n) = y := by
      apply Fin.ext; have := Fin.lt_def.1 hlt; simp only; omega
    rw [h3] at h2
    have h4 : lam ⟨y.1 - 1, hy⟩ ≤ lam x := hl (by
      apply Fin.le_def.2; have := Fin.lt_def.1 hlt; simp only; omega)
    exact h2.trans (h4.trans (hs.1 x))

omit [NeZero n] in
/- English proof (translation)
Introduce `x y hxy`. Break down `eq_or_lt_of_le hxy with rfl | hlt` into its components or cases. Conclude with `le_rfl`. Establish `h1 : x.1 + 1 < n` using `by have := y.2; have := Fin.lt_def.1 hlt; omega`. Establish `h2` using `hs.2.1 x h1`.

Establish `h4 : kap y ≤ kap ⟨x.1 + 1, h1⟩` using `hk (by`. Apply `Fin.le_def.2` to reduce the goal to its premises. Use `Fin.lt_def.1 hlt` as an intermediate fact. Simplify using `only`. Use the proof step `omega)`.

Conclude with `(hs.1 y).trans (h4.trans h2)`.
-/
lemma qs_dom_down {lam kap : Fin n → ℤ} {b : ℕ} (hk : Dominant kap) (hs : HStrip lam kap b) : Dominant lam := by
  intro x y hxy
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  · have h1 : x.1 + 1 < n := by have := y.2; have := Fin.lt_def.1 hlt; omega
    have h2 := hs.2.1 x h1
    have h4 : kap y ≤ kap ⟨x.1 + 1, h1⟩ := hk (by
      apply Fin.le_def.2; have := Fin.lt_def.1 hlt; simp only; omega)
    exact (hs.1 y).trans (h4.trans h2)

/- English proof (translation)
Establish `h1 : colH lam c ≤ colH kap c`. Assume the negation of the conclusion as `hcon`. Establish `hlt : colH kap c < n` using `lt_of_lt_of_le (not_le.1 hcon) (colH_le lam c)`. Establish `h2` using `(qb_lt_colH_iff hl c ⟨colH kap c, hlt⟩).1 (not_le.1 hcon)`. Establish `h3` using `(qb_lt_colH_iff hk c ⟨colH kap c, hlt⟩).2 (h2.trans (hs.1 _))`.

Conclude with `lt_irrefl _ h3`. Establish `h2 : colH kap c ≤ colH lam c + 1`. Assume the negation of the conclusion as `hcon`. Establish `hlt : colH lam c + 1 < n` using `lt_of_lt_of_le (not_le.1 hcon) (colH_le kap c)`. Establish `h2` using `(qb_lt_colH_iff hk c ⟨colH lam c + 1, hlt⟩).1 (not_le.1 hcon)`.

Establish `h3` using `hs.2.1 ⟨colH lam c, by omega⟩ hlt`. Establish `h4` using `(qb_lt_colH_iff hl c ⟨colH lam c, by omega⟩).2 (h2.trans h3)`. Conclude with `lt_irrefl _ h4`. Use linear arithmetic over natural numbers and integers.
-/
lemma qs_colH_strip {lam kap : Fin n → ℤ} {b : ℕ} (hl : Dominant lam) (hk : Dominant kap) (hs : HStrip lam kap b)
    (c : ℤ) : colH kap c = colH lam c ∨ colH kap c = colH lam c + 1 := by
  have h1 : colH lam c ≤ colH kap c := by
    by_contra hcon
    have hlt : colH kap c < n := lt_of_lt_of_le (not_le.1 hcon) (colH_le lam c)
    have h2 := (qb_lt_colH_iff hl c ⟨colH kap c, hlt⟩).1 (not_le.1 hcon)
    have h3 := (qb_lt_colH_iff hk c ⟨colH kap c, hlt⟩).2 (h2.trans (hs.1 _))
    exact lt_irrefl _ h3
  have h2 : colH kap c ≤ colH lam c + 1 := by
    by_contra hcon
    have hlt : colH lam c + 1 < n := lt_of_lt_of_le (not_le.1 hcon) (colH_le kap c)
    have h2 := (qb_lt_colH_iff hk c ⟨colH lam c + 1, hlt⟩).1 (not_le.1 hcon)
    have h3 := hs.2.1 ⟨colH lam c, by omega⟩ hlt
    have h4 := (qb_lt_colH_iff hl c ⟨colH lam c, by omega⟩).2 (h2.trans h3)
    exact lt_irrefl _ h4
  omega

def qs_D (lam kap : Fin n → ℤ) : Finset ℤ :=
  (Finset.Ioc (lam (lastIdx n)) (kap 0)).filter fun c => colH kap c = colH lam c + 1

/- English proof (translation)
The claim follows from `Finset.filter_subset _ _`.
-/
lemma qs_D_sub (lam kap : Fin n → ℤ) : qs_D lam kap ⊆ Finset.Ioc (lam (lastIdx n)) (kap 0) := Finset.filter_subset _ _

/- English proof (translation)
Simplify using `only [qs_D, mem_filter, mem_Ioc, and_iff_right_iff_imp]`. Introduce `h`. Prove the components needed by the constructor for the conclusion. Assume the negation of the conclusion as `hcon`. Use `qs_colH_low hl (not_lt.1 hcon)` as an intermediate fact.

Use `colH_le kap c` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Assume the negation of the conclusion as `hcon`. Use `qs_colH_high hk (not_le.1 hcon)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
lemma qs_mem_D {lam kap : Fin n → ℤ} (hl : Dominant lam) (hk : Dominant kap) (c : ℤ) :
    c ∈ qs_D lam kap ↔ colH kap c = colH lam c + 1 := by
  simp only [qs_D, mem_filter, mem_Ioc, and_iff_right_iff_imp]
  intro h
  constructor
  · by_contra hcon
    have := qs_colH_low hl (not_lt.1 hcon)
    have := colH_le kap c
    omega
  · by_contra hcon
    have := qs_colH_high hk (not_le.1 hcon)
    omega

def qs_mc (lam kap : Fin n → ℤ) : ↥(qs_D lam kap) → Fin n := fun c =>
  ⟨colH lam c.1, by have := (Finset.mem_filter.1 c.2).2; have := colH_le kap c.1; omega⟩

/- English proof (translation)
Establish `h1 : (univ.filter fun c : ↥(qs_D lam kap) => qs_mc lam kap c = x).map (Function.Embedding.subtype _) = Finset.Ioc (lam x) (kap x)`. Use extensionality with `c`. Simplify using `only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype, Subtype.exists, exists_and_right, exists_eq_right, mem_Ioc]`. Establish `e1` using `qb_lt_colH_iff hl c x`. Establish `e2` using `qb_lt_colH_iff hk c x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hc, hx⟩`. Establish `h3` using `(qs_mem_D hl hk c).1 hc`. Establish `h4 : colH lam c = x.1` using `congrArg Fin.val hx`. Prove the components needed by the constructor for the conclusion.

Assume the negation of the conclusion as `hcon`. Use `e1.2 (not_lt.1 hcon)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `e2.1 (by omega)`. Introduce and unpack `⟨h3, h4⟩`.

Establish `h5` using `e2.2 h4`. Establish `h6 : ¬ x.1 < colH lam c` using `fun h => absurd (e1.1 h) (not_le.2 h3)`. Establish `h7` using `qs_colH_strip hl hk hs c`. Conclude with `⟨(qs_mem_D hl hk c).2 (by omega), Fin.ext (by simp only [qs_mc]; omega)⟩`. Rewrite using `[qs_cnt, ← Finset.card_map (Function.Embedding.subtype _), h1, Int.card_Ioc, Int.toNat_of_nonneg (by have := hs.1 x; omega)]`.
-/
lemma qs_cnt_mc {lam kap : Fin n → ℤ} {b : ℕ} (hl : Dominant lam) (hk : Dominant kap) (hs : HStrip lam kap b)
    (x : Fin n) : ((qs_cnt (qs_mc lam kap) x : ℕ) : ℤ) = kap x - lam x := by
  have h1 : (univ.filter fun c : ↥(qs_D lam kap) => qs_mc lam kap c = x).map (Function.Embedding.subtype _) =
      Finset.Ioc (lam x) (kap x) := by
    ext c
    simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype, Subtype.exists,
      exists_and_right, exists_eq_right, mem_Ioc]
    have e1 := qb_lt_colH_iff hl c x
    have e2 := qb_lt_colH_iff hk c x
    constructor
    · rintro ⟨hc, hx⟩
      have h3 := (qs_mem_D hl hk c).1 hc
      have h4 : colH lam c = x.1 := congrArg Fin.val hx
      constructor
      · by_contra hcon; have := e1.2 (not_lt.1 hcon); omega
      · exact e2.1 (by omega)
    · rintro ⟨h3, h4⟩
      have h5 := e2.2 h4
      have h6 : ¬ x.1 < colH lam c := fun h => absurd (e1.1 h) (not_le.2 h3)
      have h7 := qs_colH_strip hl hk hs c
      exact ⟨(qs_mem_D hl hk c).2 (by omega), Fin.ext (by simp only [qs_mc]; omega)⟩
  rw [qs_cnt, ← Finset.card_map (Function.Embedding.subtype _), h1, Int.card_Ioc,
    Int.toNat_of_nonneg (by have := hs.1 x; omega)]

/- English proof (translation)
Establish `h1` using `qs_sum_cnt (qs_mc lam kap)`. Establish `h2 : ((∑ x, qs_cnt (qs_mc lam kap) x : ℕ) : ℤ) = (b : ℤ)`. Rewrite using `[← hs.2.2]`. Use `push_cast`. Conclude with `Finset.sum_congr rfl fun x _ => qs_cnt_mc hl hk hs x`.

Rewrite `h2` using `[h1]`. Conclude with `h2` after adjusting the coercions.
-/
lemma qs_card_D {lam kap : Fin n → ℤ} {b : ℕ} (hl : Dominant lam) (hk : Dominant kap) (hs : HStrip lam kap b) :
    Fintype.card ↥(qs_D lam kap) = b := by
  have h1 := qs_sum_cnt (qs_mc lam kap)
  have h2 : ((∑ x, qs_cnt (qs_mc lam kap) x : ℕ) : ℤ) = (b : ℤ) := by
    rw [← hs.2.2]; push_cast
    exact Finset.sum_congr rfl fun x _ => qs_cnt_mc hl hk hs x
  rw [h1] at h2
  exact_mod_cast h2

omit [NeZero n] in
/- English proof (translation)
Establish `: (qs_ini h : Finset (Fin n)).filter ((⟨h, hh⟩ : Fin n) < ·) = ∅`. Use extensionality with `x`. Simplify using `only [qs_ini, mem_filter, mem_univ, true_and, notMem_empty, iff_false, not_and, not_lt]`. Introduce `hx; exact Fin.le_def.2 (by simp only; omega)`. Rewrite using `[qs_sg, this]`.

Simplify using the standard rewrite rules.
-/
lemma qs_sg_ini (h : ℕ) (hh : h < n) : qs_sg (qs_ini h) (⟨h, hh⟩ : Fin n) = 1 := by
  have : (qs_ini h : Finset (Fin n)).filter ((⟨h, hh⟩ : Fin n) < ·) = ∅ := by
    ext x; simp only [qs_ini, mem_filter, mem_univ, true_and, notMem_empty, iff_false, not_and, not_lt]
    intro hx; exact Fin.le_def.2 (by simp only; omega)
  rw [qs_sg, this]; simp

omit [NeZero n] in
/- English proof (translation)
Use extensionality with `x`. Simplify using `only [qs_ini, mem_erase, mem_filter, mem_univ, true_and, ne_eq, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers.
-/
lemma qs_ini_erase (h : ℕ) (hh : h < n) : (qs_ini (h + 1) : Finset (Fin n)).erase ⟨h, hh⟩ = qs_ini h := by
  ext x
  simp only [qs_ini, mem_erase, mem_filter, mem_univ, true_and, ne_eq, Fin.ext_iff]
  omega

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use function extensionality and compare the values at `c`. Establish `h3` using `h1 c`. Establish `h4` using `congrFun h2 c.1`.

Establish `h5` using `(qs_mem_D hl hk c.1).1 c.2`. Rewrite `h4` using `[qs_rem_mem, qs_ext_can hl, qs_ext_can hk]`. Rewrite `h3` using `[qs_ext_can hk]`. Establish `h6 : m c ∉ (qs_ini (colH lam c.1) : Finset (Fin n))` using `by rw [h4]; simp`. Simplify using `only [qs_ini, mem_filter, mem_univ, true_and] at h3 h6`.

Conclude with `Fin.ext (by simp only [qs_mc]; omega)`. Introduce and unpack `rfl`. Use `⟨fun c => ?_, ?_⟩` and prove the remaining obligations. Establish `h5` using `(qs_mem_D hl hk c.1).1 c.2`. Rewrite using `[qs_ext_can hk]`.

Simplify using `only [qs_ini, qs_mc, mem_filter, mem_univ, true_and]`. Use linear arithmetic over natural numbers and integers. Use function extensionality and compare the values at `c`. Distinguish the cases in `hc : c ∈ qs_D lam kap`. Establish `h5` using `(qs_mem_D hl hk c).1 hc`.

Establish `h6` using `qs_rem_mem (qs_D lam kap) (qs_ext kap (canT kap)) (qs_mc lam kap) ⟨c, hc⟩`. Simplify using `only at h6`. Rewrite using `[h6, qs_ext_can hl, qs_ext_can hk, h5]`. Conclude with `(qs_ini_erase _ _).symm`. Rewrite using `[qs_rem_not _ _ _ hc, qs_ext_can hl, qs_ext_can hk]`.

Establish `h7` using `qs_colH_strip hl hk hs c`. Establish `h8` using `(qs_mem_D hl hk c).not.1 hc`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.
-/
lemma qs_can_iff {lam kap : Fin n → ℤ} {b : ℕ} (hl : Dominant lam) (hk : Dominant kap) (hs : HStrip lam kap b)
    (m : ↥(qs_D lam kap) → Fin n) :
    ((∀ c : ↥(qs_D lam kap), m c ∈ qs_ext kap (canT kap) c.1) ∧
      qs_ext lam (canT lam) = qs_rem (qs_D lam kap) (qs_ext kap (canT kap)) m) ↔ m = qs_mc lam kap := by
  constructor
  · rintro ⟨h1, h2⟩
    funext c
    have h3 := h1 c
    have h4 := congrFun h2 c.1
    have h5 := (qs_mem_D hl hk c.1).1 c.2
    rw [qs_rem_mem, qs_ext_can hl, qs_ext_can hk] at h4
    rw [qs_ext_can hk] at h3
    have h6 : m c ∉ (qs_ini (colH lam c.1) : Finset (Fin n)) := by rw [h4]; simp
    simp only [qs_ini, mem_filter, mem_univ, true_and] at h3 h6
    exact Fin.ext (by simp only [qs_mc]; omega)
  · rintro rfl
    refine ⟨fun c => ?_, ?_⟩
    · have h5 := (qs_mem_D hl hk c.1).1 c.2
      rw [qs_ext_can hk]
      simp only [qs_ini, qs_mc, mem_filter, mem_univ, true_and]; omega
    · funext c
      by_cases hc : c ∈ qs_D lam kap
      · have h5 := (qs_mem_D hl hk c).1 hc
        have h6 := qs_rem_mem (qs_D lam kap) (qs_ext kap (canT kap)) (qs_mc lam kap) ⟨c, hc⟩
        simp only at h6
        rw [h6, qs_ext_can hl, qs_ext_can hk, h5]
        exact (qs_ini_erase _ _).symm
      · rw [qs_rem_not _ _ _ hc, qs_ext_can hl, qs_ext_can hk]
        have h7 := qs_colH_strip hl hk hs c
        have h8 := (qs_mem_D hl hk c).not.1 hc
        congr 1; omega

/- English proof (translation)
Distinguish the cases in `hc : c ∈ qs_D lam kap`. Establish `h5` using `(qs_mem_D hl hk c).1 hc`. Establish `h6` using `qs_rem_mem (qs_D lam kap) K m ⟨c, hc⟩`. Simplify using `only at h6`. Rewrite using `[h6, Finset.card_erase_of_mem (hm ⟨c, hc⟩), hK, h5]`.

Both sides reduce to the same expression. Rewrite using `[qs_rem_not _ _ _ hc, hK]`. Establish `h7` using `qs_colH_strip hl hk hs c`. Establish `h8` using `(qs_mem_D hl hk c).not.1 hc`. Use linear arithmetic over natural numbers and integers.
-/
lemma qs_rem_card {lam kap : Fin n → ℤ} {b : ℕ} (hl : Dominant lam) (hk : Dominant kap) (hs : HStrip lam kap b)
    (K : ℤ → Finset (Fin n)) (hK : ∀ c, (K c).card = colH kap c) (m : ↥(qs_D lam kap) → Fin n)
    (hm : ∀ c : ↥(qs_D lam kap), m c ∈ K c.1) (c : ℤ) : (qs_rem (qs_D lam kap) K m c).card = colH lam c := by
  by_cases hc : c ∈ qs_D lam kap
  · have h5 := (qs_mem_D hl hk c).1 hc
    have h6 := qs_rem_mem (qs_D lam kap) K m ⟨c, hc⟩
    simp only at h6
    rw [h6, Finset.card_erase_of_mem (hm ⟨c, hc⟩), hK, h5]; rfl
  · rw [qs_rem_not _ _ _ hc, hK]
    have h7 := qs_colH_strip hl hk hs c
    have h8 := (qs_mem_D hl hk c).not.1 hc
    omega

/- English proof (translation)
Distinguish the cases in `hc : c ∈ qs_D lam kap`. Establish `h5` using `(qs_mem_D hl hk c).1 hc`. Establish `h6` using `qs_add_mem (qs_D lam kap) J a ⟨c, hc⟩`. Simplify using `only at h6`. Rewrite using `[h6, Finset.card_insert_of_notMem (ha ⟨c, hc⟩), hJ, h5]`.

Rewrite using `[qs_add_not _ _ _ hc, hJ]`. Establish `h7` using `qs_colH_strip hl hk hs c`. Establish `h8` using `(qs_mem_D hl hk c).not.1 hc`. Use linear arithmetic over natural numbers and integers.
-/
lemma qs_add_card {lam kap : Fin n → ℤ} {b : ℕ} (hl : Dominant lam) (hk : Dominant kap) (hs : HStrip lam kap b)
    (J : ℤ → Finset (Fin n)) (hJ : ∀ c, (J c).card = colH lam c) (a : ↥(qs_D lam kap) → Fin n)
    (ha : ∀ c : ↥(qs_D lam kap), a c ∉ J c.1) (c : ℤ) : (qs_add (qs_D lam kap) J a c).card = colH kap c := by
  by_cases hc : c ∈ qs_D lam kap
  · have h5 := (qs_mem_D hl hk c).1 hc
    have h6 := qs_add_mem (qs_D lam kap) J a ⟨c, hc⟩
    simp only at h6
    rw [h6, Finset.card_insert_of_notMem (ha ⟨c, hc⟩), hJ, h5]
  · rw [qs_add_not _ _ _ hc, hJ]
    have h7 := qs_colH_strip hl hk hs c
    have h8 := (qs_mem_D hl hk c).not.1 hc
    omega

end Formalism.InvariantFactorPaths.ColumnFamilies
