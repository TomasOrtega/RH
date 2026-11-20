import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift

set_option autoImplicit false

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI.AltClosed

variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι]

/- English proof (translation)
Use function extensionality and compare the values at `t`. Simplify using `only [Dtot, delta, Pi.add_apply, smul_add, Finset.sum_add_distrib, map_add]`. Normalize the expressions using the abelian group laws.
-/
theorem dtot_add {E : Type} [AddCommGroup E] (d : E →+ E) (c c' : Finset ι → E) :
    Dtot d (c + c') = Dtot d c + Dtot d c' := by
  funext t
  simp only [Dtot, delta, Pi.add_apply, smul_add, Finset.sum_add_distrib, map_add]
  abel

def dtotHom {E : Type} [AddCommGroup E] (d : E →+ E) : (Finset ι → E) →+ (Finset ι → E) :=
  AddMonoidHom.mk' (Dtot d) (dtot_add d)

omit [LinearOrder ι] in

/- English proof (translation)
Simplify using `[oneC]`.
-/
theorem oneC_empty : (oneC : Finset ι → ExteriorAlgebra K V) ∅ = 0 := by
  simp [oneC]

/- English proof (translation)
Establish `h1` using `hd.mul 1 1`. Simplify using `only [mul_one, map_one, one_mul] at h1`. Conclude with `add_left_cancel (a := d 1) (by rw [add_zero]; exact h1.symm)`.
-/
theorem d_one (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (hd : IsOddDer d) : d 1 = 0 := by
  have h1 := hd.mul 1 1
  simp only [mul_one, map_one, one_mul] at h1
  exact add_left_cancel (a := d 1) (by rw [add_zero]; exact h1.symm)

/- English proof (translation)
Establish `hne : x ≠ y` using `ne_of_lt h`. Simplify using `only [delta]`. Rewrite using `[Finset.sum_pair hne]`. Establish `e1 : ({x, y} : Finset ι).erase x = {y}`. Use extensionality with `z`.

Simplify using `only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hz, hz' | hz'⟩`. Conclude with `absurd hz' hz`. Conclude with `hz'`.

Introduce and unpack `rfl`. Conclude with `⟨hne.symm, Or.inr rfl⟩`. Establish `e2 : ({x, y} : Finset ι).erase y = {x}`. Use extensionality with `z`. Simplify using `only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hz, hz' | hz'⟩`. Conclude with `hz'`. Conclude with `absurd hz' hz`. Introduce and unpack `rfl`.

Conclude with `⟨hne, Or.inl rfl⟩`. Establish `s1 : GlobalTheory.cubeSign ({x, y} : Finset ι) x = 1`. Unfold `GlobalTheory.cubeSign`. Establish `: ({z ∈ ({x, y} : Finset ι) | z < x}) = ∅`. Use extensionality with `z`.

Simplify using `only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]`. Introduce and unpack `(rfl | rfl) hz`. Conclude with `lt_irrefl _ hz`. Conclude with `lt_asymm h hz`. Rewrite using `[this]`.

Simplify using the standard rewrite rules. Establish `s2 : GlobalTheory.cubeSign ({x, y} : Finset ι) y = -1`. Unfold `GlobalTheory.cubeSign`. Establish `: ({z ∈ ({x, y} : Finset ι) | z < y}) = {x}`. Use extensionality with `z`.

Simplify using `only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨rfl | rfl, hz⟩`. Both sides reduce to the same expression. Conclude with `absurd hz (lt_irrefl _)`.

Introduce and unpack `rfl`. Conclude with `⟨Or.inl rfl, h⟩`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Rewrite using `[e1, e2, s1, s2]`.

Simplify using `[oneC]`.
-/
theorem delta_oneC_pair {x y : ι} (h : x < y) :
    delta (oneC : Finset ι → ExteriorAlgebra K V) {x, y} = 0 := by
  have hne : x ≠ y := ne_of_lt h
  simp only [delta]
  rw [Finset.sum_pair hne]
  have e1 : ({x, y} : Finset ι).erase x = {y} := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, hz' | hz'⟩
      · exact absurd hz' hz
      · exact hz'
    · rintro rfl
      exact ⟨hne.symm, Or.inr rfl⟩
  have e2 : ({x, y} : Finset ι).erase y = {x} := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, hz' | hz'⟩
      · exact hz'
      · exact absurd hz' hz
    · rintro rfl
      exact ⟨hne, Or.inl rfl⟩
  have s1 : GlobalTheory.cubeSign ({x, y} : Finset ι) x = 1 := by
    unfold GlobalTheory.cubeSign
    have : ({z ∈ ({x, y} : Finset ι) | z < x}) = ∅ := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
      rintro (rfl | rfl) hz
      · exact lt_irrefl _ hz
      · exact lt_asymm h hz
    rw [this]
    simp
  have s2 : GlobalTheory.cubeSign ({x, y} : Finset ι) y = -1 := by
    unfold GlobalTheory.cubeSign
    have : ({z ∈ ({x, y} : Finset ι) | z < y}) = {x} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hz⟩
        · rfl
        · exact absurd hz (lt_irrefl _)
      · rintro rfl
        exact ⟨Or.inl rfl, h⟩
    rw [this]
    simp
  rw [e1, e2, s1, s2]
  simp [oneC]

/- English proof (translation)
Distinguish the cases in `h2 : t.card = 2`. Take `⟨x, y, hxy, rfl⟩` from `Finset.card_eq_two.mp h2`. Break down `lt_or_gt_of_ne hxy with hlt | hlt` into its components or cases. Conclude with `delta_oneC_pair hlt`. Rewrite using `[Finset.pair_comm]`.

Conclude with `delta_oneC_pair hlt`. Simplify using `only [delta]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `i hi`. Establish `hpos` using `Finset.card_pos.mpr ⟨i, hi⟩`.

Establish `hc : ¬ (t.erase i).card = 1`. Rewrite using `[Finset.card_erase_of_mem hi]`. Use linear arithmetic over natural numbers and integers. Simplify using `[oneC, hc]`.
-/
theorem delta_oneC (t : Finset ι) : delta (oneC : Finset ι → ExteriorAlgebra K V) t = 0 := by
  by_cases h2 : t.card = 2
  · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp h2
    rcases lt_or_gt_of_ne hxy with hlt | hlt
    · exact delta_oneC_pair hlt
    · rw [Finset.pair_comm]
      exact delta_oneC_pair hlt
  · simp only [delta]
    apply Finset.sum_eq_zero
    intro i hi
    have hpos := Finset.card_pos.mpr ⟨i, hi⟩
    have hc : ¬ (t.erase i).card = 1 := by
      rw [Finset.card_erase_of_mem hi]
      omega
    simp [oneC, hc]

/- English proof (translation)
Use function extensionality and compare the values at `t`. Simplify using `only [Dtot, delta_oneC, zero_add, Pi.zero_apply]`. Unfold `oneC`. Apply the tactic sequence `split_ifs <;> simp [d_one d hd]`.
-/
theorem dtot_oneC (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (hd : IsOddDer d) :
    Dtot d (oneC : Finset ι → ExteriorAlgebra K V) = 0 := by
  funext t
  simp only [Dtot, delta_oneC, zero_add, Pi.zero_apply]
  unfold oneC
  split_ifs <;> simp [d_one d hd]

/- English proof (translation)
Unfold `GlobalTheory.cubeSign`. Establish `e : ({x ∈ s | x < s.min' hs}) = ∅`. Apply `Finset.filter_false_of_mem` to reduce the goal to its premises. Introduce `x hx`. Conclude with `not_lt.mpr (s.min'_le x hx)`.

Rewrite using `[e]`. Simplify using the standard rewrite rules.
-/
private theorem cubeSign_min_eq_one (s : Finset ι) (hs : s.Nonempty) : GlobalTheory.cubeSign s (s.min' hs) = 1 := by
  unfold GlobalTheory.cubeSign
  have e : ({x ∈ s | x < s.min' hs}) = ∅ := by
    apply Finset.filter_false_of_mem
    intro x hx
    exact not_lt.mpr (s.min'_le x hx)
  rw [e]
  simp

/- English proof (translation)
Establish `hne : i ≠ s.min' hs` using `Finset.ne_of_mem_erase hi`. Establish `his : i ∈ s` using `Finset.mem_of_mem_erase hi`. Establish `hlt : s.min' hs < i` using `lt_of_le_of_ne (s.min'_le i his) hne.symm`. Unfold `GlobalTheory.cubeSign`. Establish `hfil : ({x ∈ s | x < i}) = insert (s.min' hs) ({x ∈ s.erase (s.min' hs) | x < i})`.

Use extensionality with `x`. Simplify using `only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hxs, hxi⟩`. Distinguish the cases in `hx : x = s.min' hs`.

Conclude with `Or.inl hx`. Conclude with `Or.inr ⟨⟨hx, hxs⟩, hxi⟩`. Introduce and unpack `(hx | ⟨⟨_, hxs⟩, hxi⟩)`. Rewrite using `[hx]`. Conclude with `⟨s.min'_mem hs, hlt⟩`.

Conclude with `⟨hxs, hxi⟩`. Rewrite using `[hfil, Finset.card_insert_of_notMem (by simp), pow_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem cubeSign_eq_neg_cubeSign_erase_min (s : Finset ι) (hs : s.Nonempty) (i : ι) (hi : i ∈ s.erase (s.min' hs)) :
    GlobalTheory.cubeSign s i = -GlobalTheory.cubeSign (s.erase (s.min' hs)) i := by
  have hne : i ≠ s.min' hs := Finset.ne_of_mem_erase hi
  have his : i ∈ s := Finset.mem_of_mem_erase hi
  have hlt : s.min' hs < i := lt_of_le_of_ne (s.min'_le i his) hne.symm
  unfold GlobalTheory.cubeSign
  have hfil : ({x ∈ s | x < i}) = insert (s.min' hs) ({x ∈ s.erase (s.min' hs) | x < i}) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨hxs, hxi⟩
      by_cases hx : x = s.min' hs
      · exact Or.inl hx
      · exact Or.inr ⟨⟨hx, hxs⟩, hxi⟩
    · rintro (hx | ⟨⟨_, hxs⟩, hxi⟩)
      · rw [hx]
        exact ⟨s.min'_mem hs, hlt⟩
      · exact ⟨hxs, hxi⟩
  rw [hfil, Finset.card_insert_of_notMem (by simp), pow_succ]
  ring

/- English proof (translation)
Unfold `delta`. Rewrite using `[← Finset.add_sum_erase s _ (s.min'_mem hs), cubeSign_min_eq_one s hs, one_smul, sub_eq_add_neg, ← Finset.sum_neg_distrib]`. Use `congr 1`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i hi`.

Rewrite using `[cubeSign_eq_neg_cubeSign_erase_min s hs i hi, neg_smul]`.
-/
private theorem delta_eq_erase_min_sub_sum_cubeSign {E : Type} [AddCommGroup E] (c : Finset ι → E) (s : Finset ι) (hs : s.Nonempty) :
    delta c s = c (s.erase (s.min' hs)) -
      ∑ i ∈ s.erase (s.min' hs), GlobalTheory.cubeSign (s.erase (s.min' hs)) i • c (s.erase i) := by
  unfold delta
  rw [← Finset.add_sum_erase s _ (s.min'_mem hs), cubeSign_min_eq_one s hs, one_smul, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [cubeSign_eq_neg_cubeSign_erase_min s hs i hi, neg_smul]

/- English proof (translation)
Substitute `hm` using the available equality. Unfold `Lop`. Rewrite using `[dif_pos ht]`.
-/
private theorem Lop_apply_of_min_eq (f : ι → V →+ V) (h : ι → ι → V →+ K) (v : V)
    (y : Finset ι → ExteriorAlgebra K V) (t : Finset ι) (m0 : ι) (ht : t.Nonempty) (hm : t.min' ht = m0) :
    Lop f h v y t = (-1 : ℤ) ^ t.card • (ExteriorAlgebra.ι K (f m0 v) * y t) +
      (if h2 : (t.erase m0).Nonempty then h m0 ((t.erase m0).min' h2) v • y (t.erase m0) else 0) := by
  subst hm
  unfold Lop
  rw [dif_pos ht]

/- English proof (translation)
Rewrite using `[Finset.card_erase_of_mem hi]`. Take `⟨k, hk⟩ : ∃ k, t.card = k + 1` from `⟨t.card - 1, by have := Finset.card_pos.mpr ⟨i, hi⟩; omega⟩`. Rewrite using `[hk, Nat.add_sub_cancel, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem neg_one_pow_card_erase_of_mem (t : Finset ι) (i : ι) (hi : i ∈ t) :
    (-1 : ℤ) ^ (t.erase i).card = -(-1) ^ t.card := by
  rw [Finset.card_erase_of_mem hi]
  obtain ⟨k, hk⟩ : ∃ k, t.card = k + 1 := ⟨t.card - 1, by have := Finset.card_pos.mpr ⟨i, hi⟩; omega⟩
  rw [hk, Nat.add_sub_cancel, pow_succ]
  ring

/- English proof (translation)
Establish `hys : ∀ s : Finset ι, d (y s) = -((-1 : ℤ) ^ s.card • delta y s)`. Introduce `s`. Establish `e0` using `congrFun hy s`. Simplify using `only [Dtot, Pi.zero_apply] at e0`. Establish `e2 : (-1 : ℤ) ^ s.card • d (y s) = -delta y s`.

Rewrite using `[eq_neg_iff_add_eq_zero, add_comm]`. Conclude with `e0`. Establish `e1 : ((-1 : ℤ) ^ s.card * (-1) ^ s.card) = 1`. Rewrite using `[← mul_pow]`. Simplify using the standard rewrite rules.

Combine the equalities or inequalities in the displayed calculation. Establish `dsm : ∀ (k : K) (x : ExteriorAlgebra K V), d (k • x) = d (algebraMap K _ k) * x + k • d x`. Introduce `k x`. Rewrite using `[Algebra.smul_def, hd.mul, AlgHom.commutes, ← Algebra.smul_def]`. Establish `dω : ∀ (i : ι) (x : ExteriorAlgebra K V), d (ExteriorAlgebra.ι K (f i v) * x) = -(ExteriorAlgebra.ι K (f i v) * d x)`.

Introduce `i x`. Rewrite using `[hd.mul, hD.closed, zero_mul, zero_add]`. Rewrite using `[show CliffordAlgebra.involute (ExteriorAlgebra.ι K (f i v)) = -ExteriorAlgebra.ι K (f i v) from CliffordAlgebra.involute_ι _, neg_mul]`. Establish `hε : ∀ (n : ℕ) (x : ExteriorAlgebra K V), (-1 : ℤ) ^ n • ((-1 : ℤ) ^ n • x) = x`. Introduce `n x`.

Rewrite using `[← mul_smul, ← mul_pow]`. Simplify using the standard rewrite rules. Use function extensionality and compare the values at `s`. Simplify using `only [Dtot, Pi.zero_apply]`. Distinguish the cases in `hs : s.Nonempty`.

Use `swap`. Rewrite using `[Finset.not_nonempty_iff_eq_empty.mp hs]`. Simplify using `[delta, Lop]`. Rewrite using `[delta_eq_erase_min_sub_sum_cubeSign _ s hs]`. Establish `hdy` using `delta_eq_erase_min_sub_sum_cubeSign y s hs`.

Use `set m := s.min' hs`. Use `set s' := s.erase m`. Establish `hms : m ∈ s` using `s.min'_mem hs`. Establish `hLs` using `Lop_apply_of_min_eq f h v y s m hs rfl`. Establish `hLi : ∀ i ∈ s', Lop f h v y (s.erase i) = -((-1 : ℤ) ^ s.card • (ExteriorAlgebra.ι K (f m v) * y (s.erase i))) + (if h2 : (s'.erase i).Nonempty then h m ((s'.erase i).min' h2) v • y (s'.erase i) else 0)`.

Introduce `i hi`. Establish `hne : i ≠ m` using `Finset.ne_of_mem_erase hi`. Establish `his : i ∈ s` using `Finset.mem_of_mem_erase hi`. Establish `hmi : m ∈ s.erase i` using `Finset.mem_erase.mpr ⟨hne.symm, hms⟩`. Establish `hmin : (s.erase i).min' ⟨m, hmi⟩ = m` using `le_antisymm ((s.erase i).min'_le m hmi) (Finset.le_min' _ _ _ (fun z hz => s.min'_le z (Finset.mem_of_mem_erase hz)))`.

Rewrite using `[Lop_apply_of_min_eq f h v y (s.erase i) m ⟨m, hmi⟩ hmin, neg_one_pow_card_erase_of_mem s i his, neg_smul, Finset.erase_right_comm]`. Establish `hsum : ∑ i ∈ s', GlobalTheory.cubeSign s' i • Lop f h v y (s.erase i) = -((-1 : ℤ) ^ s.card • (ExteriorAlgebra.ι K (f m v) * ∑ i ∈ s', GlobalTheory.cubeSign s' i • y (s.erase i))) + ∑ i ∈ s', GlobalTheory.cubeSign s' i • (if h2 : (s'.erase i).Nonempty then h m ((s'.erase i).min' …`. Rewrite using `[Finset.mul_sum, Finset.smul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i hi`.

Rewrite using `[hLi i hi, smul_add, smul_neg, mul_smul_comm, smul_comm (GlobalTheory.cubeSign s' i)]`. Establish `hX : ∑ i ∈ s', GlobalTheory.cubeSign s' i • y (s.erase i) = y s' - delta y s`. Rewrite using `[hdy]`. Normalize the expressions using the abelian group laws. Establish `hLs2 : Lop f h v y s = (-1 : ℤ) ^ s.card • (ExteriorAlgebra.ι K (f m v) * y s) + (if h2 : s'.Nonempty then h m (s'.min' h2) v • y s' else 0)` using `hLs`.

Rewrite using `[hsum, hLs2, hX, map_add, map_zsmul, dω, hys s]`. Distinguish the cases in `h2 : s'.Nonempty`. Use `set n := s'.min' h2 with hn_eq`. Establish `hns : n ∈ s'` using `s'.min'_mem h2`. Establish `hLs' : Lop f h v y s' = (-1 : ℤ) ^ s'.card • (ExteriorAlgebra.ι K (f n v) * y s') + (if h3 : (s'.erase n).Nonempty then h n ((s'.erase n).min' h3) v • y (s'.erase n) else 0)` using `Lop_apply_of_min_eq f h v y s' n h2 rfl`.

Establish `hc : (-1 : ℤ) ^ s'.card = -(-1) ^ s.card` using `neg_one_pow_card_erase_of_mem s m hms`. Establish `hSh : ∑ i ∈ s', GlobalTheory.cubeSign s' i • (if h3 : (s'.erase i).Nonempty then h m ((s'.erase i).min' h3) v • y (s'.erase i) else 0) = (if h3 : (s'.erase n).Nonempty then h n ((s'.erase n).min' h3) v • y (s'.erase n) else 0) + h m n v • delta y s'`. Rewrite using `[← sub_eq_iff_eq_add]`. Unfold `delta`. Rewrite using `[Finset.smul_sum, ← Finset.sum_sub_distrib, Finset.sum_eq_single n]`.

Rewrite using `[show GlobalTheory.cubeSign s' n = 1 from cubeSign_min_eq_one s' h2]`. Simplify using `only [one_smul]`. Distinguish the cases in `h3 : (s'.erase n).Nonempty`. Rewrite using `[dif_pos h3, dif_pos h3, ← sub_smul]`. Use `congr 1`.

Rewrite using `[← hD.cocycle m n ((s'.erase n).min' h3) v]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[dif_neg h3, dif_neg h3, Finset.not_nonempty_iff_eq_empty.mp h3, hy0]`. Simplify using the standard rewrite rules. Introduce `b hb hbn`.

Establish `hnb : n ∈ s'.erase b` using `Finset.mem_erase.mpr ⟨fun e => hbn e.symm, hns⟩`. Establish `hmin : (s'.erase b).min' ⟨n, hnb⟩ = n` using `le_antisymm ((s'.erase b).min'_le n hnb) (Finset.le_min' _ _ _ (fun z hz => s'.min'_le z (Finset.mem_of_mem_erase hz)))`. Rewrite using `[dif_pos ⟨n, hnb⟩, hmin, smul_comm (h m n v) (GlobalTheory.cubeSign s' b), sub_self]`. Introduce `hn`. Conclude with `absurd hns hn`.

Establish `hcomm : ∀ x : ExteriorAlgebra K V, h m n v • ((-1 : ℤ) ^ s.card • x) = (-1 : ℤ) ^ s.card • (h m n v • x)` using `fun x => smul_comm _ _ _`. Rewrite using `[dif_pos h2, ← hn_eq, hSh, hLs', dsm, hD.dh, hys s', hc]`. Simplify using `only [neg_smul, smul_neg, neg_neg, mul_neg, mul_sub, sub_mul, smul_add, smul_sub, mul_smul_comm, hε, hcomm]`. Normalize the expressions using the abelian group laws. Establish `hs'e : s' = ∅` using `Finset.not_nonempty_iff_eq_empty.mp h2`.

Establish `hdy0 : delta y s = 0`. Rewrite using `[hdy, hs'e]`. Simplify using `[hy0]`. Rewrite using `[dif_neg h2, hdy0, hs'e]`. Simplify using `[Lop, hy0]`.
-/
private theorem Dtot_Lop_eq_zero_of_Dtot_eq_zero_of_empty_eq_zero (p : ℕ) (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V)
    (h : ι → ι → V →+ K) (hd : IsOddDer d) (hD : IsDatum p d f h) (v : V)
    (y : Finset ι → ExteriorAlgebra K V) (hy : Dtot d y = 0) (hy0 : y ∅ = 0) :
    Dtot d (Lop f h v y) = 0 := by
  have hys : ∀ s : Finset ι, d (y s) = -((-1 : ℤ) ^ s.card • delta y s) := by
    intro s
    have e0 := congrFun hy s
    simp only [Dtot, Pi.zero_apply] at e0
    have e2 : (-1 : ℤ) ^ s.card • d (y s) = -delta y s := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact e0
    have e1 : ((-1 : ℤ) ^ s.card * (-1) ^ s.card) = 1 := by
      rw [← mul_pow]
      simp
    calc d (y s) = ((-1 : ℤ) ^ s.card * (-1) ^ s.card) • d (y s) := by rw [e1, one_smul]
      _ = (-1 : ℤ) ^ s.card • ((-1 : ℤ) ^ s.card • d (y s)) := mul_smul _ _ _
      _ = -((-1 : ℤ) ^ s.card • delta y s) := by rw [e2, smul_neg]
  have dsm : ∀ (k : K) (x : ExteriorAlgebra K V), d (k • x) = d (algebraMap K _ k) * x + k • d x := by
    intro k x
    rw [Algebra.smul_def, hd.mul, AlgHom.commutes, ← Algebra.smul_def]
  have dω : ∀ (i : ι) (x : ExteriorAlgebra K V),
      d (ExteriorAlgebra.ι K (f i v) * x) = -(ExteriorAlgebra.ι K (f i v) * d x) := by
    intro i x
    rw [hd.mul, hD.closed, zero_mul, zero_add]
    rw [show CliffordAlgebra.involute (ExteriorAlgebra.ι K (f i v)) = -ExteriorAlgebra.ι K (f i v) from
      CliffordAlgebra.involute_ι _, neg_mul]
  have hε : ∀ (n : ℕ) (x : ExteriorAlgebra K V), (-1 : ℤ) ^ n • ((-1 : ℤ) ^ n • x) = x := by
    intro n x
    rw [← mul_smul, ← mul_pow]
    simp
  funext s
  simp only [Dtot, Pi.zero_apply]
  by_cases hs : s.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp [delta, Lop]
  · rw [delta_eq_erase_min_sub_sum_cubeSign _ s hs]
    have hdy := delta_eq_erase_min_sub_sum_cubeSign y s hs
    set m := s.min' hs
    set s' := s.erase m
    have hms : m ∈ s := s.min'_mem hs
    have hLs := Lop_apply_of_min_eq f h v y s m hs rfl
    have hLi : ∀ i ∈ s', Lop f h v y (s.erase i) =
        -((-1 : ℤ) ^ s.card • (ExteriorAlgebra.ι K (f m v) * y (s.erase i))) +
        (if h2 : (s'.erase i).Nonempty then h m ((s'.erase i).min' h2) v • y (s'.erase i) else 0) := by
      intro i hi
      have hne : i ≠ m := Finset.ne_of_mem_erase hi
      have his : i ∈ s := Finset.mem_of_mem_erase hi
      have hmi : m ∈ s.erase i := Finset.mem_erase.mpr ⟨hne.symm, hms⟩
      have hmin : (s.erase i).min' ⟨m, hmi⟩ = m :=
        le_antisymm ((s.erase i).min'_le m hmi)
          (Finset.le_min' _ _ _ (fun z hz => s.min'_le z (Finset.mem_of_mem_erase hz)))
      rw [Lop_apply_of_min_eq f h v y (s.erase i) m ⟨m, hmi⟩ hmin, neg_one_pow_card_erase_of_mem s i his, neg_smul,
        Finset.erase_right_comm]
    have hsum : ∑ i ∈ s', GlobalTheory.cubeSign s' i • Lop f h v y (s.erase i) =
        -((-1 : ℤ) ^ s.card • (ExteriorAlgebra.ι K (f m v) * ∑ i ∈ s', GlobalTheory.cubeSign s' i • y (s.erase i))) +
        ∑ i ∈ s', GlobalTheory.cubeSign s' i •
          (if h2 : (s'.erase i).Nonempty then h m ((s'.erase i).min' h2) v • y (s'.erase i) else 0) := by
      rw [Finset.mul_sum, Finset.smul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hLi i hi, smul_add, smul_neg, mul_smul_comm, smul_comm (GlobalTheory.cubeSign s' i)]
    have hX : ∑ i ∈ s', GlobalTheory.cubeSign s' i • y (s.erase i) = y s' - delta y s := by
      rw [hdy]
      abel
    have hLs2 : Lop f h v y s = (-1 : ℤ) ^ s.card • (ExteriorAlgebra.ι K (f m v) * y s) +
        (if h2 : s'.Nonempty then h m (s'.min' h2) v • y s' else 0) := hLs
    rw [hsum, hLs2, hX, map_add, map_zsmul, dω, hys s]
    by_cases h2 : s'.Nonempty
    · set n := s'.min' h2 with hn_eq
      have hns : n ∈ s' := s'.min'_mem h2
      have hLs' : Lop f h v y s' = (-1 : ℤ) ^ s'.card • (ExteriorAlgebra.ι K (f n v) * y s') +
          (if h3 : (s'.erase n).Nonempty then h n ((s'.erase n).min' h3) v • y (s'.erase n) else 0) :=
        Lop_apply_of_min_eq f h v y s' n h2 rfl
      have hc : (-1 : ℤ) ^ s'.card = -(-1) ^ s.card := neg_one_pow_card_erase_of_mem s m hms
      have hSh : ∑ i ∈ s', GlobalTheory.cubeSign s' i •
          (if h3 : (s'.erase i).Nonempty then h m ((s'.erase i).min' h3) v • y (s'.erase i) else 0) =
          (if h3 : (s'.erase n).Nonempty then h n ((s'.erase n).min' h3) v • y (s'.erase n) else 0) +
            h m n v • delta y s' := by
        rw [← sub_eq_iff_eq_add]
        unfold delta
        rw [Finset.smul_sum, ← Finset.sum_sub_distrib, Finset.sum_eq_single n]
        · rw [show GlobalTheory.cubeSign s' n = 1 from cubeSign_min_eq_one s' h2]
          simp only [one_smul]
          by_cases h3 : (s'.erase n).Nonempty
          · rw [dif_pos h3, dif_pos h3, ← sub_smul]
            congr 1
            rw [← hD.cocycle m n ((s'.erase n).min' h3) v]
            ring
          · rw [dif_neg h3, dif_neg h3, Finset.not_nonempty_iff_eq_empty.mp h3, hy0]
            simp
        · intro b hb hbn
          have hnb : n ∈ s'.erase b := Finset.mem_erase.mpr ⟨fun e => hbn e.symm, hns⟩
          have hmin : (s'.erase b).min' ⟨n, hnb⟩ = n :=
            le_antisymm ((s'.erase b).min'_le n hnb)
              (Finset.le_min' _ _ _ (fun z hz => s'.min'_le z (Finset.mem_of_mem_erase hz)))
          rw [dif_pos ⟨n, hnb⟩, hmin, smul_comm (h m n v) (GlobalTheory.cubeSign s' b), sub_self]
        · intro hn
          exact absurd hns hn
      have hcomm : ∀ x : ExteriorAlgebra K V,
          h m n v • ((-1 : ℤ) ^ s.card • x) = (-1 : ℤ) ^ s.card • (h m n v • x) :=
        fun x => smul_comm _ _ _
      rw [dif_pos h2, ← hn_eq, hSh, hLs', dsm, hD.dh, hys s', hc]
      simp only [neg_smul, smul_neg, neg_neg, mul_neg, mul_sub, sub_mul, smul_add, smul_sub,
        mul_smul_comm, hε, hcomm]
      abel
    · have hs'e : s' = ∅ := Finset.not_nonempty_iff_eq_empty.mp h2
      have hdy0 : delta y s = 0 := by
        rw [hdy, hs'e]
        simp [hy0]
      rw [dif_neg h2, hdy0, hs'e]
      simp [Lop, hy0]

/- English proof (translation)
Proceed by induction on `vs with`. Consider the case `nil => exact ⟨dtot_oneC d hd, oneC_empty (ι := ι)⟩`. Consider the case `cons v vs ih`. Take `⟨h1, h2⟩` from `ih`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Conclude with `Dtot_Lop_eq_zero_of_Dtot_eq_zero_of_empty_eq_zero p d f h hd hD v _ h1 h2`. Simplify using `[prodL, Lop]`.
-/
theorem prodL_closed (p : ℕ) (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V)
    (h : ι → ι → V →+ K) (hd : IsOddDer d) (hD : IsDatum p d f h) (vs : List V) :
    Dtot d (prodL f h vs) = 0 ∧ prodL f h vs ∅ = 0 := by
  induction vs with
  | nil => exact ⟨dtot_oneC d hd, oneC_empty (ι := ι)⟩
  | cons v vs ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · exact Dtot_Lop_eq_zero_of_Dtot_eq_zero_of_empty_eq_zero p d f h hd hD v _ h1 h2
    · simp [prodL, Lop]

/- English proof (translation)
Establish `hp` using `fun vs => prodL_closed p d f h hd hD vs`. Prove the components needed by the constructor for the conclusion. Express the relevant statement in the definitionally equal form `dtotHom d (alt f h a v) = 0`. Unfold `alt`. Rewrite using `[map_sum]`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `σ _`. Rewrite using `[map_zsmul]`. Express the relevant statement in the definitionally equal form `_ • Dtot d _ = 0`. Rewrite using `[(hp _).1, smul_zero]`.

Simplify using `only [alt, Finset.sum_apply, Pi.smul_apply, (hp _).2, smul_zero, Finset.sum_const_zero]`.
-/
theorem alt_closed (p : ℕ) (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V)
    (h : ι → ι → V →+ K) (hd : IsOddDer d) (hD : IsDatum p d f h) (a : ℕ) (v : Fin a → V) :
    Dtot d (alt f h a v) = 0 ∧ alt f h a v ∅ = 0 := by
  have hp := fun vs => prodL_closed p d f h hd hD vs
  constructor
  · change dtotHom d (alt f h a v) = 0
    unfold alt
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro σ _
    rw [map_zsmul]
    change _ • Dtot d _ = 0
    rw [(hp _).1, smul_zero]
  · simp only [alt, Finset.sum_apply, Pi.smul_apply, (hp _).2, smul_zero, Finset.sum_const_zero]

end GlobalTheory.DI.AltClosed

/- English proof (translation)
Introduce `K _ V _ _ ι _ p d f h hd hD`. Conclude with `⟨fun vs => AltClosed.prodL_closed p d f h hd hD vs, fun a v => AltClosed.alt_closed p d f h hd hD a v⟩`.
-/
theorem GlobalTheory.DI.prodL_alt_closed : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V) (h : ι → ι → V →+ K), IsOddDer d → IsDatum p d f h → (∀ vs : List V, Dtot d (prodL f h vs) = 0 ∧ prodL f h vs ∅ = 0) ∧ ∀ (a : ℕ) (v : Fin a → V), Dtot d (alt f h a v) = 0 ∧ alt f h a v ∅ = 0 := by
  intro K _ V _ _ ι _ p d f h hd hD
  exact ⟨fun vs => AltClosed.prodL_closed p d f h hd hD vs,
    fun a v => AltClosed.alt_closed p d f h hd hD a v⟩
