import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.TwiceValuationFactorialProduct
import Formalism.PolynomialDimension.FinalNum

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

section Letters

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r)

/- English proof (translation)
Unfold `llPos`. Establish `hlen : l < ((Fr.LLset j).sort (· ≤ ·)).length` using `by rw [Finset.length_sort]; exact hl`. Rewrite using `[List.getD_eq_getElem _ _ hlen]`. Conclude with `(Finset.mem_sort _).mp (List.getElem_mem hlen)`.
-/
theorem llPos_mem (j : ℤ) (l : ℕ) (hl : l < (Fr.LLset j).card) : llPos Fr j l ∈ Fr.LLset j := by
  unfold llPos
  have hlen : l < ((Fr.LLset j).sort (· ≤ ·)).length := by rw [Finset.length_sort]; exact hl
  rw [List.getD_eq_getElem _ _ hlen]
  exact (Finset.mem_sort _).mp (List.getElem_mem hlen)

/- English proof (translation)
Unfold `llPos at h`. Establish `h1 : l < ((Fr.LLset j).sort (· ≤ ·)).length` using `by rw [Finset.length_sort]; exact hl`. Establish `h2 : l' < ((Fr.LLset j).sort (· ≤ ·)).length` using `by rw [Finset.length_sort]; exact hl'`. Rewrite `h` using `[List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2]`. Conclude with `(List.Nodup.getElem_inj_iff (Finset.sort_nodup _ _)).mp h`.
-/
theorem llPos_inj (j : ℤ) (l l' : ℕ) (hl : l < (Fr.LLset j).card) (hl' : l' < (Fr.LLset j).card)
    (h : llPos Fr j l = llPos Fr j l') : l = l' := by
  unfold llPos at h
  have h1 : l < ((Fr.LLset j).sort (· ≤ ·)).length := by rw [Finset.length_sort]; exact hl
  have h2 : l' < ((Fr.LLset j).sort (· ≤ ·)).length := by rw [Finset.length_sort]; exact hl'
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at h
  exact (List.Nodup.getElem_inj_iff (Finset.sort_nodup _ _)).mp h

/- English proof (translation)
Simplify using `[Frames.LLset, Finset.mem_Ioo]`.
-/
theorem mem_LLset (j x : ℤ) : x ∈ Fr.LLset j ↔
    (Fr.fr (j - 1) (r - 1) < x ∧ x < Fr.fr j 0) ∧ posOf n' x ∈ Fr.TT := by
  simp [Frames.LLset, Finset.mem_Ioo]

variable {L₁ N₁ : ℕ} {J : ℕ} [NeZero J] {nL : ZMod J → ℕ}

/- English proof (translation)
Introduce `i i' hii' hi'`. Proceed by induction on `i' with`. Consider the case `zero => rw [Nat.le_zero.mp hii']`. Consider the case `succ k ih`. Break down `Nat.lt_or_ge i (k + 1) with h | h` into its components or cases.

Conclude with `le_trans (ih (by omega) (by omega)) (hV.2.2.1 j k (by omega)).le`. Rewrite using `[le_antisymm hii' h]`.
-/
private theorem fr_mono_of_valid (hV : Fr.Valid L₁ N₁) (j : ℤ) :
    ∀ i i' : ℕ, i ≤ i' → i' < r → Fr.fr j i ≤ Fr.fr j i' := by
  intro i i' hii' hi'
  induction i' with
  | zero => rw [Nat.le_zero.mp hii']
  | succ k ih =>
    rcases Nat.lt_or_ge i (k + 1) with h | h
    · exact le_trans (ih (by omega) (by omega)) (hV.2.2.1 j k (by omega)).le
    · rw [le_antisymm hii' h]

/- English proof (translation)
Introduce `b hab`. Proceed by induction on `b, hab using Int.le_induction with`. Consider the case `base => exact le_rfl`. Consider the case `succ k _ ih`. Conclude with `le_trans ih (le_trans (hV.2.2.2.1 k).le (fr_mono_of_valid Fr hV (k + 1) 0 (r - 1) (Nat.zero_le _) (by omega)))`.
-/
private theorem fr_last_mono_in_index_of_valid (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (a : ℤ) :
    ∀ b : ℤ, a ≤ b → Fr.fr a (r - 1) ≤ Fr.fr b (r - 1) := by
  intro b hab
  induction b, hab using Int.le_induction with
  | base => exact le_rfl
  | succ k _ ih =>
    exact le_trans ih (le_trans (hV.2.2.2.1 k).le
      (fr_mono_of_valid Fr hV (k + 1) 0 (r - 1) (Nat.zero_le _) (by omega)))

/- English proof (translation)
Take `⟨j, l | m⟩` from `x`. Establish `hl : l.val < (Fr.LLset (segZ j)).card` using `by rw [← hnL j]; exact l.2`. Establish `hm` using `llPos_mem Fr (segZ j) l.val hl`. Rewrite `hm` using `[mem_LLset]`. Use `⟨hm.1.1, ?_, hm.2⟩` and prove the remaining obligations.

Conclude with `le_trans hm.1.2.le (fr_mono_of_valid Fr hV _ 0 (r - 1) (Nat.zero_le _) (by omega))`. Use `⟨?_, ?_, (hV.2.2.2.2.1 _ _ (by omega)).1⟩` and prove the remaining obligations. Establish `h1` using `hV.2.2.2.1 (segZ j - 1)`. Rewrite `h1` using `[sub_add_cancel]`. Conclude with `lt_of_lt_of_le h1 (fr_mono_of_valid Fr hV _ 0 _ (Nat.zero_le _) (by omega))`.

Conclude with `fr_mono_of_valid Fr hV _ _ _ (by omega) (by omega)`.
-/
theorem posTL_seg (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (x : TL J nL r) :
    Fr.fr (segZ x.1 - 1) (r - 1) < posTL Fr x ∧ posTL Fr x ≤ Fr.fr (segZ x.1) (r - 1) ∧
      posOf n' (posTL Fr x) ∈ Fr.TT := by
  obtain ⟨j, l | m⟩ := x
  · have hl : l.val < (Fr.LLset (segZ j)).card := by rw [← hnL j]; exact l.2
    have hm := llPos_mem Fr (segZ j) l.val hl
    rw [mem_LLset] at hm
    refine ⟨hm.1.1, ?_, hm.2⟩
    exact le_trans hm.1.2.le (fr_mono_of_valid Fr hV _ 0 (r - 1) (Nat.zero_le _) (by omega))
  · refine ⟨?_, ?_, (hV.2.2.2.2.1 _ _ (by omega)).1⟩
    · have h1 := hV.2.2.2.1 (segZ j - 1)
      rw [sub_add_cancel] at h1
      exact lt_of_lt_of_le h1 (fr_mono_of_valid Fr hV _ 0 _ (Nat.zero_le _) (by omega))
    · exact fr_mono_of_valid Fr hV _ _ _ (by omega) (by omega)

/- English proof (translation)
Conclude with `Int.natCast_nonneg _`.
-/
theorem segZ_nonneg (j : ZMod J) : 0 ≤ segZ j := by
  exact Int.natCast_nonneg _

/- English proof (translation)
Unfold `segZ`. Conclude with `ZMod.val_lt j` after adjusting the coercions.
-/
theorem segZ_lt (j : ZMod J) : segZ j < J := by
  unfold segZ
  exact_mod_cast ZMod.val_lt j

/- English proof (translation)
Establish `hs` using `posTL_seg Fr hV hr hnL x`. Establish `hj0` using `segZ_nonneg x.1`. Establish `hjJ : segZ x.1 < J` using `segZ_lt x.1`. Establish `hper` using `hV.2.1 (-1) (r - 1)`. Prove the components needed by the constructor for the conclusion.

Use `fr_last_mono_in_index_of_valid Fr hV hr (-1) (segZ x.1 - 1) (by omega)` as an intermediate fact. Combine the linear relations using `[hs.1]`. Establish `h2` using `fr_last_mono_in_index_of_valid Fr hV hr (segZ x.1) (-1 + Fr.J) (by rw [← hJ]; omega)`. Rewrite `h2` using `[hper]`. Combine the linear relations using `[hs.2.1]`.
-/
theorem posTL_win (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card)
    (x : TL J nL r) :
    Fr.fr (-1) (r - 1) + 1 ≤ posTL Fr x ∧ posTL Fr x < Fr.fr (-1) (r - 1) + 1 + n' := by
  have hs := posTL_seg Fr hV hr hnL x
  have hj0 := segZ_nonneg x.1
  have hjJ : segZ x.1 < J := segZ_lt x.1
  have hper := hV.2.1 (-1) (r - 1)
  constructor
  · have := fr_last_mono_in_index_of_valid Fr hV hr (-1) (segZ x.1 - 1) (by omega)
    linarith [hs.1]
  · have h2 := fr_last_mono_in_index_of_valid Fr hV hr (segZ x.1) (-1 + Fr.J) (by rw [← hJ]; omega)
    rw [hper] at h2
    linarith [hs.2.1]

/- English proof (translation)
Establish `hpos : Function.Injective fun x : TL J nL r => posTL Fr x`. Introduce `x y hxy`. Simplify using `only at hxy`. Establish `hsx` using `posTL_seg Fr hV hr hnL x`. Establish `hsy` using `posTL_seg Fr hV hr hnL y`.

Establish `hseg : segZ x.1 = segZ y.1`. Assume the negation of the conclusion as `hne`. Break down `lt_or_gt_of_ne hne with h | h` into its components or cases. Use `fr_last_mono_in_index_of_valid Fr hV hr (segZ x.1) (segZ y.1 - 1) (by omega)` as an intermediate fact. Combine the linear relations using `[hsx.2.1, hsy.1]`.

Use `fr_last_mono_in_index_of_valid Fr hV hr (segZ y.1) (segZ x.1 - 1) (by omega)` as an intermediate fact. Combine the linear relations using `[hsy.2.1, hsx.1]`. Establish `hj : x.1 = y.1`. Unfold `segZ at hseg`. Conclude with `ZMod.val_injective _ (by exact_mod_cast hseg)`.

Take `⟨j, a⟩` from `x`. Take `⟨j', b⟩` from `y`. Simplify using `only at hj`. Substitute `hj` using the available equality. Apply the tactic sequence `rcases a with l | m <;> rcases b with l' | m'`.

Establish `hl : l.val < (Fr.LLset (segZ j)).card` using `by rw [← hnL j]; exact l.2`. Establish `hl' : l'.val < (Fr.LLset (segZ j)).card` using `by rw [← hnL j]; exact l'.2`. Use `llPos_inj Fr (segZ j) l.val l'.val hl hl' hxy` as an intermediate fact. Rewrite `this` using `[Fin.val_eq_val]`. Rewrite using `[this]`.

It suffices to derive a contradiction. Establish `hl : l.val < (Fr.LLset (segZ j)).card` using `by rw [← hnL j]; exact l.2`. Establish `hm` using `llPos_mem Fr (segZ j) l.val hl`. Rewrite `hm` using `[mem_LLset]`. Establish `h2` using `fr_mono_of_valid Fr hV (segZ j) 0 (r - 1 - m'.val) (Nat.zero_le _) (by omega)`.

Establish `h3 : llPos Fr (segZ j) l.val = Fr.fr (segZ j) (r - 1 - m'.val)` using `hxy`. Combine the linear relations using `[hm.1.2]`. It suffices to derive a contradiction. Establish `hl : l'.val < (Fr.LLset (segZ j)).card` using `by rw [← hnL j]; exact l'.2`. Establish `hm` using `llPos_mem Fr (segZ j) l'.val hl`.

Rewrite `hm` using `[mem_LLset]`. Establish `h2` using `fr_mono_of_valid Fr hV (segZ j) 0 (r - 1 - m.val) (Nat.zero_le _) (by omega)`. Establish `h3 : Fr.fr (segZ j) (r - 1 - m.val) = llPos Fr (segZ j) l'.val` using `hxy`. Combine the linear relations using `[hm.1.2]`. Establish `h3 : Fr.fr (segZ j) (r - 1 - m.val) = Fr.fr (segZ j) (r - 1 - m'.val)` using `hxy`.

Establish `hmm : m.val = m'.val`. Assume the negation of the conclusion as `hne`. Establish `hm1` using `m.2`. Establish `hm2` using `m'.2`. Break down `Nat.lt_or_gt_of_ne hne with h | h` into its components or cases.

Use `fr_mono_of_valid Fr hV (segZ j) (r - 1 - m'.val + 1) (r - 1 - m.val) (by omega) (by omega)` as an intermediate fact. Use `hV.2.2.1 (segZ j) (r - 1 - m'.val) (by omega)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `fr_mono_of_valid Fr hV (segZ j) (r - 1 - m.val + 1) (r - 1 - m'.val) (by omega) (by omega)` as an intermediate fact. Use `hV.2.2.1 (segZ j) (r - 1 - m.val) (by omega)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `hmm` using `[Fin.val_eq_val]`. Rewrite using `[hmm]`. Introduce `x y hxy`. Apply `hpos` to reduce the goal to its premises.

Simplify using `only at hxy ⊢`. Establish `wx` using `posTL_win Fr hV hr hJ hnL x`. Establish `wy` using `posTL_win Fr hV hr hJ hnL y`. Establish `hn0 : (0 : ℤ) < n'` using `by exact_mod_cast NeZero.pos n'`. Establish `hv : ((posTL Fr x % (n' : ℤ)).toNat % n') = ((posTL Fr y % (n' : ℤ)).toNat % n')` using `congrArg Fin.val hxy`.

Establish `ex1 : 0 ≤ posTL Fr x % (n' : ℤ)` using `Int.emod_nonneg _ hn0.ne'`. Establish `ex2 : posTL Fr x % (n' : ℤ) < n'` using `Int.emod_lt_of_pos _ hn0`. Establish `ey1 : 0 ≤ posTL Fr y % (n' : ℤ)` using `Int.emod_nonneg _ hn0.ne'`. Establish `ey2 : posTL Fr y % (n' : ℤ) < n'` using `Int.emod_lt_of_pos _ hn0`. Establish `hmod : posTL Fr x % (n' : ℤ) = posTL Fr y % (n' : ℤ)`.

Rewrite `hv` using `[Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]`. Use linear arithmetic over natural numbers and integers. Establish `hdvd : (n' : ℤ) ∣ posTL Fr x - posTL Fr y` using `Int.dvd_of_emod_eq_zero (Int.emod_emod_of_dvd _ (dvd_refl _) ▸ (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hmod))`. Establish `habs : |posTL Fr x - posTL Fr y| < n'`. Apply the tactic sequence `rw [abs_lt]; constructor <;> linarith [wx.1, wx.2, wy.1, wy.2]`.

Use `Int.eq_zero_of_abs_lt_dvd hdvd habs` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem posTL_inj (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) :
    Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x) := by
  have hpos : Function.Injective fun x : TL J nL r => posTL Fr x := by
    intro x y hxy
    simp only at hxy
    have hsx := posTL_seg Fr hV hr hnL x
    have hsy := posTL_seg Fr hV hr hnL y
    have hseg : segZ x.1 = segZ y.1 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have := fr_last_mono_in_index_of_valid Fr hV hr (segZ x.1) (segZ y.1 - 1) (by omega)
        linarith [hsx.2.1, hsy.1]
      · have := fr_last_mono_in_index_of_valid Fr hV hr (segZ y.1) (segZ x.1 - 1) (by omega)
        linarith [hsy.2.1, hsx.1]
    have hj : x.1 = y.1 := by
      unfold segZ at hseg
      exact ZMod.val_injective _ (by exact_mod_cast hseg)
    obtain ⟨j, a⟩ := x
    obtain ⟨j', b⟩ := y
    simp only at hj
    subst hj
    rcases a with l | m <;> rcases b with l' | m'
    · have hl : l.val < (Fr.LLset (segZ j)).card := by rw [← hnL j]; exact l.2
      have hl' : l'.val < (Fr.LLset (segZ j)).card := by rw [← hnL j]; exact l'.2
      have := llPos_inj Fr (segZ j) l.val l'.val hl hl' hxy
      rw [Fin.val_eq_val] at this
      rw [this]
    · exfalso
      have hl : l.val < (Fr.LLset (segZ j)).card := by rw [← hnL j]; exact l.2
      have hm := llPos_mem Fr (segZ j) l.val hl
      rw [mem_LLset] at hm
      have h2 := fr_mono_of_valid Fr hV (segZ j) 0 (r - 1 - m'.val) (Nat.zero_le _) (by omega)
      have h3 : llPos Fr (segZ j) l.val = Fr.fr (segZ j) (r - 1 - m'.val) := hxy
      linarith [hm.1.2]
    · exfalso
      have hl : l'.val < (Fr.LLset (segZ j)).card := by rw [← hnL j]; exact l'.2
      have hm := llPos_mem Fr (segZ j) l'.val hl
      rw [mem_LLset] at hm
      have h2 := fr_mono_of_valid Fr hV (segZ j) 0 (r - 1 - m.val) (Nat.zero_le _) (by omega)
      have h3 : Fr.fr (segZ j) (r - 1 - m.val) = llPos Fr (segZ j) l'.val := hxy
      linarith [hm.1.2]
    · have h3 : Fr.fr (segZ j) (r - 1 - m.val) = Fr.fr (segZ j) (r - 1 - m'.val) := hxy
      have hmm : m.val = m'.val := by
        by_contra hne
        have hm1 := m.2
        have hm2 := m'.2
        rcases Nat.lt_or_gt_of_ne hne with h | h
        · have := fr_mono_of_valid Fr hV (segZ j) (r - 1 - m'.val + 1) (r - 1 - m.val) (by omega) (by omega)
          have := hV.2.2.1 (segZ j) (r - 1 - m'.val) (by omega)
          linarith
        · have := fr_mono_of_valid Fr hV (segZ j) (r - 1 - m.val + 1) (r - 1 - m'.val) (by omega) (by omega)
          have := hV.2.2.1 (segZ j) (r - 1 - m.val) (by omega)
          linarith
      rw [Fin.val_eq_val] at hmm
      rw [hmm]
  intro x y hxy
  apply hpos
  simp only at hxy ⊢
  have wx := posTL_win Fr hV hr hJ hnL x
  have wy := posTL_win Fr hV hr hJ hnL y
  have hn0 : (0 : ℤ) < n' := by exact_mod_cast NeZero.pos n'
  have hv : ((posTL Fr x % (n' : ℤ)).toNat % n') = ((posTL Fr y % (n' : ℤ)).toNat % n') :=
    congrArg Fin.val hxy
  have ex1 : 0 ≤ posTL Fr x % (n' : ℤ) := Int.emod_nonneg _ hn0.ne'
  have ex2 : posTL Fr x % (n' : ℤ) < n' := Int.emod_lt_of_pos _ hn0
  have ey1 : 0 ≤ posTL Fr y % (n' : ℤ) := Int.emod_nonneg _ hn0.ne'
  have ey2 : posTL Fr y % (n' : ℤ) < n' := Int.emod_lt_of_pos _ hn0
  have hmod : posTL Fr x % (n' : ℤ) = posTL Fr y % (n' : ℤ) := by
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv
    omega
  have hdvd : (n' : ℤ) ∣ posTL Fr x - posTL Fr y :=
    Int.dvd_of_emod_eq_zero (Int.emod_emod_of_dvd _ (dvd_refl _) ▸ (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hmod))
  have habs : |posTL Fr x - posTL Fr y| < n' := by
    rw [abs_lt]; constructor <;> linarith [wx.1, wx.2, wy.1, wy.2]
  have := Int.eq_zero_of_abs_lt_dvd hdvd habs
  linarith

/- English proof (translation)
Establish `hinj` using `posTL_inj Fr hV hr hJ hnL`. Combine the equalities or inequalities in the displayed calculation. Introduce `y hy`. Take `⟨x, -, rfl⟩` from `Finset.mem_image.mp hy`. Conclude with `(posTL_seg Fr hV hr hnL x).2.2)`.
-/
theorem card_TL_le (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) :
    Fintype.card (TL J nL r) ≤ Fr.TT.card := by
  classical
  have hinj := posTL_inj Fr hV hr hJ hnL
  calc Fintype.card (TL J nL r)
      = (Finset.univ.image fun x : TL J nL r => posOf n' (posTL Fr x)).card :=
        (Finset.card_image_of_injective _ hinj).symm
    _ ≤ Fr.TT.card := Finset.card_le_card (by
        intro y hy
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy
        exact (posTL_seg Fr hV hr hnL x).2.2)

/- English proof (translation)
Simplify using `[TL, Fintype.card_sigma, Fintype.card_sum]`.
-/
theorem card_TL_eq : Fintype.card (TL J nL r) = ∑ j : ZMod J, (nL j + r) := by
  simp [TL, Fintype.card_sigma, Fintype.card_sum]

end Letters

section Reals

/- English proof (translation)
Establish `o` using `fun (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) => one_le_mul_of_one_le_of_one_le ha hb`. Establish `hA : 1 ≤ u1 * u3 * u5 * u6 * u7` using `o _ _ (o _ _ (o _ _ (o _ _ h1 h3) h5) h6) h7`. Establish `hB : 1 ≤ u1 * u2 * u4 * u5 * u6 * u7` using `o _ _ (o _ _ (o _ _ (o _ _ (o _ _ h1 h2) h4) h5) h6) h7`. Establish `hC : 1 ≤ u1 * u2 * u3 * u4 * u6 * u7` using `o _ _ (o _ _ (o _ _ (o _ _ (o _ _ h1 h2) h3) h4) h6) h7`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem factor_le_product_seven (u1 u2 u3 u4 u5 u6 u7 : ℝ) (h1 : 1 ≤ u1) (h2 : 1 ≤ u2) (h3 : 1 ≤ u3) (h4 : 1 ≤ u4) (h5 : 1 ≤ u5)
    (h6 : 1 ≤ u6) (h7 : 1 ≤ u7) :
    u2 * u4 ≤ u1 * u2 * u3 * u4 * u5 * u6 * u7 ∧ u3 ≤ u1 * u2 * u3 * u4 * u5 * u6 * u7 ∧
      u5 ≤ u1 * u2 * u3 * u4 * u5 * u6 * u7 := by
  have o := fun (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) => one_le_mul_of_one_le_of_one_le ha hb
  have hA : 1 ≤ u1 * u3 * u5 * u6 * u7 := o _ _ (o _ _ (o _ _ (o _ _ h1 h3) h5) h6) h7
  have hB : 1 ≤ u1 * u2 * u4 * u5 * u6 * u7 := o _ _ (o _ _ (o _ _ (o _ _ (o _ _ h1 h2) h4) h5) h6) h7
  have hC : 1 ≤ u1 * u2 * u3 * u4 * u6 * u7 := o _ _ (o _ _ (o _ _ (o _ _ (o _ _ h1 h2) h3) h4) h6) h7
  refine ⟨?_, ?_, ?_⟩
  · calc u2 * u4 ≤ u2 * u4 * (u1 * u3 * u5 * u6 * u7) :=
          le_mul_of_one_le_right (mul_nonneg (by linarith) (by linarith)) hA
      _ = u1 * u2 * u3 * u4 * u5 * u6 * u7 := by ring
  · calc u3 ≤ u3 * (u1 * u2 * u4 * u5 * u6 * u7) := le_mul_of_one_le_right (by linarith) hB
      _ = u1 * u2 * u3 * u4 * u5 * u6 * u7 := by ring
  · calc u5 ≤ u5 * (u1 * u2 * u3 * u4 * u6 * u7) := le_mul_of_one_le_right (by linarith) hC
      _ = u1 * u2 * u3 * u4 * u5 * u6 * u7 := by ring

/- English proof (translation)
Unfold `lg`. Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast hp`. Establish `hr1 : (1 : ℝ) ≤ r` using `by exact_mod_cast hr`. Establish `hn0 : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Establish `hpos : (0 : ℝ) < (n : ℝ) + r` using `by linarith`.

Establish `ha : (0 : ℝ) < a` using `by linarith`. Establish `h1 : Real.logb p ((n : ℝ) + r) ≤ Real.logb p (a ^ 3)` using `Real.logb_le_logb_of_le hp1 hpos hn`. Establish `h2 : Real.logb p (a ^ 3) = 3 * Real.logb p a`. Rewrite using `[show a ^ 3 = a ^ (3 : ℝ) by norm_cast, Real.logb_rpow_eq_mul_logb_of_pos ha]`. Establish `h3 : 1 ≤ Real.logb p a`.

Rewrite using `[← Real.logb_self_eq_one hp1]`. Conclude with `Real.logb_le_logb_of_le hp1 (by linarith) hpa`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lg_le_four (p r n : ℕ) (a : ℝ) (hp : 2 ≤ p) (hr : 1 ≤ r) (hpa : (p : ℝ) ≤ a) (hn : (n : ℝ) + r ≤ a ^ 3) :
    lg p r n ≤ 4 * Real.logb p a := by
  unfold lg
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpos : (0 : ℝ) < (n : ℝ) + r := by linarith
  have ha : (0 : ℝ) < a := by linarith
  have h1 : Real.logb p ((n : ℝ) + r) ≤ Real.logb p (a ^ 3) := Real.logb_le_logb_of_le hp1 hpos hn
  have h2 : Real.logb p (a ^ 3) = 3 * Real.logb p a := by
    rw [show a ^ 3 = a ^ (3 : ℝ) by norm_cast, Real.logb_rpow_eq_mul_logb_of_pos ha]
  have h3 : 1 ≤ Real.logb p a := by
    rw [← Real.logb_self_eq_one hp1]
    exact Real.logb_le_logb_of_le hp1 (by linarith) hpa
  linarith

/- English proof (translation)
Unfold `lg`. Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast hp`. Establish `hx : (1 : ℝ) ≤ (n : ℝ) + r`. Establish `: (1 : ℝ) ≤ r` using `by exact_mod_cast hr`. Establish `: (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `Real.logb_nonneg hp1 hx` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lg_nonneg (p r n : ℕ) (hp : 2 ≤ p) (hr : 1 ≤ r) : 0 ≤ lg p r n := by
  unfold lg
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hx : (1 : ℝ) ≤ (n : ℝ) + r := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have := Real.logb_nonneg hp1 hx
  linarith

/- English proof (translation)
Establish `hs : Summable (fun k : ℕ => q ^ k)` using `summable_geometric_of_lt_one h0 h1`. Rewrite using `[← Finset.sum_image (f := fun k : ℕ => q ^ k) (s := Finset.univ) (g := t) (fun i _ j _ h => ht h)]`. Rewrite using `[← tsum_geometric_of_lt_one h0 h1]`. Use `first`. Consider the case `exact hs.sum_le_tsum _ (fun i _ => pow_nonneg h0 i)`.

Consider the case `exact sum_le_tsum _ (fun i _ => pow_nonneg h0 i) hs`.
-/
theorem geom_inj_le {ι : Type} [Fintype ι] (t : ι → ℕ) (ht : Function.Injective t) (q : ℝ) (h0 : 0 ≤ q) (h1 : q < 1) :
    ∑ i, q ^ t i ≤ (1 - q)⁻¹ := by
  classical
  have hs : Summable (fun k : ℕ => q ^ k) := summable_geometric_of_lt_one h0 h1
  rw [← Finset.sum_image (f := fun k : ℕ => q ^ k) (s := Finset.univ) (g := t)
    (fun i _ j _ h => ht h)]
  rw [← tsum_geometric_of_lt_one h0 h1]
  first
    | exact hs.sum_le_tsum _ (fun i _ => pow_nonneg h0 i)
    | exact sum_le_tsum _ (fun i _ => pow_nonneg h0 i) hs

end Reals

section Sizes

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ} [NeZero J]

/- English proof (translation)
Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast hp`. Establish `hrR : (1 : ℝ) ≤ r` using `by exact_mod_cast hr`. Establish `hrkR : (r : ℝ) ≤ k` using `by exact_mod_cast hrk`. Establish `hk1 : (1 : ℝ) ≤ k` using `le_trans hrR hrkR`. Establish `hL1 : 1 ≤ Real.logb p a`.

Rewrite using `[← Real.logb_self_eq_one hp1]`. Conclude with `Real.logb_le_logb_of_le hp1 (by linarith) hpa`. Establish `hcardR : (Fintype.card (TL J Dt.nL r) : ℝ) ≤ N` using `by exact_mod_cast hcard`. Establish `hN0 : (0 : ℝ) ≤ N` using `Nat.cast_nonneg N`. Establish `ha0 : (0 : ℝ) < a` using `by linarith`.

Establish `h4 : 4 ≤ a ^ 2` using `by nlinarith`. Establish `ha3 : 4 * a ≤ a ^ 3`. Use `mul_le_mul_of_nonneg_left h4 ha0.le` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `ha3' : a ^ 2 + a ≤ a ^ 3`.

Establish `h5 : a ≤ a ^ 2 - a` using `by nlinarith`. Use `mul_le_mul_of_nonneg_left h5 ha0.le` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hlgd : ∀ x, lg p r (Dt.d x) ≤ 4 * Real.logb p a`. Introduce `x`.

Apply `lg_le_four p r _ a hp hr hpa` to reduce the goal to its premises. Use `hd x` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsumd : ((∑ x, Dt.d x : ℕ) : ℝ) ≤ (Fintype.card (TL J Dt.nL r) : ℝ) * (2 * a)`. Use `push_cast`.

Combine the equalities or inequalities in the displayed calculation. Establish `hlgS : lg p r (2 * ∑ x, Dt.d x) ≤ 4 * Real.logb p a`. Apply `lg_le_four p r _ a hp hr hpa` to reduce the goal to its premises. Establish `h1 : ((2 * ∑ x, Dt.d x : ℕ) : ℝ) ≤ a ^ 2`. Establish `e : ((2 * ∑ x, Dt.d x : ℕ) : ℝ) = 2 * ((∑ x, Dt.d x : ℕ) : ℝ)` using `by push_cast; ring`.

Rewrite using `[e]`. Establish `h6 : (Fintype.card (TL J Dt.nL r) : ℝ) * (2 * a) ≤ N * (2 * a)` using `mul_le_mul_of_nonneg_right hcardR (by linarith)`. Establish `h7 : 4 * (N : ℝ) * a ≤ a * a` using `mul_le_mul_of_nonneg_right h4N ha0.le`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `heP0 : 0 ≤ Dt.eP`. Unfold `SignedChainData.eP`. Conclude with `mul_nonneg (by positivity) (lg_nonneg p r _ hp hr)`. Establish `heP : Dt.eP ≤ 4 * (k : ℝ) ^ 2 * Real.logb p a`. Unfold `SignedChainData.eP`.

Establish `: (r : ℝ) ^ 2 ≤ (k : ℝ) ^ 2` using `by nlinarith`. Use polynomial arithmetic with `[lg_nonneg p r (2 * ∑ x, Dt.d x) hp hr]`. Establish `hkp0 : 0 ≤ Dt.kp`. Unfold `SignedChainData.kp kap`. Conclude with `Finset.sum_nonneg (fun x _ => mul_nonneg (by positivity) (lg_nonneg p r _ hp hr))`.

Establish `hkp : Dt.kp ≤ 4 * N * (k : ℝ) ^ 2 * Real.logb p a`. Unfold `SignedChainData.kp kap`. Combine the equalities or inequalities in the displayed calculation. Establish `hcTL : (Fintype.card (TL J Dt.nL r) : ℝ) = ∑ j : ZMod J, ((Dt.nL j : ℝ) + r)`. Rewrite using `[card_TL_eq]`.

Use `push_cast`. Both sides reduce to the same expression. Establish `hnch : ((∑ j, Dt.nch j : ℕ) : ℝ) ≤ N`. Use `push_cast`. Simplify using `only [hnch]`.

Use `push_cast`. Combine the equalities or inequalities in the displayed calculation. Establish `hJr : (J : ℝ) * ((r : ℝ) - 1) ≤ N`. Combine the equalities or inequalities in the displayed calculation. Establish `: ∑ j : ZMod J, ((Dt.nL j : ℝ) + r) ≥ ∑ _j : ZMod J, (r : ℝ)` using `Finset.sum_le_sum (fun j _ => by have := Nat.cast_nonneg (α := ℝ) (Dt.nL j); linarith)`.

Simplify using `only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul] at this`. Use the polynomial consequences of the given equalities and inequalities. Use `_ ≤ N := by rw [← hcTL]; exact hcardR`. Use `⟨hkp0, ?_⟩` and prove the remaining obligations. Unfold `SignedChainData.Dm SignedChainData.Dl`.

Establish `hJr0 : (0 : ℝ) ≤ (J : ℝ) * ((r : ℝ) - 1)` using `mul_nonneg (Nat.cast_nonneg _) (by linarith)`. Establish `hD1 : ((∑ j, Dt.nch j : ℕ) : ℝ) * Dt.eP ≤ N * (4 * (k : ℝ) ^ 2 * Real.logb p a)` using `mul_le_mul hnch heP heP0 hN0`. Establish `hD2 : (J : ℝ) * ((r : ℝ) - 1) * Dt.eP ≤ N * (4 * (k : ℝ) ^ 2 * Real.logb p a)` using `mul_le_mul hJr heP heP0 hN0`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem sizes_le (Dt : SignedChainData p O r J) (N k : ℕ) (a : ℝ) (hp : 2 ≤ p) (hr : 1 ≤ r) (hrk : r ≤ k)
    (hcard : Fintype.card (TL J Dt.nL r) ≤ N) (hnch : ∀ j, Dt.nch j = Dt.nL j + 1)
    (hd : ∀ x, (Dt.d x : ℝ) ≤ 2 * a) (ha2 : 2 ≤ a) (hpa : (p : ℝ) ≤ a) (h4N : 4 * (N : ℝ) ≤ a) (hra : (r : ℝ) ≤ a) :
    0 ≤ Dt.kp ∧ Dt.Dm + Dt.Dl + 3 * Dt.kp ≤ 20 * ((N : ℝ) * (k : ℝ) ^ 2 * Real.logb p a) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrkR : (r : ℝ) ≤ k := by exact_mod_cast hrk
  have hk1 : (1 : ℝ) ≤ k := le_trans hrR hrkR
  have hL1 : 1 ≤ Real.logb p a := by
    rw [← Real.logb_self_eq_one hp1]
    exact Real.logb_le_logb_of_le hp1 (by linarith) hpa
  have hcardR : (Fintype.card (TL J Dt.nL r) : ℝ) ≤ N := by exact_mod_cast hcard
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have ha0 : (0 : ℝ) < a := by linarith
  have h4 : 4 ≤ a ^ 2 := by nlinarith
  have ha3 : 4 * a ≤ a ^ 3 := by
    have := mul_le_mul_of_nonneg_left h4 ha0.le
    nlinarith
  have ha3' : a ^ 2 + a ≤ a ^ 3 := by
    have h5 : a ≤ a ^ 2 - a := by nlinarith
    have := mul_le_mul_of_nonneg_left h5 ha0.le
    nlinarith
  have hlgd : ∀ x, lg p r (Dt.d x) ≤ 4 * Real.logb p a := by
    intro x
    apply lg_le_four p r _ a hp hr hpa
    have := hd x
    linarith
  have hsumd : ((∑ x, Dt.d x : ℕ) : ℝ) ≤ (Fintype.card (TL J Dt.nL r) : ℝ) * (2 * a) := by
    push_cast
    calc ∑ x, (Dt.d x : ℝ) ≤ ∑ _x : TL J Dt.nL r, 2 * a := Finset.sum_le_sum (fun x _ => hd x)
      _ = _ := by simp
  have hlgS : lg p r (2 * ∑ x, Dt.d x) ≤ 4 * Real.logb p a := by
    apply lg_le_four p r _ a hp hr hpa
    have h1 : ((2 * ∑ x, Dt.d x : ℕ) : ℝ) ≤ a ^ 2 := by
      have e : ((2 * ∑ x, Dt.d x : ℕ) : ℝ) = 2 * ((∑ x, Dt.d x : ℕ) : ℝ) := by push_cast; ring
      rw [e]
      have h6 : (Fintype.card (TL J Dt.nL r) : ℝ) * (2 * a) ≤ N * (2 * a) :=
        mul_le_mul_of_nonneg_right hcardR (by linarith)
      have h7 : 4 * (N : ℝ) * a ≤ a * a := mul_le_mul_of_nonneg_right h4N ha0.le
      nlinarith
    linarith
  have heP0 : 0 ≤ Dt.eP := by
    unfold SignedChainData.eP
    exact mul_nonneg (by positivity) (lg_nonneg p r _ hp hr)
  have heP : Dt.eP ≤ 4 * (k : ℝ) ^ 2 * Real.logb p a := by
    unfold SignedChainData.eP
    have : (r : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := by nlinarith
    nlinarith [lg_nonneg p r (2 * ∑ x, Dt.d x) hp hr]
  have hkp0 : 0 ≤ Dt.kp := by
    unfold SignedChainData.kp kap
    exact Finset.sum_nonneg (fun x _ => mul_nonneg (by positivity) (lg_nonneg p r _ hp hr))
  have hkp : Dt.kp ≤ 4 * N * (k : ℝ) ^ 2 * Real.logb p a := by
    unfold SignedChainData.kp kap
    calc ∑ x, (r : ℝ) * lg p r (Dt.d x) ≤ ∑ _x : TL J Dt.nL r, (k : ℝ) * (4 * Real.logb p a) :=
          Finset.sum_le_sum (fun x _ => mul_le_mul hrkR (hlgd x) (lg_nonneg p r _ hp hr) (by linarith))
      _ = (Fintype.card (TL J Dt.nL r) : ℝ) * ((k : ℝ) * (4 * Real.logb p a)) := by simp
      _ ≤ N * ((k : ℝ) * (4 * Real.logb p a)) :=
          mul_le_mul_of_nonneg_right hcardR (mul_nonneg (by linarith) (by linarith))
      _ = (4 * N * Real.logb p a) * (k : ℝ) := by ring
      _ ≤ (4 * N * Real.logb p a) * (k : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith) (mul_nonneg (mul_nonneg (by norm_num) hN0) (by linarith))
      _ = 4 * N * (k : ℝ) ^ 2 * Real.logb p a := by ring
  have hcTL : (Fintype.card (TL J Dt.nL r) : ℝ) = ∑ j : ZMod J, ((Dt.nL j : ℝ) + r) := by
    rw [card_TL_eq]; push_cast; rfl
  have hnch : ((∑ j, Dt.nch j : ℕ) : ℝ) ≤ N := by
    push_cast
    simp only [hnch]
    push_cast
    calc ∑ j : ZMod J, ((Dt.nL j : ℝ) + 1) ≤ ∑ j : ZMod J, ((Dt.nL j : ℝ) + r) :=
          Finset.sum_le_sum (fun j _ => by linarith)
      _ ≤ N := by rw [← hcTL]; exact hcardR
  have hJr : (J : ℝ) * ((r : ℝ) - 1) ≤ N := by
    calc (J : ℝ) * ((r : ℝ) - 1) ≤ ∑ j : ZMod J, ((Dt.nL j : ℝ) + r) := by
          have : ∑ j : ZMod J, ((Dt.nL j : ℝ) + r) ≥ ∑ _j : ZMod J, (r : ℝ) :=
            Finset.sum_le_sum (fun j _ => by have := Nat.cast_nonneg (α := ℝ) (Dt.nL j); linarith)
          simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul] at this
          nlinarith
      _ ≤ N := by rw [← hcTL]; exact hcardR
  refine ⟨hkp0, ?_⟩
  unfold SignedChainData.Dm SignedChainData.Dl
  have hJr0 : (0 : ℝ) ≤ (J : ℝ) * ((r : ℝ) - 1) := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have hD1 : ((∑ j, Dt.nch j : ℕ) : ℝ) * Dt.eP ≤ N * (4 * (k : ℝ) ^ 2 * Real.logb p a) :=
    mul_le_mul hnch heP heP0 hN0
  have hD2 : (J : ℝ) * ((r : ℝ) - 1) * Dt.eP ≤ N * (4 * (k : ℝ) ^ 2 * Real.logb p a) :=
    mul_le_mul hJr heP heP0 hN0
  nlinarith

end Sizes

end Formalism.MainNotions.Proposition5Numerics
