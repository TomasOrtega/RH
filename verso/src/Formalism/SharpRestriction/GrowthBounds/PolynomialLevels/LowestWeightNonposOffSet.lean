import Formalism.SharpRestriction.GrowthBounds.PolynomialLevels.TlNonempty
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.PreChainLe
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembDd
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MemSupportSumMonomial

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.NormalSetCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics Formalism.MainNotions.PairMembershipBlocks

section Congr

variable {R : Type} [CommRing R] {ι : Type} {n : ℕ}

/- English proof (translation)
Apply `MvPolynomial.hom_congr_vars _ _ rfl` to reduce the goal to its premises. Conclude with `RingHom.ext fun a => by simp [twistSub]`. Introduce `v hv _`. Take `⟨h1, h2⟩` from `h v hv`. Simplify using `only [twistSub, coe_eval₂Hom, eval₂_X, h2]`.

Distinguish the cases in `hs : v.1 ∈ S`. Simplify using `[hs, h1.mp hs]`. Simplify using `[hs, mt h1.mpr hs]`.
-/
theorem twistSub_congr (LL LL' : Letters ι) (S S' : Set ι) (j : Fin n) (F : MvPolynomial (ι × Fin n) R)
    (h : ∀ v ∈ F.vars, (v.1 ∈ S ↔ v.1 ∈ S') ∧ LL.vec v.1 = LL'.vec v.1) :
    twistSub LL S j F = twistSub LL' S' j F := by
  apply MvPolynomial.hom_congr_vars _ _ rfl
  · exact RingHom.ext fun a => by simp [twistSub]
  · intro v hv _
    obtain ⟨h1, h2⟩ := h v hv
    simp only [twistSub, coe_eval₂Hom, eval₂_X, h2]
    by_cases hs : v.1 ∈ S
    · simp [hs, h1.mp hs]
    · simp [hs, mt h1.mpr hs]

/- English proof (translation)
Simplify using `only [lam1S, sDegs, twistSub_congr LL LL' S S' 0 F h]`.
-/
theorem lowest_weight_congr [NeZero n] (LL LL' : Letters ι) (S S' : Set ι) (F : MvPolynomial (ι × Fin n) R)
    (h : ∀ v ∈ F.vars, (v.1 ∈ S ↔ v.1 ∈ S') ∧ LL.vec v.1 = LL'.vec v.1) :
    lam1S LL S F = lam1S LL' S' F := by
  simp only [lam1S, sDegs, twistSub_congr LL LL' S S' 0 F h]

/- English proof (translation)
Rewrite using `[lowest_weight_congr LL LL S ∅ F (fun v hv => ⟨by simp [h v hv], rfl⟩)]`. Establish `h0` using `(Joints.StandardMonomialSpace.lowest_degree_le_iff LL ∅ F 0).mpr (fun k hk => le_of_eq (by simpa using Joints.StandardMonomialSpace.sDegs_empty_subset LL 0 F k hk))`. Simplify using `using h0`.
-/
theorem lowest_weight_nonpos_off_set [NeZero n] (LL : Letters ι) (S : Set ι) (F : MvPolynomial (ι × Fin n) R)
    (h : ∀ v ∈ F.vars, v.1 ∉ S) : lam1S LL S F ≤ 0 := by
  rw [lowest_weight_congr LL LL S ∅ F (fun v hv => ⟨by simp [h v hv], rfl⟩)]
  have h0 := (Joints.StandardMonomialSpace.lowest_degree_le_iff LL ∅ F 0).mpr
    (fun k hk => le_of_eq (by simpa using Joints.StandardMonomialSpace.sDegs_empty_subset LL 0 F k hk))
  simpa using h0

end Congr

section Geo

variable {n' r : ℕ} [NeZero n'] [NeZero r] {Fr : Frames n' r} {L₁ N₁ : ℕ} {J : ℕ} [NeZero J] {nL : ZMod J → ℕ}

/- English proof (translation)
Establish `hr : 0 < r` using `NeZero.pos r`. Establish `hmono` using `hV.2.2.1`. Take `⟨j, s⟩` from `t`. Establish `hgap : Fr.fr (segZ j - 1) (r - 1) < Fr.fr (segZ j) 0`. Establish `h` using `hV.2.2.2.1 (segZ j - 1)`.

Simplify using `using h`. Consider the cases of `s with`. Consider the case `inl l`. Establish `hmem` using `DdG.llPos_mem Fr (segZ j) l.val (by rw [← hnL j]; exact l.isLt)`. Simplify using `only [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo] at hmem`.

Establish `h0 : Fr.fr (segZ j) 0 ≤ Fr.fr (segZ j) (r - 1)` using `DdG.fr_le Fr hmono (segZ j) (Nat.zero_le _) (by omega)`. Use `show Fr.fr (segZ j - 1) (r - 1) < llPos Fr (segZ j) l.val ∧ llPos Fr (segZ j) l.val ≤ Fr.fr (segZ j) (r - 1)`. Conclude with `⟨hmem.1.1, by linarith [hmem.1.2]⟩`. Consider the case `inr m`. Establish `hm` using `m.isLt`.

Use `show Fr.fr (segZ j - 1) (r - 1) < Fr.fr (segZ j) (r - 1 - m.val) ∧ Fr.fr (segZ j) (r - 1 - m.val) ≤ Fr.fr (segZ j) (r - 1)`. Conclude with `⟨lt_of_lt_of_le hgap (DdG.fr_le Fr hmono (segZ j) (Nat.zero_le _) (by omega)), DdG.fr_le Fr hmono (segZ j) (by omega) (by omega)⟩`.
-/
private theorem posTL_mem_Ioc_fr_last (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (t : TL J nL r) :
    Fr.fr (segZ t.1 - 1) (r - 1) < posTL Fr t ∧ posTL Fr t ≤ Fr.fr (segZ t.1) (r - 1) := by
  have hr : 0 < r := NeZero.pos r
  have hmono := hV.2.2.1
  obtain ⟨j, s⟩ := t
  have hgap : Fr.fr (segZ j - 1) (r - 1) < Fr.fr (segZ j) 0 := by
    have h := hV.2.2.2.1 (segZ j - 1)
    simpa using h
  cases s with
  | inl l =>
    have hmem := DdG.llPos_mem Fr (segZ j) l.val (by rw [← hnL j]; exact l.isLt)
    simp only [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo] at hmem
    have h0 : Fr.fr (segZ j) 0 ≤ Fr.fr (segZ j) (r - 1) := DdG.fr_le Fr hmono (segZ j) (Nat.zero_le _) (by omega)
    show Fr.fr (segZ j - 1) (r - 1) < llPos Fr (segZ j) l.val ∧ llPos Fr (segZ j) l.val ≤ Fr.fr (segZ j) (r - 1)
    exact ⟨hmem.1.1, by linarith [hmem.1.2]⟩
  | inr m =>
    have hm := m.isLt
    show Fr.fr (segZ j - 1) (r - 1) < Fr.fr (segZ j) (r - 1 - m.val) ∧
      Fr.fr (segZ j) (r - 1 - m.val) ≤ Fr.fr (segZ j) (r - 1)
    exact ⟨lt_of_lt_of_le hgap (DdG.fr_le Fr hmono (segZ j) (Nat.zero_le _) (by omega)),
      DdG.fr_le Fr hmono (segZ j) (by omega) (by omega)⟩

/- English proof (translation)
Establish `hr : 0 < r` using `NeZero.pos r`. Apply `strictMono_int_of_lt_succ` to reduce the goal to its premises. Introduce `s`. Conclude with `lt_of_lt_of_le (hV.2.2.2.1 s) (DdG.fr_le Fr hV.2.2.1 (s + 1) (Nat.zero_le _) (by omega))`.
-/
private theorem fr_last_strictMono (hV : Fr.Valid L₁ N₁) : StrictMono (fun s : ℤ => Fr.fr s (r - 1)) := by
  have hr : 0 < r := NeZero.pos r
  apply strictMono_int_of_lt_succ
  intro s
  exact lt_of_lt_of_le (hV.2.2.2.1 s) (DdG.fr_le Fr hV.2.2.1 (s + 1) (Nat.zero_le _) (by omega))

/- English proof (translation)
Establish `hr : 0 < r` using `NeZero.pos r`. Establish `hmono` using `hV.2.2.1`. Establish `hsm` using `fr_last_strictMono hV`. Establish `hseg : ∀ t t' : TL J nL r, posTL Fr t = posTL Fr t' → segZ t.1 ≤ segZ t'.1`. Introduce `t t' h`.

Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `h1` using `posTL_mem_Ioc_fr_last hV hnL t`. Establish `h2` using `posTL_mem_Ioc_fr_last hV hnL t'`. Establish `h3 : Fr.fr (segZ t'.1) (r - 1) ≤ Fr.fr (segZ t.1 - 1) (r - 1)` using `hsm.monotone (by omega)`.

Combine the linear relations using `[h1.1, h2.2]`. Introduce `t t' h`. Establish `hj : t.1 = t'.1`. Establish `h4` using `le_antisymm (hseg t t' h) (hseg t' t h.symm)`. Unfold `segZ at h4`.

Conclude with `ZMod.val_injective J (by exact_mod_cast h4)`. Take `⟨j, s⟩` from `t`. Take `⟨j', s'⟩` from `t'`. Simplify using `only at hj`. Substitute `hj` using the available equality.

Consider the cases of `s with`. Consider the case `inl l`. Consider the cases of `s' with`. Consider the case `inl l'`. Establish `h' : llPos Fr (segZ j) l.val = llPos Fr (segZ j) l'.val` using `h`.

Establish `he` using `DdG.llPos_inj Fr (segZ j) (by rw [← hnL j]; exact l.isLt) (by rw [← hnL j]; exact l'.isLt) h'`. Rewrite using `[Fin.ext he]`. Consider the case `inr m`. It suffices to derive a contradiction. Establish `hm` using `m.isLt`.

Establish `h' : llPos Fr (segZ j) l.val = Fr.fr (segZ j) (r - 1 - m.val)` using `h`. Establish `hmem` using `DdG.llPos_mem Fr (segZ j) l.val (by rw [← hnL j]; exact l.isLt)`. Simplify using `only [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo] at hmem`. Establish `h5` using `DdG.fr_le Fr hmono (segZ j) (Nat.zero_le (r - 1 - m.val)) (by omega)`. Combine the linear relations using `[hmem.1.2]`.

Consider the case `inr m`. Consider the cases of `s' with`. Consider the case `inl l'`. It suffices to derive a contradiction. Establish `hm` using `m.isLt`.

Establish `h' : Fr.fr (segZ j) (r - 1 - m.val) = llPos Fr (segZ j) l'.val` using `h`. Establish `hmem` using `DdG.llPos_mem Fr (segZ j) l'.val (by rw [← hnL j]; exact l'.isLt)`. Simplify using `only [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo] at hmem`. Establish `h5` using `DdG.fr_le Fr hmono (segZ j) (Nat.zero_le (r - 1 - m.val)) (by omega)`. Combine the linear relations using `[hmem.1.2]`.

Consider the case `inr m'`. Establish `hm` using `m.isLt`. Establish `hm'` using `m'.isLt`. Establish `h' : Fr.fr (segZ j) (r - 1 - m.val) = Fr.fr (segZ j) (r - 1 - m'.val)` using `h`. Establish `he` using `DdG.fr_inj Fr hmono (segZ j) (by omega) (by omega) h'`.

Establish `hmm : m = m'` using `Fin.ext (by omega)`. Rewrite using `[hmm]`.
-/
private theorem posTL_injective (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) :
    Function.Injective (posTL Fr : TL J nL r → ℤ) := by
  have hr : 0 < r := NeZero.pos r
  have hmono := hV.2.2.1
  have hsm := fr_last_strictMono hV
  have hseg : ∀ t t' : TL J nL r, posTL Fr t = posTL Fr t' → segZ t.1 ≤ segZ t'.1 := by
    intro t t' h
    by_contra hlt
    push_neg at hlt
    have h1 := posTL_mem_Ioc_fr_last hV hnL t
    have h2 := posTL_mem_Ioc_fr_last hV hnL t'
    have h3 : Fr.fr (segZ t'.1) (r - 1) ≤ Fr.fr (segZ t.1 - 1) (r - 1) := hsm.monotone (by omega)
    linarith [h1.1, h2.2]
  intro t t' h
  have hj : t.1 = t'.1 := by
    have h4 := le_antisymm (hseg t t' h) (hseg t' t h.symm)
    unfold segZ at h4
    exact ZMod.val_injective J (by exact_mod_cast h4)
  obtain ⟨j, s⟩ := t
  obtain ⟨j', s'⟩ := t'
  simp only at hj
  subst hj
  cases s with
  | inl l =>
    cases s' with
    | inl l' =>
      have h' : llPos Fr (segZ j) l.val = llPos Fr (segZ j) l'.val := h
      have he := DdG.llPos_inj Fr (segZ j) (by rw [← hnL j]; exact l.isLt) (by rw [← hnL j]; exact l'.isLt) h'
      rw [Fin.ext he]
    | inr m =>
      exfalso
      have hm := m.isLt
      have h' : llPos Fr (segZ j) l.val = Fr.fr (segZ j) (r - 1 - m.val) := h
      have hmem := DdG.llPos_mem Fr (segZ j) l.val (by rw [← hnL j]; exact l.isLt)
      simp only [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo] at hmem
      have h5 := DdG.fr_le Fr hmono (segZ j) (Nat.zero_le (r - 1 - m.val)) (by omega)
      linarith [hmem.1.2]
  | inr m =>
    cases s' with
    | inl l' =>
      exfalso
      have hm := m.isLt
      have h' : Fr.fr (segZ j) (r - 1 - m.val) = llPos Fr (segZ j) l'.val := h
      have hmem := DdG.llPos_mem Fr (segZ j) l'.val (by rw [← hnL j]; exact l'.isLt)
      simp only [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo] at hmem
      have h5 := DdG.fr_le Fr hmono (segZ j) (Nat.zero_le (r - 1 - m.val)) (by omega)
      linarith [hmem.1.2]
    | inr m' =>
      have hm := m.isLt
      have hm' := m'.isLt
      have h' : Fr.fr (segZ j) (r - 1 - m.val) = Fr.fr (segZ j) (r - 1 - m'.val) := h
      have he := DdG.fr_inj Fr hmono (segZ j) (by omega) (by omega) h'
      have hmm : m = m' := Fin.ext (by omega)
      rw [hmm]

/- English proof (translation)
Unfold `gT`. Conclude with `Function.leftInverse_invFun (posTL_injective hV hnL) t`.
-/
theorem gT_posTL (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (t : TL J nL r) :
    gT Fr nL (posTL Fr t) = t := by
  unfold gT
  exact Function.leftInverse_invFun (posTL_injective hV hnL) t

/- English proof (translation)
Establish `hr : 0 < r` using `NeZero.pos r`. Establish `hl` using `hx`. Simplify using `only [Frames.letters, Finset.mem_filter, Finset.mem_Icc] at hl`. Establish `hw : Fr.fr (segZ j - 1) (r - 1) < x`. Unfold `Frames.IsW at hW`.

Use `push_neg at hW`. Conclude with `hW`. Distinguish the cases in `hlt : x < Fr.fr (segZ j) 0`. Establish `hLL : x ∈ Fr.LLset (segZ j)`. Simplify using `only [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo]`.

Conclude with `⟨⟨hw, hlt⟩, hl.2⟩`. Take `⟨l, hl1, hl2⟩` from `DdG.exists_llPos Fr (segZ j) x hLL`. Conclude with `⟨Sum.inl ⟨l, by rw [hnL j]; exact hl1⟩, hl2⟩`. Use `push_neg at hlt`. Take `⟨i, hi, hxi⟩` from `DdG.eq_fr Fr hV.2.2.2.2.2.1 (by omega) (segZ j) x hlt hl.1.2 hl.2`.

Use `⟨Sum.inr ⟨r - 1 - i, by omega⟩, ?_⟩` and prove the remaining obligations. Use `show Fr.fr (segZ j) (r - 1 - (r - 1 - i)) = x`. Rewrite using `[hxi]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.
-/
theorem tl_surj (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (x : ℤ)
    (hx : x ∈ Fr.letters (segZ j)) (hW : ¬ Fr.IsW (segZ j) x) : ∃ s, posTL Fr (⟨j, s⟩ : TL J nL r) = x := by
  have hr : 0 < r := NeZero.pos r
  have hl := hx
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc] at hl
  have hw : Fr.fr (segZ j - 1) (r - 1) < x := by
    unfold Frames.IsW at hW
    push_neg at hW
    exact hW
  by_cases hlt : x < Fr.fr (segZ j) 0
  · have hLL : x ∈ Fr.LLset (segZ j) := by
      simp only [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo]
      exact ⟨⟨hw, hlt⟩, hl.2⟩
    obtain ⟨l, hl1, hl2⟩ := DdG.exists_llPos Fr (segZ j) x hLL
    exact ⟨Sum.inl ⟨l, by rw [hnL j]; exact hl1⟩, hl2⟩
  · push_neg at hlt
    obtain ⟨i, hi, hxi⟩ := DdG.eq_fr Fr hV.2.2.2.2.2.1 (by omega) (segZ j) x hlt hl.1.2 hl.2
    refine ⟨Sum.inr ⟨r - 1 - i, by omega⟩, ?_⟩
    show Fr.fr (segZ j) (r - 1 - (r - 1 - i)) = x
    rw [hxi]
    congr 1
    omega

/- English proof (translation)
Unfold `segZ`. Rewrite using `[ZMod.val_natCast_of_lt hi]`.
-/
theorem segZ_natCast (i : ℕ) (hi : i < J) : segZ ((i : ℕ) : ZMod J) = (i : ℤ) := by
  unfold segZ
  rw [ZMod.val_natCast_of_lt hi]

/- English proof (translation)
Establish `hiJ : i < J` using `by rw [hJ]; exact hi`. Establish `hs` using `segZ_natCast (J := J) i hiJ`. Establish `hx' : x ∈ Fr.letters (segZ ((i : ℕ) : ZMod J))` using `by rw [hs]; exact hx`. Establish `hW' : ¬ Fr.IsW (segZ ((i : ℕ) : ZMod J)) x` using `by rw [hs]; exact hW`. Take `⟨s, hs2⟩` from `tl_surj hV hnL ((i : ℕ) : ZMod J) x hx' hW'`.

Conclude with `⟨⟨(i : ZMod J), s⟩, hs, hs2⟩`.
-/
theorem tl_surj' (hV : Fr.Valid L₁ N₁) (hJ : J = Fr.J) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (i : ℕ)
    (hi : i < Fr.J) (x : ℤ) (hx : x ∈ Fr.letters i) (hW : ¬ Fr.IsW i x) :
    ∃ t : TL J nL r, segZ t.1 = (i : ℤ) ∧ posTL Fr t = x := by
  have hiJ : i < J := by rw [hJ]; exact hi
  have hs := segZ_natCast (J := J) i hiJ
  have hx' : x ∈ Fr.letters (segZ ((i : ℕ) : ZMod J)) := by rw [hs]; exact hx
  have hW' : ¬ Fr.IsW (segZ ((i : ℕ) : ZMod J)) x := by rw [hs]; exact hW
  obtain ⟨s, hs2⟩ := tl_surj hV hnL ((i : ℕ) : ZMod J) x hx' hW'
  exact ⟨⟨(i : ZMod J), s⟩, hs, hs2⟩

/- English proof (translation)
Simplify using `[NSet]`.
-/
theorem mem_NSet_inl (j : ZMod J) (l : Fin (nL j)) (u : ℕ) :
    (⟨j, Sum.inl l⟩ : TL J nL r) ∈ NSet nL j u ↔ l.val < u := by
  simp [NSet]

/- English proof (translation)
Simplify using `[NSet]`.
-/
theorem mem_NSet_inr (j : ZMod J) (m : Fin r) (u : ℕ) :
    (⟨j, Sum.inr m⟩ : TL J nL r) ∈ NSet nL j u ↔ nL j + (r - 1 - m.val) < u := by
  simp [NSet]

/- English proof (translation)
Apply the tactic sequence `rcases h with ⟨l, rfl, _⟩ | ⟨m, rfl, _⟩ <;> rfl`.
-/
theorem mem_NSet_fst {j : ZMod J} {u : ℕ} {t : TL J nL r} (h : t ∈ NSet nL j u) : t.1 = j := by
  rcases h with ⟨l, rfl, _⟩ | ⟨m, rfl, _⟩ <;> rfl

/- English proof (translation)
Establish `hmono` using `hV.2.2.1`. Unfold `posU`. Distinguish the cases in `hb' : b < nL j`. Establish `ha' : a < nL j` using `lt_trans hab hb'`. Rewrite using `[if_pos ha', if_pos hb']`.

Conclude with `Formalism.MainNotions.Proposition5Numerics.llPos_lt _ _ _ hab (by rw [← hnL j]; exact hb')`. Rewrite using `[if_neg hb']`. Distinguish the cases in `ha' : a < nL j`. Rewrite using `[if_pos ha']`. Establish `hm` using `Formalism.MainNotions.Proposition5Numerics.llPos_mem Fr (segZ j) a (by rw [← hnL j]; exact ha')`.

Simplify using `only [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo] at hm`. Establish `h2` using `Formalism.MainNotions.Proposition5Numerics.DdG.fr_le Fr hmono (segZ j) (Nat.zero_le (b - nL j)) (by omega)`. Conclude with `lt_of_lt_of_le hm.1.2 h2`. Rewrite using `[if_neg ha']`. Conclude with `Formalism.MainNotions.Proposition5Numerics.DdG.fr_lt Fr hmono (segZ j) (by omega) (by omega)`.
-/
private theorem posU_strictMono (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J)
    (a b : ℕ) (hab : a < b) (hb : b < nL j + r) :
    posU Fr (nL j) (segZ j) a < posU Fr (nL j) (segZ j) b := by
  have hmono := hV.2.2.1
  unfold posU
  by_cases hb' : b < nL j
  · have ha' : a < nL j := lt_trans hab hb'
    rw [if_pos ha', if_pos hb']
    exact Formalism.MainNotions.Proposition5Numerics.llPos_lt _ _ _ hab (by rw [← hnL j]; exact hb')
  · rw [if_neg hb']
    by_cases ha' : a < nL j
    · rw [if_pos ha']
      have hm := Formalism.MainNotions.Proposition5Numerics.llPos_mem Fr (segZ j) a (by rw [← hnL j]; exact ha')
      simp only [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo] at hm
      have h2 := Formalism.MainNotions.Proposition5Numerics.DdG.fr_le Fr hmono (segZ j) (Nat.zero_le (b - nL j)) (by omega)
      exact lt_of_lt_of_le hm.1.2 h2
    · rw [if_neg ha']
      exact Formalism.MainNotions.Proposition5Numerics.DdG.fr_lt Fr hmono (segZ j) (by omega) (by omega)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hc`. Break down `(not_lt.mp hc).lt_or_eq with hc | hc` into its components or cases. Conclude with `lt_asymm h (posU_strictMono hV hnL j b a hc ha)`.

Substitute `hc` using the available equality. Conclude with `lt_irrefl _ h`. Introduce `h`. Conclude with `posU_strictMono hV hnL j a b h hb`.
-/
private theorem posU_lt_posU_iff (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J)
    (a b : ℕ) (ha : a < nL j + r) (hb : b < nL j + r) :
    posU Fr (nL j) (segZ j) a < posU Fr (nL j) (segZ j) b ↔ a < b := by
  constructor
  · intro h
    by_contra hc
    rcases (not_lt.mp hc).lt_or_eq with hc | hc
    · exact lt_asymm h (posU_strictMono hV hnL j b a hc ha)
    · subst hc
      exact lt_irrefl _ h
  · intro h
    exact posU_strictMono hV hnL j a b h hb

/- English proof (translation)
Rewrite using `[← not_lt, ← not_lt, posU_lt_posU_iff hV hnL j b a hb ha]`.
-/
private theorem posU_le_posU_iff (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J)
    (a b : ℕ) (ha : a < nL j + r) (hb : b < nL j + r) :
    posU Fr (nL j) (segZ j) a ≤ posU Fr (nL j) (segZ j) b ↔ a ≤ b := by
  rw [← not_lt, ← not_lt, posU_lt_posU_iff hV hnL j b a hb ha]

/- English proof (translation)
Establish `hr : 0 < r` using `Nat.pos_of_ne_zero (NeZero.ne r)`. Consider the cases of `s with`. Consider the case `inl l`. Rewrite using `[mem_NSet_inl]`. Establish `hl` using `l.isLt`.

Establish `hp : posTL Fr (⟨j, Sum.inl l⟩ : TL J nL r) = posU Fr (nL j) (segZ j) l.val`. Simplify using `[posTL, posU, l.isLt]`. Rewrite using `[hp, posU_lt_posU_iff hV hnL j _ _ (by omega) hu]`. Consider the case `inr m`. Rewrite using `[mem_NSet_inr]`.

Establish `hp : posTL Fr (⟨j, Sum.inr m⟩ : TL J nL r) = posU Fr (nL j) (segZ j) (nL j + (r - 1 - m.val))`. Simplify using `[posTL, posU]`. Rewrite using `[hp, posU_lt_posU_iff hV hnL j _ _ (by omega) hu]`.
-/
theorem NSet_lt (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < nL j + r) (s : Fin (nL j) ⊕ Fin r) :
    (⟨j, s⟩ : TL J nL r) ∈ NSet nL j u ↔ posTL Fr (⟨j, s⟩ : TL J nL r) < posU Fr (nL j) (segZ j) u := by
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  cases s with
  | inl l =>
    rw [mem_NSet_inl]
    have hl := l.isLt
    have hp : posTL Fr (⟨j, Sum.inl l⟩ : TL J nL r) = posU Fr (nL j) (segZ j) l.val := by
      simp [posTL, posU, l.isLt]
    rw [hp, posU_lt_posU_iff hV hnL j _ _ (by omega) hu]
  | inr m =>
    rw [mem_NSet_inr]
    have hp : posTL Fr (⟨j, Sum.inr m⟩ : TL J nL r) = posU Fr (nL j) (segZ j) (nL j + (r - 1 - m.val)) := by
      simp [posTL, posU]
    rw [hp, posU_lt_posU_iff hV hnL j _ _ (by omega) hu]

/- English proof (translation)
Establish `hr : 0 < r` using `Nat.pos_of_ne_zero (NeZero.ne r)`. Consider the cases of `s with`. Consider the case `inl l`. Rewrite using `[mem_NSet_inl, Nat.lt_succ_iff]`. Establish `hl` using `l.isLt`.

Establish `hp : posTL Fr (⟨j, Sum.inl l⟩ : TL J nL r) = posU Fr (nL j) (segZ j) l.val`. Simplify using `[posTL, posU, l.isLt]`. Rewrite using `[hp, posU_le_posU_iff hV hnL j _ _ (by omega) hu]`. Consider the case `inr m`. Rewrite using `[mem_NSet_inr, Nat.lt_succ_iff]`.

Establish `hp : posTL Fr (⟨j, Sum.inr m⟩ : TL J nL r) = posU Fr (nL j) (segZ j) (nL j + (r - 1 - m.val))`. Simplify using `[posTL, posU]`. Rewrite using `[hp, posU_le_posU_iff hV hnL j _ _ (by omega) hu]`.
-/
theorem NSet_le (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < nL j + r) (s : Fin (nL j) ⊕ Fin r) :
    (⟨j, s⟩ : TL J nL r) ∈ NSet nL j (u + 1) ↔ posTL Fr (⟨j, s⟩ : TL J nL r) ≤ posU Fr (nL j) (segZ j) u := by
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  cases s with
  | inl l =>
    rw [mem_NSet_inl, Nat.lt_succ_iff]
    have hl := l.isLt
    have hp : posTL Fr (⟨j, Sum.inl l⟩ : TL J nL r) = posU Fr (nL j) (segZ j) l.val := by
      simp [posTL, posU, l.isLt]
    rw [hp, posU_le_posU_iff hV hnL j _ _ (by omega) hu]
  | inr m =>
    rw [mem_NSet_inr, Nat.lt_succ_iff]
    have hp : posTL Fr (⟨j, Sum.inr m⟩ : TL J nL r) = posU Fr (nL j) (segZ j) (nL j + (r - 1 - m.val)) := by
      simp [posTL, posU]
    rw [hp, posU_le_posU_iff hV hnL j _ _ (by omega) hu]

end Geo

section Fac

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {n' r : ℕ} [NeZero n'] [NeZero r]
  {Fr : Frames n' r} {L₁ N₁ : ℕ} {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J) {K : ℕ} [NeZero K]

/- English proof (translation)
Take `⟨j, l | m⟩` from `t`. Simplify using `only [SignedChainData.trueLet, LZ, posTL]`. Conclude with `hsgn j l`. Simplify using `only [SignedChainData.trueLet, LZ, posTL]`. Establish `h` using `(hV.2.2.2.2.1 (segZ j) (r - 1 - m.val) (by have := NeZero.pos r; omega)).2`.

Simplify using `[h]`.
-/
theorem trueLet_vec (hV : Fr.Valid L₁ N₁) (hsgn : ∀ j l, Dt.sgn j l = decide (Even (llPos Fr (segZ j) l.val)))
    (t : TL J Dt.nL r) : Dt.trueLet.vec t = LZ.vec (posTL Fr t) := by
  obtain ⟨j, l | m⟩ := t
  · simp only [SignedChainData.trueLet, LZ, posTL]
    exact hsgn j l
  · simp only [SignedChainData.trueLet, LZ, posTL]
    have h := (hV.2.2.2.2.1 (segZ j) (r - 1 - m.val) (by have := NeZero.pos r; omega)).2
    simp [h]

/- English proof (translation)
Take `⟨s, hs⟩` from `tl_surj hV hnL j x hx hW`. Conclude with `⟨s, by rw [← hs, gT_posTL hV hnL], hs⟩`.
-/
private theorem exists_gT_eq_and_posTL_eq_of_not_isW (hV : Fr.Valid L₁ N₁) {nL : ZMod J → ℕ} (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card)
    (j : ZMod J) (x : ℤ) (hx : x ∈ Fr.letters (segZ j)) (hW : ¬ Fr.IsW (segZ j) x) :
    ∃ s, gT Fr nL x = (⟨j, s⟩ : TL J nL r) ∧ posTL Fr (⟨j, s⟩ : TL J nL r) = x := by
  obtain ⟨s, hs⟩ := tl_surj hV hnL j x hx hW
  exact ⟨s, by rw [← hs, gT_posTL hV hnL], hs⟩

/- English proof (translation)
Introduce `v hv`. Take `⟨w, hw, rfl⟩` from `Finset.mem_image.mp (vars_rename _ _ hv)`. Establish `hw' : w ∈ A.vars` using `vars_map _ _ hw`. Take `⟨hx, hW⟩` from `(mem_supported.mp hA) hw'`. Take `⟨s, hs, -⟩` from `exists_gT_eq_and_posTL_eq_of_not_isW hV hnL j w.1 hx hW`.

Simplify using `[hs]`.
-/
theorem Rn_vars (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card) (j : ZMod J)
    (A : MvPolynomial (ℤ × Fin K) O)
    (hA : A ∈ supported O {v : ℤ × Fin K | v.1 ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) v.1}) :
    ∀ v ∈ (Rn Fr Dt.nL A).vars, v.1.1 = j := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp (vars_rename _ _ hv)
  have hw' : w ∈ A.vars := vars_map _ _ hw
  obtain ⟨hx, hW⟩ := (mem_supported.mp hA) hw'
  obtain ⟨s, hs, -⟩ := exists_gT_eq_and_posTL_eq_of_not_isW hV hnL j w.1 hx hW
  simp [hs]

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap O (KK O))` using `IsFractionRing.injective O (FractionRing O)`. Choose the witnesses or unpack the hypotheses as in `⟨A', rfl⟩ : ∃ A' : MvPolynomial ({x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x} × Fin K) O, rename (fun v : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x} × Fin K => (v.1.val, v.2)) A' = A := by`. Use `exists_rename_eq_of_vars_subset_range A _ ?_ ?_` and prove the remaining obligations. Introduce and unpack `⟨a, b⟩ ⟨c, d⟩ h`. Simplify using `only [Prod.mk.injEq] at h`.

Conclude with `Prod.ext (Subtype.ext h.1) h.2`. Introduce `v hv`. Take `⟨hx, hW⟩` from `(mem_supported.mp hA) hv`. Conclude with `⟨(⟨v.1, hx, hW⟩, v.2), rfl⟩`. Establish `hgood : ∀ i : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x}, ∃ s, gT Fr Dt.nL i.val = (⟨j, s⟩ : TL J Dt.nL r) ∧ posTL Fr (⟨j, s⟩ : TL J Dt.nL r) = i.val` using `fun i => exists_gT_eq_and_posTL_eq_of_not_isW hV hnL j i.val i.2.1 i.2.2`.

Establish `hpos : ∀ i : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x}, posTL Fr (gT Fr Dt.nL i.val) = i.val`. Introduce `i`. Take `⟨s, hs, hs'⟩` from `hgood i`. Rewrite using `[hs, hs']`. Establish `hinj2 : Function.Injective (fun i : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x} => gT Fr Dt.nL i.val)`.

Introduce `a b h`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hpos a, ← hpos b]`. Conclude with `congrArg (posTL Fr) h`. Establish `hvec : ∀ i : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x}, Dt.trueLet.vec (gT Fr Dt.nL i.val) = (Letters.mk fun i : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x} => LZ.vec i.val).vec i`.

Introduce `i`. Take `⟨s, hs, hs'⟩` from `hgood i`. Rewrite using `[hs, trueLet_vec Dt hV hsgn, hs']`. Establish `hmem : ∀ i : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x}, gT Fr Dt.nL i.val ∈ S ↔ i ∈ {i : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x} | i.val ∈ Sz}`. Introduce `i`.

Take `⟨s, hs, hs'⟩` from `hgood i`. Rewrite using `[hs, hS s, hs']`. Both sides reduce to the same expression. Establish `hR : Rn Fr Dt.nL (rename (fun v : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x} × Fin K => (v.1.val, v.2)) A') = rename (fun v : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x} × Fin K => (gT Fr Dt.nL v.1.val, v.2)) (MvPolynomial.map (algebraMap O (KK O)) A')`. Unfold `Rn`.

Rewrite using `[map_rename, rename_rename]`. Both sides reduce to the same expression. Apply `le_of_eq` to reduce the goal to its premises. Rewrite using `[hR]`. Unfold `lam1S`.

Rewrite using `[symbolGeneratorData.md_sDegs_rename (fun i : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x} => gT Fr Dt.nL i.val) hinj2 (Letters.mk fun i : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x} => LZ.vec i.val) Dt.trueLet {i | i.val ∈ Sz} S hvec hmem, Joints.Standar …`.
-/
theorem lam_Rn_le (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card)
    (hsgn : ∀ j l, Dt.sgn j l = decide (Even (llPos Fr (segZ j) l.val))) (j : ZMod J)
    (A : MvPolynomial (ℤ × Fin K) O)
    (hA : A ∈ supported O {v : ℤ × Fin K | v.1 ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) v.1})
    (S : Set (TL J Dt.nL r)) (Sz : Set ℤ)
    (hS : ∀ s, (⟨j, s⟩ : TL J Dt.nL r) ∈ S ↔ posTL Fr (⟨j, s⟩ : TL J Dt.nL r) ∈ Sz) :
    lam1S Dt.trueLet S (Rn Fr Dt.nL A) ≤ lam1S LZ Sz A := by
  have hinj : Function.Injective (algebraMap O (KK O)) := IsFractionRing.injective O (FractionRing O)
  obtain ⟨A', rfl⟩ : ∃ A' : MvPolynomial ({x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x} × Fin K) O,
      rename (fun v : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x} × Fin K => (v.1.val, v.2)) A' = A := by
    refine exists_rename_eq_of_vars_subset_range A _ ?_ ?_
    · rintro ⟨a, b⟩ ⟨c, d⟩ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Subtype.ext h.1) h.2
    · intro v hv
      obtain ⟨hx, hW⟩ := (mem_supported.mp hA) hv
      exact ⟨(⟨v.1, hx, hW⟩, v.2), rfl⟩
  have hgood : ∀ i : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x},
      ∃ s, gT Fr Dt.nL i.val = (⟨j, s⟩ : TL J Dt.nL r) ∧ posTL Fr (⟨j, s⟩ : TL J Dt.nL r) = i.val :=
    fun i => exists_gT_eq_and_posTL_eq_of_not_isW hV hnL j i.val i.2.1 i.2.2
  have hpos : ∀ i : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x},
      posTL Fr (gT Fr Dt.nL i.val) = i.val := by
    intro i
    obtain ⟨s, hs, hs'⟩ := hgood i
    rw [hs, hs']
  have hinj2 : Function.Injective
      (fun i : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x} => gT Fr Dt.nL i.val) := by
    intro a b h
    apply Subtype.ext
    rw [← hpos a, ← hpos b]
    exact congrArg (posTL Fr) h
  have hvec : ∀ i : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x},
      Dt.trueLet.vec (gT Fr Dt.nL i.val) = (Letters.mk fun i : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x} => LZ.vec i.val).vec i := by
    intro i
    obtain ⟨s, hs, hs'⟩ := hgood i
    rw [hs, trueLet_vec Dt hV hsgn, hs']
  have hmem : ∀ i : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x},
      gT Fr Dt.nL i.val ∈ S ↔ i ∈ {i : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x} | i.val ∈ Sz} := by
    intro i
    obtain ⟨s, hs, hs'⟩ := hgood i
    rw [hs, hS s, hs']
    rfl
  have hR : Rn Fr Dt.nL (rename (fun v : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x} × Fin K => (v.1.val, v.2)) A') =
      rename (fun v : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x} × Fin K => (gT Fr Dt.nL v.1.val, v.2))
        (MvPolynomial.map (algebraMap O (KK O)) A') := by
    unfold Rn
    rw [map_rename, rename_rename]
    rfl
  apply le_of_eq
  rw [hR]
  unfold lam1S
  rw [symbolGeneratorData.md_sDegs_rename (fun i : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x} => gT Fr Dt.nL i.val) hinj2
      (Letters.mk fun i : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x} => LZ.vec i.val) Dt.trueLet
      {i | i.val ∈ Sz} S hvec hmem,
    Joints.StandardMonomialSpace.sDegs_map _ hinj,
    symbolGeneratorData.md_sDegs_rename (fun i : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x} => i.val) Subtype.val_injective
      (Letters.mk fun i : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x} => LZ.vec i.val) LZ
      {i | i.val ∈ Sz} Sz (fun _ => rfl) (fun _ => Iff.rfl)]

/- English proof (translation)
Establish `hjlt : j.val < Fr.J` using `hJ ▸ ZMod.val_lt j`. Establish `hmemr : j.val ∈ Finset.range Fr.J` using `Finset.mem_range.mpr hjlt`. Rewrite using `[← Finset.mul_prod_erase _ _ hmemr]`. Establish `h1 : lam1S Dt.trueLet S (Rn Fr Dt.nL (G (j.val : ℤ))) ≤ lam1S LZ Sz (G (segZ j))` using `lam_Rn_le Dt hV hnL hsgn j (G (j.val : ℤ)) (hG j.val hjlt) S Sz hS`. Establish `h2 : lam1S Dt.trueLet S (∏ i ∈ (Finset.range Fr.J).erase j.val, Rn Fr Dt.nL (G (i : ℤ))) ≤ 0`.

Apply `lowest_weight_nonpos_off_set` to reduce the goal to its premises. Introduce `v hv hvS`. Take `⟨i, hi, hvi⟩` from `Finset.mem_biUnion.mp (vars_prod _ hv)`. Take `⟨hne, hir⟩` from `Finset.mem_erase.mp hi`. Establish `hiJ : i < J` using `hJ ▸ Finset.mem_range.mp hir`.

Establish `hGi : G (i : ℤ) ∈ supported O {v : ℤ × Fin K | v.1 ∈ Fr.letters (segZ ((i : ℕ) : ZMod J)) ∧ ¬ Fr.IsW (segZ ((i : ℕ) : ZMod J)) v.1}`. Rewrite using `[segZ_natCast i hiJ]`. Conclude with `hG i (Finset.mem_range.mp hir)`. Establish `hv1` using `Rn_vars Dt hV hnL ((i : ℕ) : ZMod J) (G (i : ℤ)) hGi v hvi`. Establish `hv2` using `hSj v.1 hvS`.

Apply `hne` to reduce the goal to its premises. Rewrite using `[← hv2, hv1, ZMod.val_natCast_of_lt hiJ]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem lam_prod_le (hV : Fr.Valid L₁ N₁) (hJ : J = Fr.J) (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card)
    (hsgn : ∀ j l, Dt.sgn j l = decide (Even (llPos Fr (segZ j) l.val)))
    (G : ℤ → MvPolynomial (ℤ × Fin K) O)
    (hG : ∀ i : ℕ, i < Fr.J → G i ∈ supported O {v : ℤ × Fin K | v.1 ∈ Fr.letters i ∧ ¬ Fr.IsW i v.1})
    (j : ZMod J) (S : Set (TL J Dt.nL r)) (Sz : Set ℤ) (hSj : ∀ t ∈ S, t.1 = j)
    (hS : ∀ s, (⟨j, s⟩ : TL J Dt.nL r) ∈ S ↔ posTL Fr (⟨j, s⟩ : TL J Dt.nL r) ∈ Sz) :
    lam1S Dt.trueLet S (∏ i ∈ Finset.range Fr.J, Rn Fr Dt.nL (G i)) ≤ lam1S LZ Sz (G (segZ j)) := by
  have hjlt : j.val < Fr.J := hJ ▸ ZMod.val_lt j
  have hmemr : j.val ∈ Finset.range Fr.J := Finset.mem_range.mpr hjlt
  rw [← Finset.mul_prod_erase _ _ hmemr]
  have h1 : lam1S Dt.trueLet S (Rn Fr Dt.nL (G (j.val : ℤ))) ≤ lam1S LZ Sz (G (segZ j)) :=
    lam_Rn_le Dt hV hnL hsgn j (G (j.val : ℤ)) (hG j.val hjlt) S Sz hS
  have h2 : lam1S Dt.trueLet S (∏ i ∈ (Finset.range Fr.J).erase j.val, Rn Fr Dt.nL (G (i : ℤ))) ≤ 0 := by
    apply lowest_weight_nonpos_off_set
    intro v hv hvS
    obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp (vars_prod _ hv)
    obtain ⟨hne, hir⟩ := Finset.mem_erase.mp hi
    have hiJ : i < J := hJ ▸ Finset.mem_range.mp hir
    have hGi : G (i : ℤ) ∈ supported O {v : ℤ × Fin K | v.1 ∈ Fr.letters (segZ ((i : ℕ) : ZMod J)) ∧
        ¬ Fr.IsW (segZ ((i : ℕ) : ZMod J)) v.1} := by
      rw [segZ_natCast i hiJ]
      exact hG i (Finset.mem_range.mp hir)
    have hv1 := Rn_vars Dt hV hnL ((i : ℕ) : ZMod J) (G (i : ℤ)) hGi v hvi
    have hv2 := hSj v.1 hvS
    apply hne
    rw [← hv2, hv1, ZMod.val_natCast_of_lt hiJ]
  calc lam1S Dt.trueLet S (Rn Fr Dt.nL (G (j.val : ℤ)) * ∏ i ∈ (Finset.range Fr.J).erase j.val, Rn Fr Dt.nL (G (i : ℤ)))
      ≤ lam1S Dt.trueLet S (Rn Fr Dt.nL (G (j.val : ℤ))) + lam1S Dt.trueLet S (∏ i ∈ (Finset.range Fr.J).erase j.val, Rn Fr Dt.nL (G (i : ℤ))) :=
        GLWeightTheory.flt_lam1S_mul_le _ _ _ _
    _ ≤ lam1S LZ Sz (G (segZ j)) + 0 := add_le_add h1 h2
    _ = lam1S LZ Sz (G (segZ j)) := add_zero _

end Fac

end Formalism.MainNotions.NormalSetCounting
