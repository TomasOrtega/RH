import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.PairStep

namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M

section steptie
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (D : BlockData N)

noncomputable def stQ (k : ℕ) (kk : Fin D.T.t) (j : Fin D.T.t → ℕ) (jp : ℕ) :
    MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
  (∏ i ∈ univ.erase kk, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
    (∏ i : Fin D.T.t with i.val < k, X (zi D r i) ^ D.T.z i) * X (zP D r) ^ D.zPlus

/- English proof (translation)
Rewrite using `[List.drop_eq_getElem_cons (by simpa using hk)]`. Use `congr 1`. Use `ext`. Simplify using the standard rewrite rules.
-/
theorem st_drop (t k : ℕ) (hk : k < t) :
    (List.finRange t).drop k = ⟨k, hk⟩ :: (List.finRange t).drop (k + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using hk)]
  congr 1
  ext
  simp

/- English proof (translation)
Establish `h` using `List.Nodup.sublist (List.drop_sublist k (List.finRange t)) (List.nodup_finRange t)`. Rewrite `h` using `[st_drop t k hk]`. Conclude with `(List.nodup_cons.1 h).1`.
-/
theorem st_notin (t k : ℕ) (hk : k < t) : (⟨k, hk⟩ : Fin t) ∉ (List.finRange t).drop (k + 1) := by
  have h := List.Nodup.sublist (List.drop_sublist k (List.finRange t)) (List.nodup_finRange t)
  rw [st_drop t k hk] at h
  exact (List.nodup_cons.1 h).1

/- English proof (translation)
Use extensionality with `i`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, Fin.val_mk]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use linear arithmetic over natural numbers and integers.

Introduce `h`. Use linear arithmetic over natural numbers and integers.
-/
theorem st_filter (t k : ℕ) (hk : k < t) :
    (univ.filter (fun i : Fin t => i.val < k + 1)) = insert ⟨k, hk⟩ (univ.filter (fun i : Fin t => i.val < k)) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, Fin.val_mk]
  constructor
  · intro h
    omega
  · intro h
    omega

variable {D}

/- English proof (translation)
Establish `hA' : _ ∧ _ ∧ _` using `hA`. Take `⟨-, hv, -⟩` from `hA'`. Take `⟨h1, hb1, -⟩` from `hv b`. Take `⟨h2, -, hk2⟩` from `hv kk`. Establish `he : (⟨T.pos b, by omega⟩ : Fin N) = ⟨T.pos kk + 1, h2⟩` using `Fin.ext h`.

Rewrite `hb1` using `[he, hk2]`. Conclude with `Bool.false_ne_true hb1`.
-/
private theorem st_vec_lemma {N : ℕ} (LL : Letters N) (T : TieData) (hA : T.Admissible LL)
    (b kk : Fin T.t) (h : T.pos b = T.pos kk + 1) : False := by
  have hA' : _ ∧ _ ∧ _ := hA
  obtain ⟨-, hv, -⟩ := hA'
  obtain ⟨h1, hb1, -⟩ := hv b
  obtain ⟨h2, -, hk2⟩ := hv kk
  have he : (⟨T.pos b, by omega⟩ : Fin N) = ⟨T.pos kk + 1, h2⟩ := Fin.ext h
  rw [he, hk2] at hb1
  exact Bool.false_ne_true hb1

/- English proof (translation)
Establish `hB' : _ ∧ _ ∧ _ ∧ _` using `hB`. Take `⟨hA, hlt, -, hN⟩` from `hB'`. Establish `hA' : _ ∧ _ ∧ _` using `hA`. Establish `hinj : Function.Injective D.T.pos` using `hA'.1.injective`. Establish `hk1` using `hlt kk`.

Establish `hu` using `D.uPos.2`. Establish `e1 : ((D.letterAt (D.T.pos kk) : Fin N) : ℕ) = D.T.pos kk` using `by show min (D.T.pos kk) (N - 1) = D.T.pos kk`. Use linear arithmetic over natural numbers and integers. Establish `e2 : ((D.letterAt (D.T.pos kk + 1) : Fin N) : ℕ) = D.T.pos kk + 1` using `by show min (D.T.pos kk + 1) (N - 1) = D.T.pos kk + 1`. Use linear arithmetic over natural numbers and integers.

Establish `hs1 : (∑ i, if D.T.pos kk = D.T.pos i ∨ D.T.pos kk = D.T.pos i + 1 then j i else 0) = j kk`. Rewrite using `[Finset.sum_eq_single kk (fun b _ hb => if_neg (by`. Introduce and unpack `(h | h)`. Conclude with `hb (hinj h.symm)`. Conclude with `st_vec_lemma D.LL D.T hA kk b h)) (fun h => absurd (Finset.mem_univ kk) h)]`.

Conclude with `if_pos (Or.inl rfl)`. Establish `hs2 : (∑ i, if D.T.pos kk + 1 = D.T.pos i ∨ D.T.pos kk + 1 = D.T.pos i + 1 then j i else 0) = j kk`. Rewrite using `[Finset.sum_eq_single kk (fun b _ hb => if_neg (by`. Introduce and unpack `(h | h)`. Conclude with `st_vec_lemma D.LL D.T hA b kk h.symm`.

Conclude with `hb (hinj (by omega)))) (fun h => absurd (Finset.mem_univ kk) h)]`. Conclude with `if_pos (Or.inr rfl)`. Establish `hne1 : ¬ (D.letterAt (D.T.pos kk) = D.uPos)`. Introduce `h`. Establish `h'` using `congrArg Fin.val h`.

Rewrite `h'` using `[e1]`. Use linear arithmetic over natural numbers and integers. Establish `hne2 : ¬ (D.letterAt (D.T.pos kk + 1) = D.uPos)`. Introduce `h`. Establish `h'` using `congrArg Fin.val h`.

Rewrite `h'` using `[e2]`. Use linear arithmetic over natural numbers and integers. Establish `h1 : (D.lettersAt j jp).deg (D.letterAt (D.T.pos kk)) = D.LL.deg (D.letterAt (D.T.pos kk)) - j kk` using `by show D.LL.deg (D.letterAt (D.T.pos kk)) - (∑ i, if ((D.letterAt (D.T.pos kk) : Fin N) : ℕ) = D.T.pos i ∨ ((D.letterAt (D.T.pos kk) : Fin N) : ℕ) = D.T.pos i + 1 then j i else 0) - (if D.letterAt (D.T.pos kk) = D.uPos then jp else 0) = _`. Rewrite using `[e1, hs1, if_neg hne1, Nat.sub_zero]`. Establish `h2 : (D.lettersAt j jp).deg (D.letterAt (D.T.pos kk + 1)) = D.LL.deg (D.letterAt (D.T.pos kk + 1)) - j kk` using `by show D.LL.deg (D.letterAt (D.T.pos kk + 1)) - (∑ i, if ((D.letterAt (D.T.pos kk + 1) : Fin N) : ℕ) = D.T.pos i ∨ ((D.letterAt (D.T.pos kk + 1) : Fin N) : ℕ) = D.T.pos i + 1 then j i else 0) - (if D.letterAt (D.T.pos kk + 1) = D.uPos then jp else 0) = _`.

Rewrite using `[e2, hs2, if_neg hne2, Nat.sub_zero]`. Use `show tieP (wv D kk) (ev D kk) (zi D r kk) (si D r kk) ((D.lettersAt j jp).deg (D.letterAt (D.T.pos kk))) ((D.lettersAt j jp).deg (D.letterAt (D.T.pos kk + 1))) (D.T.z kk) y = _`. Rewrite using `[h1, h2]`.
-/
theorem st_Pt (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) (kk : Fin D.T.t)
    (y : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    Pt p D j jp kk y = tieP (wv D kk) (ev D kk) (zi D r kk) (si D r kk)
      (D.LL.deg (D.letterAt (D.T.pos kk)) - j kk) (D.LL.deg (D.letterAt (D.T.pos kk + 1)) - j kk) (D.T.z kk) y := by
  have hB' : _ ∧ _ ∧ _ ∧ _ := hB
  obtain ⟨hA, hlt, -, hN⟩ := hB'
  have hA' : _ ∧ _ ∧ _ := hA
  have hinj : Function.Injective D.T.pos := hA'.1.injective
  have hk1 := hlt kk
  have hu := D.uPos.2
  have e1 : ((D.letterAt (D.T.pos kk) : Fin N) : ℕ) = D.T.pos kk := by
    show min (D.T.pos kk) (N - 1) = D.T.pos kk
    omega
  have e2 : ((D.letterAt (D.T.pos kk + 1) : Fin N) : ℕ) = D.T.pos kk + 1 := by
    show min (D.T.pos kk + 1) (N - 1) = D.T.pos kk + 1
    omega
  have hs1 : (∑ i, if D.T.pos kk = D.T.pos i ∨ D.T.pos kk = D.T.pos i + 1 then j i else 0) = j kk := by
    rw [Finset.sum_eq_single kk (fun b _ hb => if_neg (by
      rintro (h | h)
      · exact hb (hinj h.symm)
      · exact st_vec_lemma D.LL D.T hA kk b h)) (fun h => absurd (Finset.mem_univ kk) h)]
    exact if_pos (Or.inl rfl)
  have hs2 : (∑ i, if D.T.pos kk + 1 = D.T.pos i ∨ D.T.pos kk + 1 = D.T.pos i + 1 then j i else 0) = j kk := by
    rw [Finset.sum_eq_single kk (fun b _ hb => if_neg (by
      rintro (h | h)
      · exact st_vec_lemma D.LL D.T hA b kk h.symm
      · exact hb (hinj (by omega)))) (fun h => absurd (Finset.mem_univ kk) h)]
    exact if_pos (Or.inr rfl)
  have hne1 : ¬ (D.letterAt (D.T.pos kk) = D.uPos) := by
    intro h
    have h' := congrArg Fin.val h
    rw [e1] at h'
    omega
  have hne2 : ¬ (D.letterAt (D.T.pos kk + 1) = D.uPos) := by
    intro h
    have h' := congrArg Fin.val h
    rw [e2] at h'
    omega
  have h1 : (D.lettersAt j jp).deg (D.letterAt (D.T.pos kk)) = D.LL.deg (D.letterAt (D.T.pos kk)) - j kk := by
    show D.LL.deg (D.letterAt (D.T.pos kk)) - (∑ i, if ((D.letterAt (D.T.pos kk) : Fin N) : ℕ) = D.T.pos i ∨
      ((D.letterAt (D.T.pos kk) : Fin N) : ℕ) = D.T.pos i + 1 then j i else 0) -
      (if D.letterAt (D.T.pos kk) = D.uPos then jp else 0) = _
    rw [e1, hs1, if_neg hne1, Nat.sub_zero]
  have h2 : (D.lettersAt j jp).deg (D.letterAt (D.T.pos kk + 1)) = D.LL.deg (D.letterAt (D.T.pos kk + 1)) - j kk := by
    show D.LL.deg (D.letterAt (D.T.pos kk + 1)) - (∑ i, if ((D.letterAt (D.T.pos kk + 1) : Fin N) : ℕ) = D.T.pos i ∨
      ((D.letterAt (D.T.pos kk + 1) : Fin N) : ℕ) = D.T.pos i + 1 then j i else 0) -
      (if D.letterAt (D.T.pos kk + 1) = D.uPos then jp else 0) = _
    rw [e2, hs2, if_neg hne2, Nat.sub_zero]
  show tieP (wv D kk) (ev D kk) (zi D r kk) (si D r kk) ((D.lettersAt j jp).deg (D.letterAt (D.T.pos kk)))
    ((D.lettersAt j jp).deg (D.letterAt (D.T.pos kk + 1))) (D.T.z kk) y = _
  rw [h1, h2]

/- English proof (translation)
Establish `hE : (∏ i, D.Ehat p (r` using `r) i ^ j i) = ehP (wv D ⟨k, hk⟩) (ev D ⟨k, hk⟩) (zi D r ⟨k, hk⟩) (si D r ⟨k, hk⟩) ^ j ⟨k, hk⟩ * ∏ i ∈ univ.erase ⟨k, hk⟩, D.Ehat p (r := r) i ^ j i := by`. Rewrite using `[← Finset.mul_prod_erase univ (fun i => D.Ehat p (r := r) i ^ j i) (Finset.mem_univ ⟨k, hk⟩)]`. Both sides reduce to the same expression. Establish `hZ : (∏ i : Fin D.T.t with i.val < k + 1, (X (zi D r i) : MvPolynomial (BVar N r D.T.t) ℚ_[p]) ^ D.T.z i) = (X (zi D r ⟨k, hk⟩) : MvPolynomial (BVar N r D.T.t) ℚ_[p]) ^ D.T.z ⟨k, hk⟩ * ∏ i : Fin D.T.t with i.val < k, (X (zi D r i) : MvPolynomial (BVar N r D.T.t) ℚ_[p]) ^ D.T.z i`. Rewrite using `[st_filter _ k hk, Finset.prod_insert (by simp)]`.

Use `show (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp * (∏ i : Fin D.T.t with i.val < k + 1, X (zi D r i) ^ D.T.z i) * X (zP D r) ^ D.zPlus * PL p D ((List.finRange D.T.t).drop (k + 1)) j jp x = _`. Rewrite using `[hE, hZ]`. Simplify using `only [stQ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem st_mid_succ (k : ℕ) (hk : k < D.T.t) (j : Fin D.T.t → ℕ) (jp : ℕ)
    (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    midGen p D (k + 1) j jp x = stQ p D k ⟨k, hk⟩ j jp *
      (ehP (wv D ⟨k, hk⟩) (ev D ⟨k, hk⟩) (zi D r ⟨k, hk⟩) (si D r ⟨k, hk⟩) ^ j ⟨k, hk⟩ *
        (X (zi D r ⟨k, hk⟩) ^ D.T.z ⟨k, hk⟩ * PL p D ((List.finRange D.T.t).drop (k + 1)) j jp x)) := by
  have hE : (∏ i, D.Ehat p (r := r) i ^ j i) = ehP (wv D ⟨k, hk⟩) (ev D ⟨k, hk⟩) (zi D r ⟨k, hk⟩) (si D r ⟨k, hk⟩) ^ j ⟨k, hk⟩ *
      ∏ i ∈ univ.erase ⟨k, hk⟩, D.Ehat p (r := r) i ^ j i := by
    rw [← Finset.mul_prod_erase univ (fun i => D.Ehat p (r := r) i ^ j i) (Finset.mem_univ ⟨k, hk⟩)]
    rfl
  have hZ : (∏ i : Fin D.T.t with i.val < k + 1,
      (X (zi D r i) : MvPolynomial (BVar N r D.T.t) ℚ_[p]) ^ D.T.z i) =
      (X (zi D r ⟨k, hk⟩) : MvPolynomial (BVar N r D.T.t) ℚ_[p]) ^ D.T.z ⟨k, hk⟩ *
        ∏ i : Fin D.T.t with i.val < k, (X (zi D r i) : MvPolynomial (BVar N r D.T.t) ℚ_[p]) ^ D.T.z i := by
    rw [st_filter _ k hk, Finset.prod_insert (by simp)]
  show (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
    (∏ i : Fin D.T.t with i.val < k + 1, X (zi D r i) ^ D.T.z i) * X (zP D r) ^ D.zPlus *
    PL p D ((List.finRange D.T.t).drop (k + 1)) j jp x = _
  rw [hE, hZ]
  simp only [stQ]
  ring

/- English proof (translation)
Establish `hE : (∏ i, D.Ehat p (r` using `r) i ^ j i) = ehP (wv D ⟨k, hk⟩) (ev D ⟨k, hk⟩) (zi D r ⟨k, hk⟩) (si D r ⟨k, hk⟩) ^ j ⟨k, hk⟩ * ∏ i ∈ univ.erase ⟨k, hk⟩, D.Ehat p (r := r) i ^ j i := by`. Rewrite using `[← Finset.mul_prod_erase univ (fun i => D.Ehat p (r := r) i ^ j i) (Finset.mem_univ ⟨k, hk⟩)]`. Both sides reduce to the same expression. Establish `hP : PL p D ((List.finRange D.T.t).drop k) j jp x = tieP (wv D ⟨k, hk⟩) (ev D ⟨k, hk⟩) (zi D r ⟨k, hk⟩) (si D r ⟨k, hk⟩) (D.LL.deg (D.letterAt (D.T.pos ⟨k, hk⟩)) - j ⟨k, hk⟩) (D.LL.deg (D.letterAt (D.T.pos ⟨k, hk⟩ + 1)) - j ⟨k, hk⟩) (D.T.z ⟨k, hk⟩) (PL p D ((List.finRange D.T.t). …`. Rewrite using `[st_drop _ k hk]`.

Conclude with `st_Pt p hB j jp ⟨k, hk⟩ _`. Use `show (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp * (∏ i : Fin D.T.t with i.val < k, X (zi D r i) ^ D.T.z i) * X (zP D r) ^ D.zPlus * PL p D ((List.finRange D.T.t).drop k) j jp x = _`. Rewrite using `[hE, hP]`. Simplify using `only [stQ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem st_mid (hB : D.BlockOK) (k : ℕ) (hk : k < D.T.t) (j : Fin D.T.t → ℕ) (jp : ℕ)
    (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    midGen p D k j jp x = stQ p D k ⟨k, hk⟩ j jp *
      (ehP (wv D ⟨k, hk⟩) (ev D ⟨k, hk⟩) (zi D r ⟨k, hk⟩) (si D r ⟨k, hk⟩) ^ j ⟨k, hk⟩ *
        tieP (wv D ⟨k, hk⟩) (ev D ⟨k, hk⟩) (zi D r ⟨k, hk⟩) (si D r ⟨k, hk⟩)
          (D.LL.deg (D.letterAt (D.T.pos ⟨k, hk⟩)) - j ⟨k, hk⟩)
          (D.LL.deg (D.letterAt (D.T.pos ⟨k, hk⟩ + 1)) - j ⟨k, hk⟩) (D.T.z ⟨k, hk⟩)
          (PL p D ((List.finRange D.T.t).drop (k + 1)) j jp x)) := by
  have hE : (∏ i, D.Ehat p (r := r) i ^ j i) = ehP (wv D ⟨k, hk⟩) (ev D ⟨k, hk⟩) (zi D r ⟨k, hk⟩) (si D r ⟨k, hk⟩) ^ j ⟨k, hk⟩ *
      ∏ i ∈ univ.erase ⟨k, hk⟩, D.Ehat p (r := r) i ^ j i := by
    rw [← Finset.mul_prod_erase univ (fun i => D.Ehat p (r := r) i ^ j i) (Finset.mem_univ ⟨k, hk⟩)]
    rfl
  have hP : PL p D ((List.finRange D.T.t).drop k) j jp x =
      tieP (wv D ⟨k, hk⟩) (ev D ⟨k, hk⟩) (zi D r ⟨k, hk⟩) (si D r ⟨k, hk⟩)
        (D.LL.deg (D.letterAt (D.T.pos ⟨k, hk⟩)) - j ⟨k, hk⟩)
        (D.LL.deg (D.letterAt (D.T.pos ⟨k, hk⟩ + 1)) - j ⟨k, hk⟩) (D.T.z ⟨k, hk⟩)
        (PL p D ((List.finRange D.T.t).drop (k + 1)) j jp x) := by
    rw [st_drop _ k hk]
    exact st_Pt p hB j jp ⟨k, hk⟩ _
  show (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
    (∏ i : Fin D.T.t with i.val < k, X (zi D r i) ^ D.T.z i) * X (zP D r) ^ D.zPlus *
    PL p D ((List.finRange D.T.t).drop k) j jp x = _
  rw [hE, hP]
  simp only [stQ]
  ring

/- English proof (translation)
Establish `h : (∏ i ∈ univ.erase kk, D.Ehat p (r` using `r) i ^ Function.update j kk l i) = ∏ i ∈ univ.erase kk, D.Ehat p (r := r) i ^ j i := Finset.prod_congr rfl fun i hi => by`. Rewrite using `[Function.update_apply, if_neg (Finset.ne_of_mem_erase hi)]`. Simplify using `only [stQ, h]`.
-/
theorem st_Q_update (k : ℕ) (kk : Fin D.T.t) (j : Fin D.T.t → ℕ) (jp l : ℕ) :
    stQ p (r := r) D k kk (Function.update j kk l) jp = stQ p D k kk j jp := by
  have h : (∏ i ∈ univ.erase kk, D.Ehat p (r := r) i ^ Function.update j kk l i) =
      ∏ i ∈ univ.erase kk, D.Ehat p (r := r) i ^ j i :=
    Finset.prod_congr rfl fun i hi => by
      rw [Function.update_apply, if_neg (Finset.ne_of_mem_erase hi)]
  simp only [stQ, h]

/- English proof (translation)
Introduce `c d h`. Conclude with `(Prod.mk.inj (Sum.inl.inj h)).2`.
-/
theorem st_wv_inj (kk : Fin D.T.t) : Function.Injective (wv (r := r) D kk) := by
  intro c d h
  exact (Prod.mk.inj (Sum.inl.inj h)).2

/- English proof (translation)
Introduce `c d h`. Conclude with `(Prod.mk.inj (Sum.inl.inj h)).2`.
-/
theorem st_ev_inj (kk : Fin D.T.t) : Function.Injective (ev (r := r) D kk) := by
  intro c d h
  exact (Prod.mk.inj (Sum.inl.inj h)).2

/- English proof (translation)
Introduce `h`. Establish `hB' : _ ∧ _ ∧ _ ∧ _` using `hB`. Take `⟨-, hlt, -, hN⟩` from `hB'`. Establish `h2` using `hlt kk`. Establish `h3` using `D.uPos.2`.

Establish `h1` using `congrArg Fin.val (Prod.mk.inj (Sum.inl.inj h)).1`. Express the relevant statement in the definitionally equal form `min (D.T.pos kk) N = min (D.T.pos kk + 1) N at h1`. Use linear arithmetic over natural numbers and integers.
-/
theorem st_wv_ne_ev (hB : D.BlockOK) (kk : Fin D.T.t) (c d : Fin r) : wv D kk c ≠ ev D kk d := by
  intro h
  have hB' : _ ∧ _ ∧ _ ∧ _ := hB
  obtain ⟨-, hlt, -, hN⟩ := hB'
  have h2 := hlt kk
  have h3 := D.uPos.2
  have h1 := congrArg Fin.val (Prod.mk.inj (Sum.inl.inj h)).1
  change min (D.T.pos kk) N = min (D.T.pos kk + 1) N at h1
  omega

/- English proof (translation)
Use `delta Formalism.GM.M.BlockData.LevelOK at h ⊢`. Use `⟨fun i => ?_, h.2⟩` and prove the remaining obligations. Rewrite using `[Function.update_apply]`. Use `split_ifs with hi`. Substitute `hi` using the available equality.

Conclude with `⟨le_trans hl (min_le_left _ _), le_trans hl (min_le_right _ _)⟩`. Conclude with `h.1 i`.
-/
theorem st_levelOK (kk : Fin D.T.t) (j : Fin D.T.t → ℕ) (jp l : ℕ) (h : D.LevelOK j jp)
    (hl : l ≤ min (D.LL.deg (D.letterAt (D.T.pos kk))) (D.LL.deg (D.letterAt (D.T.pos kk + 1)))) :
    D.LevelOK (Function.update j kk l) jp := by
  delta Formalism.GM.M.BlockData.LevelOK at h ⊢
  refine ⟨fun i => ?_, h.2⟩
  rw [Function.update_apply]
  split_ifs with hi
  · subst hi
    exact ⟨le_trans hl (min_le_left _ _), le_trans hl (min_le_right _ _)⟩
  · exact h.1 i

/- English proof (translation)
Take `⟨T, hT⟩` from `(hLin p N r D ((List.finRange D.T.t).drop (k + 1)) j jp).1`. Establish `hnot` using `st_notin D.T.t k hk`. Generalize the expression as in `hkk : (⟨k, hk⟩ : Fin D.T.t) = kk at hnot`. Generalize the expression as in `hL' : (List.finRange D.T.t).drop (k + 1) = L' at hnot hT`. Set `Λ : ℕ → Submodule ℤ_[p] (MvPolynomial (BVar N r D.T.t) ℚ_[p])` to `fun l => Submodule.map (T.restrictScalars ℤ_[p]) (Lat p D (Function.update j kk l) jp)`.

Establish `hcomm : ∀ m y, (tieF (wv D kk) (ev D kk) ^ m) (T y) = T ((tieF (wv D kk) (ev D kk) ^ m) y)`. Introduce `m y`. Rewrite using `[hT, hT]`. Conclude with `(hC p N r D hB L' j jp m y).1 kk hnot`. Establish `ho` using `hdeg (D.letterAt (D.T.pos kk))`.

Establish `hn` using `hdeg (D.letterAt (D.T.pos kk + 1))`. Establish `hz'` using `hzz kk`. Establish `key` using `hPS p (BVar N r D.T.t) r (wv D kk) (ev D kk) (zi D r kk) (si D r kk) hr (fun c => ⟨Sum.inl_ne_inr, Sum.inl_ne_inr⟩) (D.LL.deg (D.letterAt (D.T.pos kk))) (D.LL.deg (D.letterAt (D.T.pos kk + 1))) (D.T.z kk) (Nat.log p (2 * a)) u Λ (by`. Introduce and unpack `l x' ⟨x'', hx'', rfl⟩ m hm`. Use `show (tieF (wv D kk) (ev D kk) ^ m) (T x'') = 0`.

Establish `hb` using `biHom_tie hB (Function.update j kk l) jp kk x'' hx''`. Rewrite `hb` using `[deg_lettersAt_pos hB, deg_lettersAt_pos_succ hB, Function.update_self]`. Rewrite using `[hcomm, tieF_pow_apply_eq_zero_of_min_lt (wv D kk) (ev D kk) (st_wv_inj kk) (st_ev_inj kk) (st_wv_ne_ev hB kk) hb m hm, map_zero])`. Use the proof step `(by`. Introduce and unpack `l m hm x' ⟨x'', hx'', rfl⟩`.

Establish `h` using `hLT p N r D hB hH (Function.update j kk l) jp kk m (Nat.log p (2 * a)) (Nat.log_mono_right (le_trans hm (le_trans (min_le_left _ _) ho))) x'' hx''`. Establish `he : Function.update j kk l + Pi.single kk m = Function.update j kk (l + m)`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = kk`. Substitute `hi` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne hi, Pi.single_eq_of_ne hi]`. Rewrite `h` using `[he]`. Use `⟨_, h, ?_⟩` and prove the remaining obligations. Use `show T _ = _ • (tieF (wv D kk) (ev D kk) ^ m) (T x'')`.

Rewrite using `[map_smul, hcomm])`. Use the proof step `(le_trans (Nat.add_le_add_left (Nat.log_mono_right (by omega)) _) hu)`. Use the proof step `(j kk) (le_min (hOK.1 kk).1 (hOK.1 kk).2) (T x)`. Use the proof step `⟨x, by rw [Function.update_eq_self]; exact hx, rfl⟩`. Substitute `hkk` using the available equality.

Substitute `hL'` using the available equality. Prove the components needed by the constructor for the conclusion. Use `span_map_mem (LinearMap.mulLeft ℚ_[p] (stQ p D k ⟨k, hk⟩ j jp)) _ (Mid p (r := r) D k) ?_ _ key.1` as an intermediate fact. Rewrite using `[st_mid_succ p k hk, ← hT, ← mul_smul_comm]`. Conclude with `this`.

Introduce and unpack `v ⟨l', hl', x', ⟨x'', hx'', rfl⟩, rfl⟩`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨Function.update j ⟨k, hk⟩ l', jp, st_levelOK _ j jp l' hOK hl', x'', hx'', ?_⟩` and prove the remaining obligations. Rewrite using `[st_mid p hB k hk, st_Q_update, Function.update_self, hPar p N r D hB _ (Function.update j ⟨k, hk⟩ l') j jp jp x'' (fun i hi => Function.update_of_ne (fun h : i = ⟨k, hk⟩ => hnot (h ▸ hi)) _ _), ← hT]`. Both sides reduce to the same expression.

Use `span_map_mem (LinearMap.mulLeft ℚ_[p] (stQ p D k ⟨k, hk⟩ j jp)) _ (Mid p (r := r) D (k + 1)) ?_ _ key.2` as an intermediate fact. Rewrite using `[st_mid p hB k hk, ← hT, ← mul_smul_comm]`. Conclude with `this`. Introduce and unpack `v ⟨l', hl', x', ⟨x'', hx'', rfl⟩, rfl⟩`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `⟨Function.update j ⟨k, hk⟩ l', jp, st_levelOK _ j jp l' hOK hl', x'', hx'', ?_⟩` and prove the remaining obligations. Rewrite using `[st_mid_succ p k hk, st_Q_update, Function.update_self, hPar p N r D hB _ (Function.update j ⟨k, hk⟩ l') j jp jp x'' (fun i hi => Function.update_of_ne (fun h : i = ⟨k, hk⟩ => hnot (h ▸ hi)) _ _), ← hT]`. Both sides reduce to the same expression.
-/
theorem st_gen (hPS : PairStep) (hLT : LatTie) (hLin : PLLin) (hC : CommPL) (hPar : ParamPL) (a u : ℕ)
    (hB : D.BlockOK) (hr : 1 ≤ r) (hdeg : ∀ x, D.LL.deg x ≤ 2 * a) (hzz : ∀ i, D.T.z i ≤ 2 * a)
    (hH : HypJoin p (r := r) D) (hu : r * Nat.log p (2 * a) + Nat.log p (6 * a + r) ≤ u) (k : ℕ) (hk : k < D.T.t)
    (j : Fin D.T.t → ℕ) (jp : ℕ) (hOK : D.LevelOK j jp) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p])
    (hx : x ∈ Lat p D (r := r) j jp) :
    (p : ℚ_[p]) ^ u • midGen p D (k + 1) j jp x ∈ Mid p (r := r) D k ∧
      (p : ℚ_[p]) ^ u • midGen p D k j jp x ∈ Mid p (r := r) D (k + 1) := by
  obtain ⟨T, hT⟩ := (hLin p N r D ((List.finRange D.T.t).drop (k + 1)) j jp).1
  have hnot := st_notin D.T.t k hk
  generalize hkk : (⟨k, hk⟩ : Fin D.T.t) = kk at hnot
  generalize hL' : (List.finRange D.T.t).drop (k + 1) = L' at hnot hT
  let Λ : ℕ → Submodule ℤ_[p] (MvPolynomial (BVar N r D.T.t) ℚ_[p]) := fun l =>
    Submodule.map (T.restrictScalars ℤ_[p]) (Lat p D (Function.update j kk l) jp)
  have hcomm : ∀ m y, (tieF (wv D kk) (ev D kk) ^ m) (T y) = T ((tieF (wv D kk) (ev D kk) ^ m) y) := by
    intro m y
    rw [hT, hT]
    exact (hC p N r D hB L' j jp m y).1 kk hnot
  have ho := hdeg (D.letterAt (D.T.pos kk))
  have hn := hdeg (D.letterAt (D.T.pos kk + 1))
  have hz' := hzz kk
  have key := hPS p (BVar N r D.T.t) r (wv D kk) (ev D kk) (zi D r kk) (si D r kk) hr
    (fun c => ⟨Sum.inl_ne_inr, Sum.inl_ne_inr⟩)
    (D.LL.deg (D.letterAt (D.T.pos kk))) (D.LL.deg (D.letterAt (D.T.pos kk + 1))) (D.T.z kk)
    (Nat.log p (2 * a)) u Λ
    (by
      rintro l x' ⟨x'', hx'', rfl⟩ m hm
      show (tieF (wv D kk) (ev D kk) ^ m) (T x'') = 0
      have hb := biHom_tie hB (Function.update j kk l) jp kk x'' hx''
      rw [deg_lettersAt_pos hB, deg_lettersAt_pos_succ hB, Function.update_self] at hb
      rw [hcomm, tieF_pow_apply_eq_zero_of_min_lt (wv D kk) (ev D kk) (st_wv_inj kk) (st_ev_inj kk) (st_wv_ne_ev hB kk) hb m hm,
        map_zero])
    (by
      rintro l m hm x' ⟨x'', hx'', rfl⟩
      have h := hLT p N r D hB hH (Function.update j kk l) jp kk m (Nat.log p (2 * a))
        (Nat.log_mono_right (le_trans hm (le_trans (min_le_left _ _) ho))) x'' hx''
      have he : Function.update j kk l + Pi.single kk m = Function.update j kk (l + m) := by
        funext i
        by_cases hi : i = kk
        · subst hi; simp
        · simp [Function.update_of_ne hi, Pi.single_eq_of_ne hi]
      rw [he] at h
      refine ⟨_, h, ?_⟩
      show T _ = _ • (tieF (wv D kk) (ev D kk) ^ m) (T x'')
      rw [map_smul, hcomm])
    (le_trans (Nat.add_le_add_left (Nat.log_mono_right (by omega)) _) hu)
    (j kk) (le_min (hOK.1 kk).1 (hOK.1 kk).2) (T x)
    ⟨x, by rw [Function.update_eq_self]; exact hx, rfl⟩
  subst hkk
  subst hL'
  constructor
  · have := span_map_mem (LinearMap.mulLeft ℚ_[p] (stQ p D k ⟨k, hk⟩ j jp)) _ (Mid p (r := r) D k) ?_ _ key.1
    · rw [st_mid_succ p k hk, ← hT, ← mul_smul_comm]
      exact this
    · rintro v ⟨l', hl', x', ⟨x'', hx'', rfl⟩, rfl⟩
      apply Submodule.subset_span
      refine ⟨Function.update j ⟨k, hk⟩ l', jp, st_levelOK _ j jp l' hOK hl', x'', hx'', ?_⟩
      rw [st_mid p hB k hk, st_Q_update, Function.update_self,
        hPar p N r D hB _ (Function.update j ⟨k, hk⟩ l') j jp jp x''
          (fun i hi => Function.update_of_ne (fun h : i = ⟨k, hk⟩ => hnot (h ▸ hi)) _ _), ← hT]
      rfl
  · have := span_map_mem (LinearMap.mulLeft ℚ_[p] (stQ p D k ⟨k, hk⟩ j jp)) _ (Mid p (r := r) D (k + 1)) ?_ _ key.2
    · rw [st_mid p hB k hk, ← hT, ← mul_smul_comm]
      exact this
    · rintro v ⟨l', hl', x', ⟨x'', hx'', rfl⟩, rfl⟩
      apply Submodule.subset_span
      refine ⟨Function.update j ⟨k, hk⟩ l', jp, st_levelOK _ j jp l' hOK hl', x'', hx'', ?_⟩
      rw [st_mid_succ p k hk, st_Q_update, Function.update_self,
        hPar p N r D hB _ (Function.update j ⟨k, hk⟩ l') j jp jp x''
          (fun i hi => Function.update_of_ne (fun h : i = ⟨k, hk⟩ => hnot (h ▸ hi)) _ _), ← hT]
      rfl

end steptie

/- English proof (translation)
Introduce `hPS hLT hLin hC hPar p _ N r _ D a u hB hr hdeg hzz hH hu k hk`. Establish `hc : ∀ v : MvPolynomial (BVar N r D.T.t) ℚ_[p], (p : ℚ_[p]) ^ u • v = ((p : ℤ_[p]) ^ u) • v`. Introduce `v`. Rewrite using `[← algebraMap_smul ℚ_[p] ((p : ℤ_[p]) ^ u) v, map_pow, map_natCast]`. Establish `key : ∀ k₁ k₂ : ℕ, (∀ (j : Fin D.T.t → ℕ) (jp : ℕ), D.LevelOK j jp → ∀ x ∈ Lat p D (r` using `r) j jp, (p : ℚ_[p]) ^ u • midGen p D k₁ j jp x ∈ Mid p (r := r) D k₂) → ∀ v ∈ Mid p (r := r) D k₁, (p : ℚ_[p]) ^ u • v ∈ Mid p (r := r) D k₂ := by`.

Introduce `k₁ k₂ hg v hv`. Rewrite using `[hc]`. Establish `hle : Mid p (r` using `r) D k₁ ≤ (Mid p (r := r) D k₂).comap (((p : ℤ_[p]) ^ u) • LinearMap.id : MvPolynomial (BVar N r D.T.t) ℚ_[p] →ₗ[ℤ_[p]] MvPolynomial (BVar N r D.T.t) ℚ_[p]) := by`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `w ⟨j, jp, hOK, x, hx, rfl⟩`.

Simplify using `only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]`. Rewrite using `[← hc]`. Conclude with `hg j jp hOK x hx`. Establish `h2` using `Submodule.mem_comap.1 (hle hv)`. Rewrite `h2` using `[LinearMap.smul_apply, LinearMap.id_apply]`. Then use the resulting hypothesis.

Conclude with `⟨key (k + 1) k (fun j jp hOK x hx => (st_gen p hPS hLT hLin hC hPar a u hB hr hdeg hzz hH hu k hk j jp hOK x hx).1), key k (k + 1) (fun j jp hOK x hx => (st_gen p hPS hLT hLin hC hPar a u hB hr hdeg hzz hH hu k hk j jp hOK x hx).2)⟩`.
-/
theorem StepTie_of : PairStep → LatTie → PLLin → CommPL → ParamPL → JoinCondition := by
  intro hPS hLT hLin hC hPar p _ N r _ D a u hB hr hdeg hzz hH hu k hk
  have hc : ∀ v : MvPolynomial (BVar N r D.T.t) ℚ_[p], (p : ℚ_[p]) ^ u • v = ((p : ℤ_[p]) ^ u) • v := by
    intro v
    rw [← algebraMap_smul ℚ_[p] ((p : ℤ_[p]) ^ u) v, map_pow, map_natCast]
  have key : ∀ k₁ k₂ : ℕ, (∀ (j : Fin D.T.t → ℕ) (jp : ℕ), D.LevelOK j jp → ∀ x ∈ Lat p D (r := r) j jp,
      (p : ℚ_[p]) ^ u • midGen p D k₁ j jp x ∈ Mid p (r := r) D k₂) →
      ∀ v ∈ Mid p (r := r) D k₁, (p : ℚ_[p]) ^ u • v ∈ Mid p (r := r) D k₂ := by
    intro k₁ k₂ hg v hv
    rw [hc]
    have hle : Mid p (r := r) D k₁ ≤ (Mid p (r := r) D k₂).comap
        (((p : ℤ_[p]) ^ u) • LinearMap.id :
          MvPolynomial (BVar N r D.T.t) ℚ_[p] →ₗ[ℤ_[p]] MvPolynomial (BVar N r D.T.t) ℚ_[p]) := by
      refine Submodule.span_le.2 ?_
      rintro w ⟨j, jp, hOK, x, hx, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
      rw [← hc]
      exact hg j jp hOK x hx
    have h2 := Submodule.mem_comap.1 (hle hv)
    rwa [LinearMap.smul_apply, LinearMap.id_apply] at h2
  exact ⟨key (k + 1) k (fun j jp hOK x hx =>
      (st_gen p hPS hLT hLin hC hPar a u hB hr hdeg hzz hH hu k hk j jp hOK x hx).1),
    key k (k + 1) (fun j jp hOK x hx =>
      (st_gen p hPS hLT hLin hC hPar a u hB hr hdeg hzz hH hu k hk j jp hOK x hx).2)⟩

end Formalism.InvariantFactorPaths.KP.LL
