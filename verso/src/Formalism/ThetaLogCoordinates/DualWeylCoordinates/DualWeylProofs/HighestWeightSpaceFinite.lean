import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QcColHSuccLe

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

def qr_ext {m : ℕ} (e : Prop) [Decidable e] (S : Finset (Fin m)) : Finset (Fin (m + 1)) :=
  if e then insert (Fin.last m) (S.map Fin.castSuccEmb) else S.map Fin.castSuccEmb

section Ext

variable {m : ℕ} (e : Prop) [Decidable e] (S : Finset (Fin m))

/- English proof (translation)
Simplify using `only [Finset.mem_map, not_exists, not_and]`. Introduce `a _ h`. Conclude with `(Fin.castSucc_lt_last a).ne h`.
-/
lemma qr_last_notMem : Fin.last m ∉ S.map Fin.castSuccEmb := by
  simp only [Finset.mem_map, not_exists, not_and]
  intro a _ h
  exact (Fin.castSucc_lt_last a).ne h

/- English proof (translation)
Unfold `qr_ext`. Apply the tactic sequence `split_ifs <;> simp [(Fin.castSucc_lt_last a).ne]`.
-/
lemma qr_mem_castSucc (a : Fin m) : a.castSucc ∈ qr_ext e S ↔ a ∈ S := by
  unfold qr_ext
  split_ifs <;> simp [(Fin.castSucc_lt_last a).ne]

/- English proof (translation)
Unfold `qr_ext`. Use `split_ifs with h`. Simplify using `[h]`. Simplify using `only [h, iff_false]`. Conclude with `qr_last_notMem S`.
-/
lemma qr_mem_last : Fin.last m ∈ qr_ext e S ↔ e := by
  unfold qr_ext
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]; exact qr_last_notMem S

/- English proof (translation)
Unfold `qr_ext`. Use `split_ifs with h`. Rewrite using `[Finset.card_insert_of_notMem (qr_last_notMem S), Finset.card_map]`. Rewrite using `[Finset.card_map]`. Both sides reduce to the same expression.
-/
lemma qr_ext_card : (qr_ext e S).card = S.card + if e then 1 else 0 := by
  unfold qr_ext
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (qr_last_notMem S), Finset.card_map]
  · rw [Finset.card_map]; rfl

/- English proof (translation)
Use extensionality with `a`. Rewrite using `[← qr_mem_castSucc e S a, h, qr_mem_castSucc]`.
-/
lemma qr_ext_inj {S S' : Finset (Fin m)} (h : qr_ext e S = qr_ext e S') : S = S' := by
  ext a
  rw [← qr_mem_castSucc e S a, h, qr_mem_castSucc]

/- English proof (translation)
Use extensionality with `x`. Proceed by induction on `x using Fin.lastCases with`. Consider the case `last => rw [qr_mem_last, h]`. Consider the case `cast a => rw [qr_mem_castSucc]`. Simplify using the standard rewrite rules.
-/
lemma qr_ext_surj (K : Finset (Fin (m + 1))) (h : Fin.last m ∈ K ↔ e) :
    K = qr_ext e (univ.filter fun a : Fin m => a.castSucc ∈ K) := by
  ext x
  induction x using Fin.lastCases with
  | last => rw [qr_mem_last, h]
  | cast a => rw [qr_mem_castSucc]; simp

/- English proof (translation)
Use extensionality with `x`. Proceed by induction on `x using Fin.lastCases with`. Consider the case `last`. Simplify using `only [Finset.mem_filter, Finset.mem_map]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨_, h⟩`. Conclude with `absurd h (not_le.2 (Fin.castSucc_lt_last t))`. Introduce and unpack `⟨a, _, h⟩`. Conclude with `absurd h (Fin.castSucc_lt_last a).ne`. Consider the case `cast a`.

Simplify using `only [Finset.mem_filter, qr_mem_castSucc, Finset.mem_map, Fin.castSuccEmb_apply, Fin.castSucc_inj, exists_eq_right, Fin.castSucc_le_castSucc_iff]`.
-/
lemma qr_filter_castSucc (t : Fin m) :
    ((qr_ext e S).filter (· ≤ t.castSucc)) = (S.filter (· ≤ t)).map Fin.castSuccEmb := by
  ext x
  induction x using Fin.lastCases with
  | last =>
    simp only [Finset.mem_filter, Finset.mem_map]
    constructor
    · rintro ⟨_, h⟩; exact absurd h (not_le.2 (Fin.castSucc_lt_last t))
    · rintro ⟨a, _, h⟩; exact absurd h (Fin.castSucc_lt_last a).ne
  | cast a =>
    simp only [Finset.mem_filter, qr_mem_castSucc, Finset.mem_map, Fin.castSuccEmb_apply, Fin.castSucc_inj,
      exists_eq_right, Fin.castSucc_le_castSucc_iff]

/- English proof (translation)
Apply `Finset.filter_true_of_mem` to reduce the goal to its premises. Introduce `x _`. Conclude with `Fin.le_last x`.
-/
lemma qr_filter_last : ((qr_ext e S).filter (· ≤ Fin.last m)) = qr_ext e S := by
  apply Finset.filter_true_of_mem
  intro x _; exact Fin.le_last x

/- English proof (translation)
Use `symm`. Apply `Finset.orderEmbOfFin_unique` to reduce the goal to its premises. Introduce `a`. Simplify using `[Finset.orderEmbOfFin_mem]`. Introduce `a b hab`.

Conclude with `Fin.castSucc_lt_castSucc_iff.2 ((S.orderEmbOfFin h).strictMono hab)`.
-/
lemma qr_emb_map {k : ℕ} (h : S.card = k) (h' : (S.map Fin.castSuccEmb).card = k) :
    ⇑((S.map Fin.castSuccEmb).orderEmbOfFin h') = fun a => (S.orderEmbOfFin h a).castSucc := by
  symm
  apply Finset.orderEmbOfFin_unique
  · intro a; simp [Finset.orderEmbOfFin_mem]
  · intro a b hab
    exact Fin.castSucc_lt_castSucc_iff.2 ((S.orderEmbOfFin h).strictMono hab)

/- English proof (translation)
Use `symm`. Apply `Finset.orderEmbOfFin_unique` to reduce the goal to its premises. Introduce `a`. Proceed by induction on `a using Fin.lastCases with`. Consider the case `last => simp`.

Consider the case `cast a => simp [Finset.orderEmbOfFin_mem]`. Introduce `a b hab`. Proceed by induction on `b using Fin.lastCases with`. Consider the case `last`. Proceed by induction on `a using Fin.lastCases with`.

Consider the case `last => exact absurd hab (lt_irrefl _)`. Consider the case `cast a => simp only [Fin.snoc_castSucc, Fin.snoc_last]`. Conclude with `Fin.castSucc_lt_last _`. Consider the case `cast b`. Proceed by induction on `a using Fin.lastCases with`.

Consider the case `last => exact absurd hab (not_lt.2 (Fin.le_last _))`. Consider the case `cast a`. Simplify using `only [Fin.snoc_castSucc]`. Conclude with `Fin.castSucc_lt_castSucc_iff.2 ((S.orderEmbOfFin h).strictMono (Fin.castSucc_lt_castSucc_iff.1 hab))`.
-/
lemma qr_emb_insert {k : ℕ} (h : S.card = k) (h' : (insert (Fin.last m) (S.map Fin.castSuccEmb)).card = k + 1) :
    ⇑((insert (Fin.last m) (S.map Fin.castSuccEmb)).orderEmbOfFin h') =
      Fin.snoc (α := fun _ => Fin (m + 1)) (fun a => (S.orderEmbOfFin h a).castSucc) (Fin.last m) := by
  symm
  apply Finset.orderEmbOfFin_unique
  · intro a
    induction a using Fin.lastCases with
    | last => simp
    | cast a => simp [Finset.orderEmbOfFin_mem]
  · intro a b hab
    induction b using Fin.lastCases with
    | last =>
      induction a using Fin.lastCases with
      | last => exact absurd hab (lt_irrefl _)
      | cast a => simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Fin.castSucc_lt_last _
    | cast b =>
      induction a using Fin.lastCases with
      | last => exact absurd hab (not_lt.2 (Fin.le_last _))
      | cast a =>
        simp only [Fin.snoc_castSucc]
        exact Fin.castSucc_lt_castSucc_iff.2 ((S.orderEmbOfFin h).strictMono (Fin.castSucc_lt_castSucc_iff.1 hab))

end Ext

section Block

variable {m : ℕ} {R : Type} [CommRing R] {h : GL (Fin (m + 1)) R} {g1 : GL (Fin m) R} {t : Rˣ}

/- English proof (translation)
Use `congr 1`. Use extensionality with `a b`. Conclude with `hb.1 _ _`.
-/
lemma qr_det_cast (hb : IsBlock h g1 t) {k : ℕ} (r c : Fin k → Fin m) :
    (h.val.submatrix (fun a => (r a).castSucc) (fun a => (c a).castSucc)).det = (g1.val.submatrix r c).det := by
  congr 1
  ext a b
  exact hb.1 _ _

/- English proof (translation)
Rewrite using `[Matrix.det_succ_row _ (Fin.last k), Finset.sum_eq_single (Fin.last k)]`. Establish `h1 : ((h.val.submatrix (Fin.snoc (α` using `fun _ => Fin (m + 1)) (fun a => (r a).castSucc) (Fin.last m)) (Fin.snoc (α := fun _ => Fin (m + 1)) (fun a => (c a).castSucc) (Fin.last m))).submatrix (Fin.last k).succAbove (Fin.last k).succAbove) = g1.val.submatrix r c := by`. Use extensionality with `a b`. Simplify using `[Fin.succAbove_last, hb.1]`. Rewrite using `[h1]`.

Simplify using `[hb.2.1, ← two_mul]`. Introduce `j _ hj`. Take `⟨j', rfl⟩` from `Fin.exists_castSucc_eq.2 hj`. Simplify using `[(hb.2.2 _).2]`. Simplify using the standard rewrite rules.
-/
lemma qr_det_snoc (hb : IsBlock h g1 t) {k : ℕ} (r c : Fin k → Fin m) :
    (h.val.submatrix (Fin.snoc (α := fun _ => Fin (m + 1)) (fun a => (r a).castSucc) (Fin.last m))
      (Fin.snoc (α := fun _ => Fin (m + 1)) (fun a => (c a).castSucc) (Fin.last m))).det =
      (t : R) * (g1.val.submatrix r c).det := by
  rw [Matrix.det_succ_row _ (Fin.last k), Finset.sum_eq_single (Fin.last k)]
  · have h1 : ((h.val.submatrix (Fin.snoc (α := fun _ => Fin (m + 1)) (fun a => (r a).castSucc) (Fin.last m))
      (Fin.snoc (α := fun _ => Fin (m + 1)) (fun a => (c a).castSucc) (Fin.last m))).submatrix
        (Fin.last k).succAbove (Fin.last k).succAbove) = g1.val.submatrix r c := by
      ext a b
      simp [Fin.succAbove_last, hb.1]
    rw [h1]
    simp [hb.2.1, ← two_mul]
  · intro j _ hj
    obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.2 hj
    simp [(hb.2.2 _).2]
  · simp

/- English proof (translation)
Use `qr_det_snoc hb (id : Fin m → Fin m) id` as an intermediate fact. Establish `h1 : (Fin.snoc (α` using `fun _ => Fin (m + 1)) (fun a : Fin m => (id a).castSucc) (Fin.last m)) = id := by`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `induction a using Fin.lastCases <;> simp`. Rewrite `this` using `[h1]`.

Simplify using `using this`.
-/
lemma qr_det_block (hb : IsBlock h g1 t) : h.val.det = (t : R) * g1.val.det := by
  have := qr_det_snoc hb (id : Fin m → Fin m) id
  have h1 : (Fin.snoc (α := fun _ => Fin (m + 1)) (fun a : Fin m => (id a).castSucc) (Fin.last m)) = id := by
    funext a
    induction a using Fin.lastCases <;> simp
  rw [h1] at this
  simpa using this

/- English proof (translation)
Distinguish the cases in `he : e`. Establish `hk : k = k' + 1` using `by rw [← hK, qr_ext_card, hK', if_pos he]`. Substitute `hk` using the available equality. Establish `key : ∀ (A B : Finset (Fin (m + 1))) (hA : A.card = k' + 1) (hB : B.card = k' + 1), A = insert (Fin.last m) (K'.map Fin.castSuccEmb) → B = insert (Fin.last m) (S.map Fin.castSuccEmb) → (h.val.submatrix (A.orderEmbOfFin hA) (B.orderEmbOfFin hB)).det = (t : R) * (g1.val.submatrix ( …`. Introduce `A B hA hB eA eB`.

Substitute `eA eB` using the available equality. Rewrite using `[qr_emb_insert K' hK', qr_emb_insert S hS', qr_det_snoc hb]`. Rewrite using `[if_pos he]`. Conclude with `key _ _ hK hS (by rw [qr_ext, if_pos he]) (by rw [qr_ext, if_pos he])`. Establish `hk : k = k'` using `by rw [← hK, qr_ext_card, hK', if_neg he]; rfl`.

Substitute `hk` using the available equality. Establish `key : ∀ (A B : Finset (Fin (m + 1))) (hA : A.card = k) (hB : B.card = k), A = K'.map Fin.castSuccEmb → B = S.map Fin.castSuccEmb → (h.val.submatrix (A.orderEmbOfFin hA) (B.orderEmbOfFin hB)).det = (g1.val.submatrix (K'.orderEmbOfFin hK') (S.orderEmbOfFin hS')).det`. Introduce `A B hA hB eA eB`. Substitute `eA eB` using the available equality. Rewrite using `[qr_emb_map K' hK', qr_emb_map S hS', qr_det_cast hb]`.

Rewrite using `[if_neg he, one_mul]`. Conclude with `key _ _ hK hS (by rw [qr_ext, if_neg he]) (by rw [qr_ext, if_neg he])`.
-/
lemma qr_minor_ext (hb : IsBlock h g1 t) (e : Prop) [Decidable e] (K' S : Finset (Fin m)) {k k' : ℕ}
    (hK' : K'.card = k') (hS' : S.card = k') (hK : (qr_ext e K').card = k) (hS : (qr_ext e S).card = k) :
    (h.val.submatrix ((qr_ext e K').orderEmbOfFin hK) ((qr_ext e S).orderEmbOfFin hS)).det =
      (if e then (t : R) else 1) * (g1.val.submatrix (K'.orderEmbOfFin hK') (S.orderEmbOfFin hS')).det := by
  by_cases he : e
  · have hk : k = k' + 1 := by rw [← hK, qr_ext_card, hK', if_pos he]
    subst hk
    have key : ∀ (A B : Finset (Fin (m + 1))) (hA : A.card = k' + 1) (hB : B.card = k' + 1),
        A = insert (Fin.last m) (K'.map Fin.castSuccEmb) → B = insert (Fin.last m) (S.map Fin.castSuccEmb) →
        (h.val.submatrix (A.orderEmbOfFin hA) (B.orderEmbOfFin hB)).det =
          (t : R) * (g1.val.submatrix (K'.orderEmbOfFin hK') (S.orderEmbOfFin hS')).det := by
      intro A B hA hB eA eB
      subst eA eB
      rw [qr_emb_insert K' hK', qr_emb_insert S hS', qr_det_snoc hb]
    rw [if_pos he]
    exact key _ _ hK hS (by rw [qr_ext, if_pos he]) (by rw [qr_ext, if_pos he])
  · have hk : k = k' := by rw [← hK, qr_ext_card, hK', if_neg he]; rfl
    subst hk
    have key : ∀ (A B : Finset (Fin (m + 1))) (hA : A.card = k) (hB : B.card = k),
        A = K'.map Fin.castSuccEmb → B = S.map Fin.castSuccEmb →
        (h.val.submatrix (A.orderEmbOfFin hA) (B.orderEmbOfFin hB)).det =
          (g1.val.submatrix (K'.orderEmbOfFin hK') (S.orderEmbOfFin hS')).det := by
      intro A B hA hB eA eB
      subst eA eB
      rw [qr_emb_map K' hK', qr_emb_map S hS', qr_det_cast hb]
    rw [if_neg he, one_mul]
    exact key _ _ hK hS (by rw [qr_ext, if_neg he]) (by rw [qr_ext, if_neg he])

/- English proof (translation)
Distinguish the cases in `he : e`. Establish `hl : Fin.last m ∉ K` using `fun hl => hne ⟨fun _ => he, fun _ => hl⟩`. Establish `h1 : Fin.last m ∈ Set.range ((qr_ext e S).orderEmbOfFin hS)`. Rewrite using `[Finset.range_orderEmbOfFin]`. Conclude with `(qr_mem_last e S).2 he`.

Take `⟨b0, hb0⟩` from `h1`. Apply `Matrix.det_eq_zero_of_column_eq_zero b0` to reduce the goal to its premises. Introduce `a`. Rewrite using `[Matrix.submatrix_apply, hb0]`. Establish `h2 : K.orderEmbOfFin hK a ≠ Fin.last m` using `fun h3 => hl (h3 ▸ Finset.orderEmbOfFin_mem K hK a)`.

Take `⟨a', ha'⟩` from `Fin.exists_castSucc_eq.2 h2`. Rewrite using `[← ha']`. Conclude with `(hb.2.2 a').1`. Establish `hl : Fin.last m ∈ K`. Assume the negation of the conclusion as `hl`.

Conclude with `hne ⟨fun h => absurd h hl, fun h => absurd h he⟩`. Establish `h1 : Fin.last m ∈ Set.range (K.orderEmbOfFin hK)`. Rewrite using `[Finset.range_orderEmbOfFin]`. Conclude with `hl`. Take `⟨a0, ha0⟩` from `h1`.

Apply `Matrix.det_eq_zero_of_row_eq_zero a0` to reduce the goal to its premises. Introduce `b`. Rewrite using `[Matrix.submatrix_apply, ha0]`. Establish `h2 : (qr_ext e S).orderEmbOfFin hS b ≠ Fin.last m` using `fun h3 => he ((qr_mem_last e S).1 (h3 ▸ Finset.orderEmbOfFin_mem _ hS b))`. Take `⟨b', hb'⟩` from `Fin.exists_castSucc_eq.2 h2`.

Rewrite using `[← hb']`. Conclude with `(hb.2.2 b').2`.
-/
lemma qr_minor_zero (hb : IsBlock h g1 t) (e : Prop) [Decidable e] (K : Finset (Fin (m + 1))) (S : Finset (Fin m))
    {k : ℕ} (hK : K.card = k) (hS : (qr_ext e S).card = k) (hne : ¬ (Fin.last m ∈ K ↔ e)) :
    (h.val.submatrix (K.orderEmbOfFin hK) ((qr_ext e S).orderEmbOfFin hS)).det = 0 := by
  by_cases he : e
  · have hl : Fin.last m ∉ K := fun hl => hne ⟨fun _ => he, fun _ => hl⟩
    have h1 : Fin.last m ∈ Set.range ((qr_ext e S).orderEmbOfFin hS) := by
      rw [Finset.range_orderEmbOfFin]; exact (qr_mem_last e S).2 he
    obtain ⟨b0, hb0⟩ := h1
    apply Matrix.det_eq_zero_of_column_eq_zero b0
    intro a
    rw [Matrix.submatrix_apply, hb0]
    have h2 : K.orderEmbOfFin hK a ≠ Fin.last m := fun h3 => hl (h3 ▸ Finset.orderEmbOfFin_mem K hK a)
    obtain ⟨a', ha'⟩ := Fin.exists_castSucc_eq.2 h2
    rw [← ha']
    exact (hb.2.2 a').1
  · have hl : Fin.last m ∈ K := by
      by_contra hl; exact hne ⟨fun h => absurd h hl, fun h => absurd h he⟩
    have h1 : Fin.last m ∈ Set.range (K.orderEmbOfFin hK) := by
      rw [Finset.range_orderEmbOfFin]; exact hl
    obtain ⟨a0, ha0⟩ := h1
    apply Matrix.det_eq_zero_of_row_eq_zero a0
    intro b
    rw [Matrix.submatrix_apply, ha0]
    have h2 : (qr_ext e S).orderEmbOfFin hS b ≠ Fin.last m := fun h3 =>
      he ((qr_mem_last e S).1 (h3 ▸ Finset.orderEmbOfFin_mem _ hS b))
    obtain ⟨b', hb'⟩ := Fin.exists_castSucc_eq.2 h2
    rw [← hb']
    exact (hb.2.2 b').2

end Block

end Formalism.InvariantFactorPaths.ColumnFamilies
