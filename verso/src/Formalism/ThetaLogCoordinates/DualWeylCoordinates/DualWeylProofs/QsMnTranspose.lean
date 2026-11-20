import Formalism.ThetaLogCoordinates.DualWeylCoordinates.StripDataTensorColumnFamilies

noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

def qs_sg (A : Finset (Fin n)) (m : Fin n) : ℤ := (-1) ^ (A.filter (m < ·)).card

def qs_mn {R : Type*} [CommRing R] (g : Matrix (Fin n) (Fin n) R) (J I : Finset (Fin n)) : R :=
  if h : J.card = I.card then
    Matrix.det (Matrix.of fun a b : Fin I.card => g (J.orderEmbOfFin h a) (I.orderEmbOfFin rfl b)) else 0

variable {R : Type*} [CommRing R] (g : Matrix (Fin n) (Fin n) R)

/- English proof (translation)
Substitute `hI` using the available equality. Rewrite using `[qs_mn, dif_pos hJ]`.
-/
lemma qs_mn_eq {h : ℕ} (J I : Finset (Fin n)) (hJ : J.card = h) (hI : I.card = h) :
    qs_mn g J I = Matrix.det (Matrix.of fun a b : Fin h => g (J.orderEmbOfFin hJ a) (I.orderEmbOfFin hI b)) := by
  subst hI; rw [qs_mn, dif_pos hJ]

/- English proof (translation)
The claim follows from `dif_neg h`.
-/
lemma qs_mn_ne {J I : Finset (Fin n)} (h : J.card ≠ I.card) : qs_mn g J I = 0 := dif_neg h

/- English proof (translation)
Distinguish the cases in `h : J.card = I.card`. Rewrite using `[qs_mn_eq _ J I h rfl, qs_mn_eq _ I J rfl h, ← Matrix.det_transpose]`. Both sides reduce to the same expression. Rewrite using `[qs_mn_ne _ h, qs_mn_ne _ (Ne.symm h)]`.
-/
lemma qs_mn_transpose (J I : Finset (Fin n)) : qs_mn g.transpose J I = qs_mn g I J := by
  by_cases h : J.card = I.card
  · rw [qs_mn_eq _ J I h rfl, qs_mn_eq _ I J rfl h, ← Matrix.det_transpose]; rfl
  · rw [qs_mn_ne _ h, qs_mn_ne _ (Ne.symm h)]

/- English proof (translation)
Use `Finset.orderEmbOfFin_unique hs' (f := fun i => s.orderEmbOfFin hs (j.succAbove i)) (fun x => Finset.mem_erase.2 ⟨(s.orderEmbOfFin hs).injective.ne (Fin.succAbove_ne j x), Finset.orderEmbOfFin_mem _ _ _⟩) ((s.orderEmbOfFin hs).strictMono.comp (Fin.strictMono_succAbove j))` as an intermediate fact. Conclude with `congrFun this i`.
-/
lemma qs_oe_succAbove {h : ℕ} (s : Finset (Fin n)) (hs : s.card = h + 1) (j : Fin (h + 1))
    (hs' : (s.erase (s.orderEmbOfFin hs j)).card = h) (i : Fin h) :
    s.orderEmbOfFin hs (j.succAbove i) = (s.erase (s.orderEmbOfFin hs j)).orderEmbOfFin hs' i := by
  have := Finset.orderEmbOfFin_unique hs' (f := fun i => s.orderEmbOfFin hs (j.succAbove i))
    (fun x => Finset.mem_erase.2 ⟨(s.orderEmbOfFin hs).injective.ne (Fin.succAbove_ne j x),
      Finset.orderEmbOfFin_mem _ _ _⟩)
    ((s.orderEmbOfFin hs).strictMono.comp (Fin.strictMono_succAbove j))
  exact congrFun this i

/- English proof (translation)
Establish `: (s.erase (s.orderEmbOfFin hs j)).filter (s.orderEmbOfFin hs j < ·) = (Finset.Ioi j).map (s.orderEmbOfFin hs).toEmbedding`. Use extensionality with `x`. Simplify using `only [mem_filter, mem_erase, mem_map, mem_Ioi, RelEmbedding.coe_toEmbedding]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨_, hx⟩, hlt⟩`.

Establish `hx' : x ∈ Set.range (s.orderEmbOfFin hs)` using `by rw [Finset.range_orderEmbOfFin]; exact hx`. Take `⟨i, rfl⟩` from `hx'`. Conclude with `⟨i, (s.orderEmbOfFin hs).lt_iff_lt.1 hlt, rfl⟩`. Introduce and unpack `⟨i, hi, rfl⟩`. Conclude with `⟨⟨((s.orderEmbOfFin hs).lt_iff_lt.2 hi).ne', Finset.orderEmbOfFin_mem _ _ _⟩, (s.orderEmbOfFin hs).lt_iff_lt.2 hi⟩`.

Rewrite using `[this, card_map, Fin.card_Ioi]`. Use linear arithmetic over natural numbers and integers.
-/
lemma qs_card_gt {h : ℕ} (s : Finset (Fin n)) (hs : s.card = h + 1) (j : Fin (h + 1)) :
    ((s.erase (s.orderEmbOfFin hs j)).filter (s.orderEmbOfFin hs j < ·)).card = h - j := by
  have : (s.erase (s.orderEmbOfFin hs j)).filter (s.orderEmbOfFin hs j < ·) =
      (Finset.Ioi j).map (s.orderEmbOfFin hs).toEmbedding := by
    ext x
    simp only [mem_filter, mem_erase, mem_map, mem_Ioi, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨⟨_, hx⟩, hlt⟩
      have hx' : x ∈ Set.range (s.orderEmbOfFin hs) := by rw [Finset.range_orderEmbOfFin]; exact hx
      obtain ⟨i, rfl⟩ := hx'
      exact ⟨i, (s.orderEmbOfFin hs).lt_iff_lt.1 hlt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨((s.orderEmbOfFin hs).lt_iff_lt.2 hi).ne', Finset.orderEmbOfFin_mem _ _ _⟩,
        (s.orderEmbOfFin hs).lt_iff_lt.2 hi⟩
  rw [this, card_map, Fin.card_Ioi]; omega

/- English proof (translation)
Use `conv_lhs => rw [← Finset.map_orderEmbOfFin_univ I hI]`. Rewrite using `[Finset.sum_map]`. Both sides reduce to the same expression.
-/
lemma qs_sum_oe {M : Type*} [AddCommMonoid M] {h : ℕ} (I : Finset (Fin n)) (hI : I.card = h) (f : Fin n → M) :
    ∑ m ∈ I, f m = ∑ j : Fin h, f (I.orderEmbOfFin hI j) := by
  conv_lhs => rw [← Finset.map_orderEmbOfFin_univ I hI]
  rw [Finset.sum_map]; rfl

/- English proof (translation)
Rewrite using `[Matrix.det_succ_row _ p, Finset.mul_sum, qs_sum_oe I hI]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `hc : (I.erase (I.orderEmbOfFin hI j)).card = h`. Rewrite using `[Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem _ _ _), hI]`. Both sides reduce to the same expression.

Rewrite using `[qs_mn_eq g A _ hA hc, qs_sg, qs_card_gt I hI j]`. Establish `hM : (Matrix.of fun a b : Fin (h + 1) => g (r a) (I.orderEmbOfFin hI b)).submatrix p.succAbove j.succAbove = Matrix.of fun a b : Fin h => g (A.orderEmbOfFin hA a) ((I.erase (I.orderEmbOfFin hI j)).orderEmbOfFin hc b)`. Use extensionality with `a b`. Simplify using `only [Matrix.submatrix_apply, Matrix.of_apply]`. Rewrite using `[hr, qs_oe_succAbove I hI j hc]`.

Rewrite using `[hM]`. Establish `hs : ((-1 : R)) ^ (h - (j : ℕ)) = (-1) ^ (h - (p : ℕ)) * (-1) ^ ((p : ℕ) + (j : ℕ))`. Rewrite using `[← pow_add]`. Establish `hj` using `j.2`. Establish `hp` using `p.2`.

Establish `: h - (p : ℕ) + ((p : ℕ) + (j : ℕ)) = (h - (j : ℕ)) + 2 * (j : ℕ)` using `by omega`. Rewrite using `[this, pow_add, pow_mul]`. Simplify using the standard rewrite rules. Use `push_cast`. Rewrite using `[hs]`.

Simplify using `only [Matrix.of_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma qs_lap_row {h : ℕ} (r : Fin (h + 1) → Fin n) (p : Fin (h + 1)) (I : Finset (Fin n)) (hI : I.card = h + 1)
    (A : Finset (Fin n)) (hA : A.card = h) (hr : ∀ i, r (p.succAbove i) = A.orderEmbOfFin hA i) :
    ∑ m ∈ I, ((qs_sg (I.erase m) m : ℤ) : R) * qs_mn g A (I.erase m) * g (r p) m =
      (-1) ^ (h - (p : ℕ)) * Matrix.det (Matrix.of fun a b : Fin (h + 1) => g (r a) (I.orderEmbOfFin hI b)) := by
  rw [Matrix.det_succ_row _ p, Finset.mul_sum, qs_sum_oe I hI]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : (I.erase (I.orderEmbOfFin hI j)).card = h := by
    rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem _ _ _), hI]; rfl
  rw [qs_mn_eq g A _ hA hc, qs_sg, qs_card_gt I hI j]
  have hM : (Matrix.of fun a b : Fin (h + 1) => g (r a) (I.orderEmbOfFin hI b)).submatrix p.succAbove j.succAbove =
      Matrix.of fun a b : Fin h => g (A.orderEmbOfFin hA a) ((I.erase (I.orderEmbOfFin hI j)).orderEmbOfFin hc b) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.of_apply]
    rw [hr, qs_oe_succAbove I hI j hc]
  rw [hM]
  have hs : ((-1 : R)) ^ (h - (j : ℕ)) = (-1) ^ (h - (p : ℕ)) * (-1) ^ ((p : ℕ) + (j : ℕ)) := by
    rw [← pow_add]
    have hj := j.2; have hp := p.2
    have : h - (p : ℕ) + ((p : ℕ) + (j : ℕ)) = (h - (j : ℕ)) + 2 * (j : ℕ) := by omega
    rw [this, pow_add, pow_mul]; simp
  push_cast
  rw [hs]
  simp only [Matrix.of_apply]
  ring

/- English proof (translation)
Distinguish the cases in `hc : I.card = A.card + 1`. Use `split_ifs with hk`. Establish `hk' : k ∈ Set.range (A.orderEmbOfFin rfl)` using `by rw [Finset.range_orderEmbOfFin]; exact hk`. Take `⟨q, hq⟩` from `hk'`. Use `qs_lap_row g (Fin.cons k (A.orderEmbOfFin rfl)) 0 I hc A rfl (fun i => by simp)` as an intermediate fact.

Simplify using `only [Fin.cons_zero] at this`. Rewrite using `[this, Matrix.det_zero_of_row_eq (i := 0) (j := q.succ) (Fin.succ_ne_zero q).symm, mul_zero]`. Use extensionality with `b`. Simplify using `[hq]`. Establish `hs : (insert k A).card = A.card + 1` using `Finset.card_insert_of_notMem hk`.

Establish `hk' : k ∈ Set.range ((insert k A).orderEmbOfFin hs)`. Rewrite using `[Finset.range_orderEmbOfFin]`. Simplify using the standard rewrite rules. Take `⟨p, hp⟩` from `hk'`. Establish `he : (insert k A).erase ((insert k A).orderEmbOfFin hs p) = A`.

Rewrite using `[hp, Finset.erase_insert hk]`. Establish `hAc : ((insert k A).erase ((insert k A).orderEmbOfFin hs p)).card = A.card` using `by rw [he]`. Use `qs_lap_row g ((insert k A).orderEmbOfFin hs) p I hc _ hAc (fun i => qs_oe_succAbove _ hs p hAc i)` as an intermediate fact. Establish `h2` using `qs_card_gt (insert k A) hs p`. Rewrite `this`, `h2` using `[he, hp]`.

Rewrite using `[this, qs_mn_eq g _ _ hs hc, qs_sg, h2]`. Use `push_cast`. Both sides reduce to the same expression. Establish `h1 : ∀ m ∈ I, qs_mn g A (I.erase m) = 0` using `fun m hm => qs_mn_ne g (by`. Rewrite using `[Finset.card_erase_of_mem hm]`.

Use `Finset.card_pos.2 ⟨m, hm⟩` as an intermediate fact. Use the proof step `omega)`. Rewrite using `[Finset.sum_eq_zero (fun m hm => by rw [h1 m hm]; simp)]`. Use `split_ifs with hk`. Both sides reduce to the same expression.

Rewrite using `[qs_mn_ne g (by rw [Finset.card_insert_of_notMem hk]; omega), mul_zero]`.
-/
theorem qs_laplace (A I : Finset (Fin n)) (k : Fin n) :
    ∑ m ∈ I, ((qs_sg (I.erase m) m : ℤ) : R) * qs_mn g A (I.erase m) * g k m =
      if k ∈ A then 0 else ((qs_sg A k : ℤ) : R) * qs_mn g (insert k A) I := by
  by_cases hc : I.card = A.card + 1
  · split_ifs with hk
    ·
      have hk' : k ∈ Set.range (A.orderEmbOfFin rfl) := by rw [Finset.range_orderEmbOfFin]; exact hk
      obtain ⟨q, hq⟩ := hk'
      have := qs_lap_row g (Fin.cons k (A.orderEmbOfFin rfl)) 0 I hc A rfl (fun i => by simp)
      simp only [Fin.cons_zero] at this
      rw [this, Matrix.det_zero_of_row_eq (i := 0) (j := q.succ) (Fin.succ_ne_zero q).symm, mul_zero]
      ext b; simp [hq]
    · have hs : (insert k A).card = A.card + 1 := Finset.card_insert_of_notMem hk
      have hk' : k ∈ Set.range ((insert k A).orderEmbOfFin hs) := by
        rw [Finset.range_orderEmbOfFin]; simp
      obtain ⟨p, hp⟩ := hk'
      have he : (insert k A).erase ((insert k A).orderEmbOfFin hs p) = A := by
        rw [hp, Finset.erase_insert hk]
      have hAc : ((insert k A).erase ((insert k A).orderEmbOfFin hs p)).card = A.card := by rw [he]
      have := qs_lap_row g ((insert k A).orderEmbOfFin hs) p I hc _ hAc
        (fun i => qs_oe_succAbove _ hs p hAc i)
      have h2 := qs_card_gt (insert k A) hs p
      rw [he, hp] at this h2
      rw [this, qs_mn_eq g _ _ hs hc, qs_sg, h2]
      push_cast; rfl
  · have h1 : ∀ m ∈ I, qs_mn g A (I.erase m) = 0 := fun m hm => qs_mn_ne g (by
      rw [Finset.card_erase_of_mem hm]
      have := Finset.card_pos.2 ⟨m, hm⟩
      omega)
    rw [Finset.sum_eq_zero (fun m hm => by rw [h1 m hm]; simp)]
    split_ifs with hk
    · rfl
    · rw [qs_mn_ne g (by rw [Finset.card_insert_of_notMem hk]; omega), mul_zero]

/- English proof (translation)
Use `qs_laplace g.transpose I A m` as an intermediate fact. Simplify `this` using `only [qs_mn_transpose, Matrix.transpose_apply]`.
-/
theorem qs_laplace_col (A I : Finset (Fin n)) (m : Fin n) :
    ∑ k ∈ A, ((qs_sg (A.erase k) k : ℤ) : R) * qs_mn g (A.erase k) I * g k m =
      if m ∈ I then 0 else ((qs_sg I m : ℤ) : R) * qs_mn g A (insert m I) := by
  have := qs_laplace g.transpose I A m
  simpa only [qs_mn_transpose, Matrix.transpose_apply] using this

end Formalism.InvariantFactorPaths.ColumnFamilies
