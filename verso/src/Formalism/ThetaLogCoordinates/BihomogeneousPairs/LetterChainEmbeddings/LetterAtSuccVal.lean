import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.SmulMemOfNorm

namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M

section block
variable {N r : ℕ} (D : BlockData N)

def wv (i : Fin D.T.t) (c : Fin r) : BVar N r D.T.t := Sum.inl (finPos N (D.T.pos i), c)
def ev (i : Fin D.T.t) (c : Fin r) : BVar N r D.T.t := Sum.inl (finPos N (D.T.pos i + 1), c)
def zi (r : ℕ) (i : Fin D.T.t) : BVar N r D.T.t := scalZ N r D.T.t (Fin.castSucc i)
def si (r : ℕ) (i : Fin D.T.t) : BVar N r D.T.t := scalS N r D.T.t (Fin.castSucc i)
def wU (c : Fin r) : BVar N r D.T.t := Sum.inl (Fin.castSucc D.uPos, c)
def zP (r : ℕ) : BVar N r D.T.t := scalZ N r D.T.t (Fin.last D.T.t)
def sP (r : ℕ) : BVar N r D.T.t := scalS N r D.T.t (Fin.last D.T.t)

variable {D}

/- English proof (translation)
Take `⟨_, h2, _, h4⟩` from `hB`. Use `h2 i` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem pos_succ_lt (hB : D.BlockOK) (i : Fin D.T.t) : D.T.pos i + 1 + 1 < N := by
  obtain ⟨_, h2, _, h4⟩ := hB
  have := h2 i
  omega

/- English proof (translation)
Use `pos_succ_lt hB i` as an intermediate fact. Use `show min (D.T.pos i) N = D.T.pos i`. Use linear arithmetic over natural numbers and integers.
-/
theorem finPos_pos_val (hB : D.BlockOK) (i : Fin D.T.t) : (finPos N (D.T.pos i)).val = D.T.pos i := by
  have := pos_succ_lt hB i
  show min (D.T.pos i) N = D.T.pos i
  omega

/- English proof (translation)
Use `pos_succ_lt hB i` as an intermediate fact. Use `show min (D.T.pos i + 1) N = D.T.pos i + 1`. Use linear arithmetic over natural numbers and integers.
-/
theorem finPos_succ_val (hB : D.BlockOK) (i : Fin D.T.t) :
    (finPos N (D.T.pos i + 1)).val = D.T.pos i + 1 := by
  have := pos_succ_lt hB i
  show min (D.T.pos i + 1) N = D.T.pos i + 1
  omega

/- English proof (translation)
Use `pos_succ_lt hB i` as an intermediate fact. Use `show min (D.T.pos i) (N - 1) = D.T.pos i`. Use linear arithmetic over natural numbers and integers.
-/
theorem letterAt_pos_val (hB : D.BlockOK) (i : Fin D.T.t) : (D.letterAt (D.T.pos i)).val = D.T.pos i := by
  have := pos_succ_lt hB i
  show min (D.T.pos i) (N - 1) = D.T.pos i
  omega

/- English proof (translation)
Use `pos_succ_lt hB i` as an intermediate fact. Use `show min (D.T.pos i + 1) (N - 1) = D.T.pos i + 1`. Use linear arithmetic over natural numbers and integers.
-/
theorem letterAt_succ_val (hB : D.BlockOK) (i : Fin D.T.t) :
    (D.letterAt (D.T.pos i + 1)).val = D.T.pos i + 1 := by
  have := pos_succ_lt hB i
  show min (D.T.pos i + 1) (N - 1) = D.T.pos i + 1
  omega

/- English proof (translation)
The claim follows from `hB.1.1.injective h`.
-/
theorem pos_inj (hB : D.BlockOK) {i i' : Fin D.T.t} (h : D.T.pos i = D.T.pos i') : i = i' := hB.1.1.injective h

/- English proof (translation)
Introduce `h`. Take `⟨hi, hti, _⟩` from `hB.1.2.1 i`. Take `⟨hi', _, hfi'⟩` from `hB.1.2.1 i'`. Establish `e : D.LL.vec ⟨D.T.pos i, by omega⟩ = D.LL.vec ⟨D.T.pos i' + 1, hi'⟩` using `congrArg D.LL.vec (Fin.ext h)`. Rewrite `e` using `[hti, hfi']`.

Conclude with `absurd e (by decide)`.
-/
theorem pos_ne_succ (hB : D.BlockOK) (i i' : Fin D.T.t) : D.T.pos i ≠ D.T.pos i' + 1 := by
  intro h
  obtain ⟨hi, hti, _⟩ := hB.1.2.1 i
  obtain ⟨hi', _, hfi'⟩ := hB.1.2.1 i'
  have e : D.LL.vec ⟨D.T.pos i, by omega⟩ = D.LL.vec ⟨D.T.pos i' + 1, hi'⟩ := congrArg D.LL.vec (Fin.ext h)
  rw [hti, hfi'] at e
  exact absurd e (by decide)

/- English proof (translation)
The claim follows from `hB.2.1 i`.
-/
theorem pos_lt_u (hB : D.BlockOK) (i : Fin D.T.t) : D.T.pos i + 1 < (D.uPos : ℕ) := hB.2.1 i

/- English proof (translation)
Simplify using `only [BlockData.lettersAt]`. Establish `hs : (∑ i', if ((D.letterAt (D.T.pos i) : Fin N) : ℕ) = D.T.pos i' ∨ ((D.letterAt (D.T.pos i) : Fin N) : ℕ) = D.T.pos i' + 1 then j i' else 0) = j i`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using `[letterAt_pos_val hB]`. Introduce `b _ hb`.

Rewrite using `[if_neg]`. Rewrite using `[letterAt_pos_val hB]`. Introduce and unpack `(h | h)`. Conclude with `hb (pos_inj hB h).symm`. Conclude with `pos_ne_succ hB i b h`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Establish `hu : D.letterAt (D.T.pos i) ≠ D.uPos`. Introduce `h`. Establish `h1` using `congrArg Fin.val h`.

Rewrite `h1` using `[letterAt_pos_val hB]`. Use `pos_lt_u hB i` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[hs, if_neg hu, Nat.sub_zero]`.
-/
theorem deg_lettersAt_pos (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t) :
    (D.lettersAt j jp).deg (D.letterAt (D.T.pos i)) = D.LL.deg (D.letterAt (D.T.pos i)) - j i := by
  simp only [BlockData.lettersAt]
  have hs : (∑ i', if ((D.letterAt (D.T.pos i) : Fin N) : ℕ) = D.T.pos i' ∨
      ((D.letterAt (D.T.pos i) : Fin N) : ℕ) = D.T.pos i' + 1 then j i' else 0) = j i := by
    rw [Finset.sum_eq_single i]
    · simp [letterAt_pos_val hB]
    · intro b _ hb
      rw [if_neg]
      rw [letterAt_pos_val hB]
      rintro (h | h)
      · exact hb (pos_inj hB h).symm
      · exact pos_ne_succ hB i b h
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hu : D.letterAt (D.T.pos i) ≠ D.uPos := by
    intro h
    have h1 := congrArg Fin.val h
    rw [letterAt_pos_val hB] at h1
    have := pos_lt_u hB i
    omega
  rw [hs, if_neg hu, Nat.sub_zero]

/- English proof (translation)
Simplify using `only [BlockData.lettersAt]`. Establish `hs : (∑ i', if ((D.letterAt (D.T.pos i + 1) : Fin N) : ℕ) = D.T.pos i' ∨ ((D.letterAt (D.T.pos i + 1) : Fin N) : ℕ) = D.T.pos i' + 1 then j i' else 0) = j i`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using `[letterAt_succ_val hB]`. Introduce `b _ hb`.

Rewrite using `[if_neg]`. Rewrite using `[letterAt_succ_val hB]`. Introduce and unpack `(h | h)`. Conclude with `pos_ne_succ hB b i h.symm`. Conclude with `hb (pos_inj hB (by omega)).symm`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Establish `hu : D.letterAt (D.T.pos i + 1) ≠ D.uPos`. Introduce `h`. Establish `h1` using `congrArg Fin.val h`.

Rewrite `h1` using `[letterAt_succ_val hB]`. Use `pos_lt_u hB i` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[hs, if_neg hu, Nat.sub_zero]`.
-/
theorem deg_lettersAt_pos_succ (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t) :
    (D.lettersAt j jp).deg (D.letterAt (D.T.pos i + 1)) = D.LL.deg (D.letterAt (D.T.pos i + 1)) - j i := by
  simp only [BlockData.lettersAt]
  have hs : (∑ i', if ((D.letterAt (D.T.pos i + 1) : Fin N) : ℕ) = D.T.pos i' ∨
      ((D.letterAt (D.T.pos i + 1) : Fin N) : ℕ) = D.T.pos i' + 1 then j i' else 0) = j i := by
    rw [Finset.sum_eq_single i]
    · simp [letterAt_succ_val hB]
    · intro b _ hb
      rw [if_neg]
      rw [letterAt_succ_val hB]
      rintro (h | h)
      · exact pos_ne_succ hB b i h.symm
      · exact hb (pos_inj hB (by omega)).symm
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hu : D.letterAt (D.T.pos i + 1) ≠ D.uPos := by
    intro h
    have h1 := congrArg Fin.val h
    rw [letterAt_succ_val hB] at h1
    have := pos_lt_u hB i
    omega
  rw [hs, if_neg hu, Nat.sub_zero]

/- English proof (translation)
Simplify using `only [BlockData.lettersAt]`. Rewrite using `[Finset.sum_eq_zero (fun b _ => by`. Rewrite using `[if_neg]`. Use `pos_lt_u hB b` as an intermediate fact. Use the proof step `omega)]`.

Simplify using the standard rewrite rules.
-/
theorem deg_U (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) :
    (D.lettersAt j jp).deg D.uPos = D.LL.deg D.uPos - jp := by
  simp only [BlockData.lettersAt]
  rw [Finset.sum_eq_zero (fun b _ => by
      rw [if_neg]
      have := pos_lt_u hB b
      omega)]
  simp

end block

end Formalism.InvariantFactorPaths.KP.LL
