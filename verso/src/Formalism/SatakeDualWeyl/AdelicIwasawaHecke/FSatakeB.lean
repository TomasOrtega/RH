import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeA

open Formalism.UG

noncomputable section

namespace Formalism.UG.P

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem fSatake_borel_iff (b : GU σ n) :
    IsBorelU b ↔ (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id := Iff.rfl

/- English proof (translation)
Rewrite `hb`, `hb'`, the goal using `[fSatake_borel_iff]`. Simplify `hb.mul hb'` using `only [Subgroup.coe_mul, Units.val_mul]`.
-/
theorem fSatake_borel_mul {b b' : GU σ n} (hb : IsBorelU b) (hb' : IsBorelU b') :
    IsBorelU (b * b') := by
  rw [fSatake_borel_iff] at hb hb' ⊢
  simpa only [Subgroup.coe_mul, Units.val_mul] using hb.mul hb'

/- English proof (translation)
Rewrite `hb`, the goal using `[fSatake_borel_iff]`. Use `haveI : Invertible (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := Units.invertible _`. Use `Matrix.blockTriangular_inv_of_blockTriangular hb` as an intermediate fact. Simplify `this` using `[Matrix.coe_units_inv]`.
-/
theorem fSatake_borel_inv {b : GU σ n} (hb : IsBorelU b) : IsBorelU b⁻¹ := by
  rw [fSatake_borel_iff] at hb ⊢
  haveI : Invertible (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := Units.invertible _
  have := Matrix.blockTriangular_inv_of_blockTriangular hb
  simpa [Matrix.coe_units_inv] using this

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single i]`. Introduce `j _ hj`. Break down `lt_or_gt_of_ne hj with h | h` into its components or cases. Rewrite using `[hM h, zero_mul]`. Rewrite using `[hN h, mul_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.
-/
theorem fSatake_diag_mul {M N : Matrix (Fin n) (Fin n) L} (hM : M.BlockTriangular id)
    (hN : N.BlockTriangular id) (i : Fin n) : (M * N) i i = M i i * N i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hM h, zero_mul]
    · rw [hN h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/- English proof (translation)
Use `fSatake_diag_mul ((fSatake_borel_iff b).1 hb) ((fSatake_borel_iff b').1 hb') i` as an intermediate fact. Simplify `this` using `only [Subgroup.coe_mul, Units.val_mul]`.
-/
theorem fSatake_borel_diag_mul {b b' : GU σ n} (hb : IsBorelU b) (hb' : IsBorelU b') (i : Fin n) :
    (((b * b' : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i =
      (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i *
      (((b' : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i := by
  have := fSatake_diag_mul ((fSatake_borel_iff b).1 hb) ((fSatake_borel_iff b').1 hb') i
  simpa only [Subgroup.coe_mul, Units.val_mul] using this

/- English proof (translation)
Rewrite using `[← fSatake_borel_diag_mul (fSatake_borel_inv hb) hb i]`. Simplify using the standard rewrite rules.
-/
theorem fSatake_borel_diag_inv {b : GU σ n} (hb : IsBorelU b) (i : Fin n) :
    (((b⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i *
      (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 1 := by
  rw [← fSatake_borel_diag_mul (fSatake_borel_inv hb) hb i]
  simp

/- English proof (translation)
Use `k.isLt` as an intermediate fact. Use `l.isLt` as an intermediate fact. Rewrite using `[Fin.ext_iff, Fin.val_rev]`. Use linear arithmetic over natural numbers and integers.
-/
theorem fSatake_rev_iff (k l : Fin n) : (k : ℕ) + l + 1 = n ↔ k = l.rev := by
  have := k.isLt
  have := l.isLt
  rw [Fin.ext_iff, Fin.val_rev]
  omega

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single l.rev]`. Rewrite using `[show antiJ L n l.rev l = 1 from if_pos ((fSatake_rev_iff l.rev l).2 rfl), mul_one]`. Both sides reduce to the same expression. Introduce `j _ hj`. Rewrite using `[show antiJ L n j l = 0 from if_neg (fun h => hj ((fSatake_rev_iff j l).1 h)), mul_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem fSatake_cTJ (M : Matrix (Fin n) (Fin n) L) (i l : Fin n) :
    (cT σ M * antiJ L n) i l = σ (M l.rev i) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single l.rev]
  · rw [show antiJ L n l.rev l = 1 from if_pos ((fSatake_rev_iff l.rev l).2 rfl), mul_one]
    rfl
  · intro j _ hj
    rw [show antiJ L n j l = 0 from if_neg (fun h => hj ((fSatake_rev_iff j l).1 h)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Establish `h` using `congrFun (congrFun hU i) i.rev`. Rewrite `h` using `[Matrix.mul_apply, Finset.sum_eq_single i.rev]`. Rewrite `h` using `[fSatake_cTJ, Fin.rev_rev, show antiJ L n i i.rev = 1 from if_pos ((fSatake_rev_iff i i.rev).2 (Fin.rev_rev i).symm)]`. Conclude with `h`. Introduce `l _ hl`.

Rewrite using `[fSatake_cTJ]`. Break down `lt_or_gt_of_ne hl with h1 | h1` into its components or cases. Establish `h2 : i < l.rev`. Simplify using `only [Fin.lt_iff_val_lt_val, Fin.val_rev] at h1 ⊢`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hb _ _ h2, map_zero, zero_mul]`. Rewrite using `[hb l i.rev h1, mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem fSatake_unit_diag_mat {M : Matrix (Fin n) (Fin n) L} (hb : ∀ i j : Fin n, j < i → M i j = 0)
    (hU : cT σ M * antiJ L n * M = antiJ L n) (i : Fin n) : σ (M i i) * M i.rev i.rev = 1 := by
  have h := congrFun (congrFun hU i) i.rev
  rw [Matrix.mul_apply, Finset.sum_eq_single i.rev] at h
  · rw [fSatake_cTJ, Fin.rev_rev,
      show antiJ L n i i.rev = 1 from if_pos ((fSatake_rev_iff i i.rev).2 (Fin.rev_rev i).symm)] at h
    exact h
  · intro l _ hl
    rw [fSatake_cTJ]
    rcases lt_or_gt_of_ne hl with h1 | h1
    · have h2 : i < l.rev := by
        simp only [Fin.lt_iff_val_lt_val, Fin.val_rev] at h1 ⊢
        omega
      rw [hb _ _ h2, map_zero, zero_mul]
    · rw [hb l i.rev h1, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
The claim follows from `fSatake_unit_diag_mat hb b.2 i`.
-/
theorem fSatake_unit_diag {b : GU σ n} (hb : IsBorelU b) (i : Fin n) :
    σ ((((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) *
      (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i.rev i.rev = 1 :=
  fSatake_unit_diag_mat hb b.2 i

/- English proof (translation)
Establish `hne : ∀ i, e i ≠ 0` using `fun i h => by`. Use `he i.rev` as an intermediate fact. Rewrite `this` using `[Fin.rev_rev, h, mul_zero]`. Conclude with `zero_ne_one this`. Set `g : GL (Fin n) L` to `⟨Matrix.diagonal e, Matrix.diagonal (fun i => (e i)⁻¹), by simp [Matrix.diagonal_mul_diagonal, mul_inv_cancel₀ (hne _)], by simp [Matrix.diagonal_mul_diagonal, inv_mul_cancel₀ (hne _)]⟩`.

Establish `hc : cT σ (Matrix.diagonal e) = Matrix.diagonal (fun i => σ (e i))`. Use extensionality with `a c`. Distinguish the cases in `h : a = c`. Substitute `h` using the available equality. Simplify using `[cT]`.

Simplify using `[cT, Matrix.diagonal_apply, h, Ne.symm h]`. Establish `hg : g ∈ GU σ n` using `by show cT σ (Matrix.diagonal e) * antiJ L n * Matrix.diagonal e = antiJ L n`. Use extensionality with `i l`. Rewrite using `[hc, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Simplify using `only [antiJ]`.

Use `split_ifs with h`. Establish `hl : l = i.rev` using `(fSatake_rev_iff l i).1 (by omega)`. Substitute `hl` using the available equality. Simplify using `[he i]`. Simplify using the standard rewrite rules.

Conclude with `⟨⟨g, hg⟩, rfl, rfl⟩`.
-/
theorem fSatake_diag_exists (e : Fin n → L) (he : ∀ i, σ (e i) * e i.rev = 1) :
    ∃ d : GU σ n, (((d : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal e ∧
      (((d⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        Matrix.diagonal (fun i => (e i)⁻¹) := by
  have hne : ∀ i, e i ≠ 0 := fun i h => by
    have := he i.rev
    rw [Fin.rev_rev, h, mul_zero] at this
    exact zero_ne_one this
  let g : GL (Fin n) L := ⟨Matrix.diagonal e, Matrix.diagonal (fun i => (e i)⁻¹),
    by simp [Matrix.diagonal_mul_diagonal, mul_inv_cancel₀ (hne _)],
    by simp [Matrix.diagonal_mul_diagonal, inv_mul_cancel₀ (hne _)]⟩
  have hc : cT σ (Matrix.diagonal e) = Matrix.diagonal (fun i => σ (e i)) := by
    ext a c
    by_cases h : a = c
    · subst h
      simp [cT]
    · simp [cT, Matrix.diagonal_apply, h, Ne.symm h]
  have hg : g ∈ GU σ n := by
    show cT σ (Matrix.diagonal e) * antiJ L n * Matrix.diagonal e = antiJ L n
    ext i l
    rw [hc, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [antiJ]
    split_ifs with h
    · have hl : l = i.rev := (fSatake_rev_iff l i).1 (by omega)
      subst hl
      simp [he i]
    · simp
  exact ⟨⟨g, hg⟩, rfl, rfl⟩

end Formalism.UG.P
