import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.CayDivOf

noncomputable section

open MvPolynomial Matrix Module

namespace PositivityTheory.Rg.Sw.SP

namespace NullPf

variable {K : Type*} [Field K]

/- English proof (translation)
Take `⟨b, hbs, hspan, hli⟩` from `exists_linearIndependent K (Set.range M.row)`. Establish `hfin : b.Finite` using `(Set.finite_range _).subset hbs`. Establish `: Fintype b` using `hfin.fintype`. Establish `hcard : M.rank = b.toFinset.card`. Rewrite using `[M.rank_eq_finrank_span_row, ← hspan]`.

Conclude with `finrank_span_set_eq_card hli`. Establish `hkb : k ≤ Fintype.card b` using `by rw [← Set.toFinset_card]; omega`. Set `e : Fin k ↪ b` to `(Fin.castLEEmb hkb).trans (Fintype.equivFin b).symm.toEmbedding`. Set `sec : b → m` to `fun v => (hbs v.2).choose`. Establish `hsec : ∀ v : b, M.row (sec v) = v` using `fun v => (hbs v.2).choose_spec`.

Establish `hinj : Function.Injective sec`. Introduce `v w h`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hsec v, ← hsec w, h]`. Use `⟨e.trans ⟨sec, hinj⟩, ?_⟩` and prove the remaining obligations.

Establish `h2 : (fun p => M ((e.trans ⟨sec, hinj⟩) p)) = (fun v : b => (v : n → K)) ∘ e`. Use function extensionality and compare the values at `p`. Simplify using `only [Function.comp_apply, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk]`. Conclude with `hsec (e p)`. Rewrite using `[h2]`.

Conclude with `hli.comp e e.injective`.
-/
theorem exists_rows {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] (M : Matrix m n K) {k : ℕ} (hk : k ≤ M.rank) :
    ∃ I : Fin k ↪ m, LinearIndependent K (fun p => M (I p)) := by
  classical
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent K (Set.range M.row)
  have hfin : b.Finite := (Set.finite_range _).subset hbs
  have : Fintype b := hfin.fintype
  have hcard : M.rank = b.toFinset.card := by
    rw [M.rank_eq_finrank_span_row, ← hspan]
    exact finrank_span_set_eq_card hli
  have hkb : k ≤ Fintype.card b := by rw [← Set.toFinset_card]; omega
  let e : Fin k ↪ b := (Fin.castLEEmb hkb).trans (Fintype.equivFin b).symm.toEmbedding
  let sec : b → m := fun v => (hbs v.2).choose
  have hsec : ∀ v : b, M.row (sec v) = v := fun v => (hbs v.2).choose_spec
  have hinj : Function.Injective sec := by
    intro v w h
    apply Subtype.ext
    rw [← hsec v, ← hsec w, h]
  refine ⟨e.trans ⟨sec, hinj⟩, ?_⟩
  have h2 : (fun p => M ((e.trans ⟨sec, hinj⟩) p)) = (fun v : b => (v : n → K)) ∘ e := by
    funext p
    simp only [Function.comp_apply, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk]
    exact hsec (e p)
  rw [h2]
  exact hli.comp e e.injective

/- English proof (translation)
Take `⟨I, hI⟩` from `exists_rows M hk`. Use `set R : Matrix (Fin k) (Fin n) K := M.submatrix I id with hR`. Establish `hRrank : R.rank = k`. Establish `: LinearIndependent K R.row` using `hI`. Simplify using `using this.rank_matrix`.

Establish `hRt : k ≤ Rᵀ.rank` using `by rw [rank_transpose, hRrank]`. Take `⟨J, hJ⟩` from `exists_rows Rᵀ hRt`. Use `⟨I, J, ?_⟩` and prove the remaining obligations. Use `set T : Matrix (Fin k) (Fin k) K := Rᵀ.submatrix J id with hT`. Establish `hTu : IsUnit T`.

Rewrite using `[← linearIndependent_rows_iff_isUnit]`. Conclude with `hJ`. Establish `hTeq : T = (M.submatrix I J)ᵀ`. Use extensionality with `p q`. Simplify using `[T, R, transpose_apply, submatrix_apply]`.

Use `(Matrix.isUnit_iff_isUnit_det T).1 hTu` as an intermediate fact. Rewrite `this` using `[hTeq, det_transpose]`. Conclude with `this.ne_zero`.
-/
theorem exists_minor_ne_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {k : ℕ} (hk : k ≤ M.rank) :
    ∃ I J : Fin k ↪ Fin n, (M.submatrix I J).det ≠ 0 := by
  classical
  obtain ⟨I, hI⟩ := exists_rows M hk
  set R : Matrix (Fin k) (Fin n) K := M.submatrix I id with hR
  have hRrank : R.rank = k := by
    have : LinearIndependent K R.row := hI
    simpa using this.rank_matrix
  have hRt : k ≤ Rᵀ.rank := by rw [rank_transpose, hRrank]
  obtain ⟨J, hJ⟩ := exists_rows Rᵀ hRt
  refine ⟨I, J, ?_⟩
  set T : Matrix (Fin k) (Fin k) K := Rᵀ.submatrix J id with hT
  have hTu : IsUnit T := by
    rw [← linearIndependent_rows_iff_isUnit]
    exact hJ
  have hTeq : T = (M.submatrix I J)ᵀ := by
    ext p q
    simp [T, R, transpose_apply, submatrix_apply]
  have := (Matrix.isUnit_iff_isUnit_det T).1 hTu
  rw [hTeq, det_transpose] at this
  exact this.ne_zero

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Take `⟨I, J, hIJ⟩` from `exists_minor_ne_zero M (not_lt.1 hc)`. Conclude with `hIJ (h I J)`.
-/
theorem rank_lt_of_minors {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {k : ℕ}
    (h : ∀ I J : Fin k ↪ Fin n, (M.submatrix I J).det = 0) : M.rank < k := by
  by_contra hc
  obtain ⟨I, J, hIJ⟩ := exists_minor_ne_zero M (not_lt.1 hc)
  exact hIJ (h I J)

/- English proof (translation)
Unfold `Matrix.rank`. Rewrite using `[Matrix.mulVecLin_add]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem rank_add_le' {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  calc finrank K (LinearMap.range (A.mulVecLin + B.mulVecLin))
      ≤ finrank K ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin : Submodule K (Fin n → K)) :=
        Submodule.finrank_mono (LinearMap.range_add_le _ _)
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

/- English proof (translation)
Assume the negation of the conclusion as `hd`. Use `Matrix.rank_of_isUnit M ((Matrix.isUnit_iff_isUnit_det M).2 (Ne.isUnit hd))` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem det_eq_zero_of_rank_lt {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (h : M.rank < n) : M.det = 0 := by
  by_contra hd
  have := Matrix.rank_of_isUnit M ((Matrix.isUnit_iff_isUnit_det M).2 (Ne.isUnit hd))
  simp at this
  omega

end NullPf

open NullPf in
/- English proof (translation)
Introduce `n m hmn N₀`. Use `set S : Set (PAB n) := {x : PAB n | ∃ i j : ℕ, i + j = n - m ∧ ((i = 0 ∧ j = 0 ∧ x = 1) ∨ (i = 0 ∧ 0 < j ∧ ∃ (I J : Fin j ↪ Fin n), x = minorPolynomial true I J ^ N₀) ∨ (0 < i ∧ j = 0 ∧ ∃ (I J : Fin (m + i) ↪ Fin n), x = minorPolynomial false I J ^ N₀) ∨ (0 < i ∧ 0 < j ∧ ∃ (I J : …`. Use `set D : PAB n := Matrix.det (fun p q : Fin n => (X (false, p, q) + X (true, p, q) : PAB n)) with hD`. It suffices to establish `hrad : D ∈ (Ideal.span S).radical from (Ideal.mem_radical_iff).1 hrad`. Rewrite using `[← vanishingIdeal_zeroLocus_eq_radical (K := ℂ)]`.

Introduce `x hx`. Rewrite `hx` using `[mem_zeroLocus_iff]`. Establish `hgen : ∀ s ∈ S, aeval x s = 0` using `fun s hs => hx s (Ideal.subset_span hs)`. Use `set A : Matrix (Fin n) (Fin n) ℂ := fun p q => x (false, p, q) with hA`. Use `set B : Matrix (Fin n) (Fin n) ℂ := fun p q => x (true, p, q) with hB`.

Establish `hminor : ∀ (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n), aeval x (minorPolynomial b I J) = Matrix.det (fun p q : Fin ρ => x (b, I p, J q))`. Introduce `b ρ I J`. Combine the equalities or inequalities in the displayed calculation. Establish `h` using `RingHom.map_det ((aeval x : PAB n →ₐ[ℂ] ℂ) : PAB n →+* ℂ) (Matrix.of fun p q : Fin ρ => (X (b, I p, J q) : PAB n))`. Use `h.trans ?_` and prove the remaining obligations.

Use `congr 1`. Use extensionality with `p q`. Simplify using the standard rewrite rules. Establish `hpow : ∀ (a : ℂ), a ^ N₀ = 0 → a = 0` using `fun a h => ((pow_eq_zero_iff' (M₀ := ℂ)).1 h).1`. Establish `hr : 0 < n - m` using `by omega`.

Establish `hBr : B.rank < n - m`. Apply `rank_lt_of_minors` to reduce the goal to its premises. Introduce `I J`. Use `hgen (minorPolynomial true I J ^ N₀) ⟨0, n - m, by omega, Or.inr (Or.inl ⟨rfl, hr, I, J, rfl⟩)⟩` as an intermediate fact. Rewrite `this` using `[map_pow, hminor]`.

Conclude with `hpow _ this`. Establish `hsum : (A + B).rank < n`. Break down `Nat.eq_zero_or_pos B.rank with h0 | hpos` into its components or cases. Establish `hAr : A.rank < m + (n - m)`. Apply `rank_lt_of_minors` to reduce the goal to its premises.

Introduce `I J`. Use `hgen (minorPolynomial false I J ^ N₀) ⟨n - m, 0, by omega, Or.inr (Or.inr (Or.inl ⟨hr, rfl, I, J, rfl⟩))⟩` as an intermediate fact. Rewrite `this` using `[map_pow, hminor]`. Conclude with `hpow _ this`. Use `rank_add_le' A B` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Take `⟨I', J', hIJ'⟩` from `exists_minor_ne_zero B (le_refl B.rank)`. Establish `hAr : A.rank < m + (n - m - B.rank)`. Apply `rank_lt_of_minors` to reduce the goal to its premises. Introduce `I J`.

Use `hgen (minorPolynomial false I J ^ N₀ * minorPolynomial true I' J' ^ N₀) ⟨n - m - B.rank, B.rank, by omega, Or.inr (Or.inr (Or.inr ⟨by omega, hpos, I, J, I', J', rfl⟩))⟩` as an intermediate fact. Rewrite `this` using `[map_mul, map_pow, map_pow, hminor, hminor]`. Break down `mul_eq_zero.1 this with h | h` into its components or cases. Conclude with `hpow _ h`. Conclude with `absurd (hpow _ h) hIJ'`.

Use `rank_add_le' A B` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hdet` using `det_eq_zero_of_rank_lt (A + B) hsum`. Combine the equalities or inequalities in the displayed calculation. Establish `h` using `RingHom.map_det ((aeval x : PAB n →ₐ[ℂ] ℂ) : PAB n →+* ℂ) (Matrix.of fun p q : Fin n => (X (false, p, q) + X (true, p, q) : PAB n))`.

Use `h.trans ?_` and prove the remaining obligations. Use `congr 1`. Use extensionality with `p q`. Simplify using `[A, B, Matrix.add_apply]`. Both sides reduce to the same expression.

Use `_ = 0 := hdet`.
-/
theorem null : Null := by
  classical
  intro n m hmn N₀
  set S : Set (PAB n) := {x : PAB n | ∃ i j : ℕ, i + j = n - m ∧
        ((i = 0 ∧ j = 0 ∧ x = 1) ∨
         (i = 0 ∧ 0 < j ∧ ∃ (I J : Fin j ↪ Fin n), x = minorPolynomial true I J ^ N₀) ∨
         (0 < i ∧ j = 0 ∧ ∃ (I J : Fin (m + i) ↪ Fin n), x = minorPolynomial false I J ^ N₀) ∨
         (0 < i ∧ 0 < j ∧ ∃ (I J : Fin (m + i) ↪ Fin n) (I' J' : Fin j ↪ Fin n),
            x = minorPolynomial false I J ^ N₀ * minorPolynomial true I' J' ^ N₀))} with hS
  set D : PAB n := Matrix.det (fun p q : Fin n => (X (false, p, q) + X (true, p, q) : PAB n)) with hD
  suffices hrad : D ∈ (Ideal.span S).radical from (Ideal.mem_radical_iff).1 hrad
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := ℂ)]
  intro x hx
  rw [mem_zeroLocus_iff] at hx
  have hgen : ∀ s ∈ S, aeval x s = 0 := fun s hs => hx s (Ideal.subset_span hs)
  set A : Matrix (Fin n) (Fin n) ℂ := fun p q => x (false, p, q) with hA
  set B : Matrix (Fin n) (Fin n) ℂ := fun p q => x (true, p, q) with hB
  have hminor : ∀ (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n),
      aeval x (minorPolynomial b I J) = Matrix.det (fun p q : Fin ρ => x (b, I p, J q)) := by
    intro b ρ I J
    calc aeval x (minorPolynomial b I J) = ((aeval x : PAB n →ₐ[ℂ] ℂ) : PAB n →+* ℂ) (minorPolynomial b I J) := rfl
      _ = _ := by
        have h := RingHom.map_det ((aeval x : PAB n →ₐ[ℂ] ℂ) : PAB n →+* ℂ)
          (Matrix.of fun p q : Fin ρ => (X (b, I p, J q) : PAB n))
        refine h.trans ?_
        congr 1
        ext p q
        simp
  have hpow : ∀ (a : ℂ), a ^ N₀ = 0 → a = 0 := fun a h => ((pow_eq_zero_iff' (M₀ := ℂ)).1 h).1
  have hr : 0 < n - m := by omega

  have hBr : B.rank < n - m := by
    apply rank_lt_of_minors
    intro I J
    have := hgen (minorPolynomial true I J ^ N₀) ⟨0, n - m, by omega, Or.inr (Or.inl ⟨rfl, hr, I, J, rfl⟩)⟩
    rw [map_pow, hminor] at this
    exact hpow _ this
  have hsum : (A + B).rank < n := by
    rcases Nat.eq_zero_or_pos B.rank with h0 | hpos
    · have hAr : A.rank < m + (n - m) := by
        apply rank_lt_of_minors
        intro I J
        have := hgen (minorPolynomial false I J ^ N₀) ⟨n - m, 0, by omega, Or.inr (Or.inr (Or.inl ⟨hr, rfl, I, J, rfl⟩))⟩
        rw [map_pow, hminor] at this
        exact hpow _ this
      have := rank_add_le' A B
      omega
    · obtain ⟨I', J', hIJ'⟩ := exists_minor_ne_zero B (le_refl B.rank)
      have hAr : A.rank < m + (n - m - B.rank) := by
        apply rank_lt_of_minors
        intro I J
        have := hgen (minorPolynomial false I J ^ N₀ * minorPolynomial true I' J' ^ N₀)
          ⟨n - m - B.rank, B.rank, by omega, Or.inr (Or.inr (Or.inr ⟨by omega, hpos, I, J, I', J', rfl⟩))⟩
        rw [map_mul, map_pow, map_pow, hminor, hminor] at this
        rcases mul_eq_zero.1 this with h | h
        · exact hpow _ h
        · exact absurd (hpow _ h) hIJ'
      have := rank_add_le' A B
      omega
  have hdet := det_eq_zero_of_rank_lt (A + B) hsum
  calc aeval x D = ((aeval x : PAB n →ₐ[ℂ] ℂ) : PAB n →+* ℂ) D := rfl
    _ = (A + B).det := by
        have h := RingHom.map_det ((aeval x : PAB n →ₐ[ℂ] ℂ) : PAB n →+* ℂ)
          (Matrix.of fun p q : Fin n => (X (false, p, q) + X (true, p, q) : PAB n))
        refine h.trans ?_
        congr 1
        ext p q
        simp [A, B, Matrix.add_apply]
        rfl
    _ = 0 := hdet

end PositivityTheory.Rg.Sw.SP
