import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
open NumberField ReciprocityTheory.ChartRestriction.G.FD

open scoped ComplexOrder ComplexConjugate Matrix

namespace GlobalTheory.FlagDomain

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.
-/
theorem gram_eq_transpose_mul {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G M = Mᵀ * G.map τ * M.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/- English proof (translation)
Rewrite using `[gram_eq_transpose_mul, gram_eq_transpose_mul, Matrix.transpose_mul, Matrix.map_mul]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem gram_mul {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (P Q : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G (P * Q) = Qᵀ * gram τ G P * Q.map (starRingEnd ℂ) := by
  rw [gram_eq_transpose_mul, gram_eq_transpose_mul, Matrix.transpose_mul,
    Matrix.map_mul]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨ε, hε, hsgn⟩ : ∃ ε : ℝ, ε ^ 2 = 1 ∧ ∀ a : ℕ, a < r → sgn X.p0 a = ε := by`. Break down `h with h | h` into its components or cases. Conclude with `⟨-1, by norm_num, fun a _ => by simp [sgn, h]⟩`. Conclude with `⟨1, by norm_num, fun a ha => by simp [sgn, h, ha]⟩`. Establish `hi : (i : ℕ) ≤ r` using `Nat.le_of_lt_succ i.isLt`.

Establish `hps : psgn X.p0 i = ε ^ (i : ℕ)`. Unfold `psgn`. Rewrite using `[Finset.prod_congr rfl (g := fun _ => ε), Finset.prod_const, Finset.card_range]`. Introduce `a ha`. Conclude with `hsgn a (lt_of_lt_of_le (Finset.mem_range.1 ha) hi)`.

Take `⟨P, hPdet, hP⟩` from `X.signature τ`. Use `set M := mat x τ with hM`. Use `set Q := P⁻¹ * M with hQ`. Establish `hPQ : P * Q = M` using `Matrix.mul_nonsing_inv_cancel_left P M (isUnit_iff_ne_zero.2 hPdet)`. Establish `hQdet : Q.det ≠ 0`.

Introduce `h0`. Apply `hx` to reduce the goal to its premises. Rewrite using `[← hPQ, Matrix.det_mul, h0, mul_zero]`. Use `set N := Q.map (starRingEnd ℂ) with hN`. Establish `hNdet : N.det ≠ 0`.

Rewrite using `[hN, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Simplify using `using hQdet`. Establish `hNinj : Function.Injective N.mulVec` using `Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det N).2 (isUnit_iff_ne_zero.2 hNdet))`. Establish `hH : (Nᴴ * N).PosDef` using `Matrix.PosDef.conjTranspose_mul_self N hNinj`. Establish `hNt : Nᴴ = Qᵀ`.

Use extensionality with `a b`. Simplify using `[hN, Matrix.conjTranspose_apply]`. Establish `hdiag : Matrix.diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) = (ε : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)`. Rewrite using `[Matrix.smul_one_eq_diagonal]`. Use `congr 1`.

Use function extensionality and compare the values at `a`. Rewrite using `[hsgn a a.isLt]`. Establish `hgram : gram τ.1 X.Gm M = (ε : ℂ) • (Nᴴ * N)`. Rewrite using `[← hPQ, GlobalTheory.FlagDomain.gram_mul, hP, hdiag, hNt, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]`. Use `set e := Fin.castLE hi with he`.

Establish `hsub : ((Nᴴ * N).submatrix e e).PosDef` using `hH.submatrix (Fin.castLE_injective hi)`. Establish `hdpos` using `Complex.pos_iff.1 hsub.det_pos`. Establish `hd : dmin X.Gm x τ i = ((ε ^ (i : ℕ) : ℝ) : ℂ) * ((Nᴴ * N).submatrix e e).det`. Simplify using `only [dmin, lminor]`. Establish `hs : ((ε : ℂ) • (Nᴴ * N)).submatrix e e = (ε : ℂ) • ((Nᴴ * N).submatrix e e)`.

Use extensionality with `a b`. Simplify using the standard rewrite rules. Rewrite using `[← hM, hgram, ← he, hs, Matrix.det_smul, Fintype.card_fin]`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite using `[hd, Complex.re_ofReal_mul, hps, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, hε, one_pow, one_mul]`. Conclude with `hdpos.1`.
-/
theorem dmin_sign_of_definite (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : Data E r) (h : X.p0 = 0 ∨ X.p0 = r) (x : Frame X.Ψ r) (τ : X.Ψ)
    (hx : (mat x τ).det ≠ 0) (i : Fin (r + 1)) :
    0 < psgn X.p0 i * (dmin X.Gm x τ i).re := by
  obtain ⟨ε, hε, hsgn⟩ : ∃ ε : ℝ, ε ^ 2 = 1 ∧ ∀ a : ℕ, a < r → sgn X.p0 a = ε := by
    rcases h with h | h
    · exact ⟨-1, by norm_num, fun a _ => by simp [sgn, h]⟩
    · exact ⟨1, by norm_num, fun a ha => by simp [sgn, h, ha]⟩
  have hi : (i : ℕ) ≤ r := Nat.le_of_lt_succ i.isLt
  have hps : psgn X.p0 i = ε ^ (i : ℕ) := by
    unfold psgn
    rw [Finset.prod_congr rfl (g := fun _ => ε), Finset.prod_const, Finset.card_range]
    intro a ha
    exact hsgn a (lt_of_lt_of_le (Finset.mem_range.1 ha) hi)
  obtain ⟨P, hPdet, hP⟩ := X.signature τ
  set M := mat x τ with hM
  set Q := P⁻¹ * M with hQ
  have hPQ : P * Q = M := Matrix.mul_nonsing_inv_cancel_left P M (isUnit_iff_ne_zero.2 hPdet)
  have hQdet : Q.det ≠ 0 := by
    intro h0
    apply hx
    rw [← hPQ, Matrix.det_mul, h0, mul_zero]
  set N := Q.map (starRingEnd ℂ) with hN
  have hNdet : N.det ≠ 0 := by
    rw [hN, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simpa using hQdet
  have hNinj : Function.Injective N.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det N).2 (isUnit_iff_ne_zero.2 hNdet))
  have hH : (Nᴴ * N).PosDef := Matrix.PosDef.conjTranspose_mul_self N hNinj
  have hNt : Nᴴ = Qᵀ := by
    ext a b
    simp [hN, Matrix.conjTranspose_apply]
  have hdiag : Matrix.diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) = (ε : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) := by
    rw [Matrix.smul_one_eq_diagonal]
    congr 1
    funext a
    rw [hsgn a a.isLt]
  have hgram : gram τ.1 X.Gm M = (ε : ℂ) • (Nᴴ * N) := by
    rw [← hPQ, GlobalTheory.FlagDomain.gram_mul, hP, hdiag, hNt, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  set e := Fin.castLE hi with he
  have hsub : ((Nᴴ * N).submatrix e e).PosDef := hH.submatrix (Fin.castLE_injective hi)
  have hdpos := Complex.pos_iff.1 hsub.det_pos
  have hd : dmin X.Gm x τ i = ((ε ^ (i : ℕ) : ℝ) : ℂ) * ((Nᴴ * N).submatrix e e).det := by
    simp only [dmin, lminor]
    have hs : ((ε : ℂ) • (Nᴴ * N)).submatrix e e = (ε : ℂ) • ((Nᴴ * N).submatrix e e) := by
      ext a b
      simp
    rw [← hM, hgram, ← he, hs, Matrix.det_smul, Fintype.card_fin]
    push_cast
    rfl
  rw [hd, Complex.re_ofReal_mul, hps, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, hε, one_pow,
    one_mul]
  exact hdpos.1

/- English proof (translation)
Introduce `E _ _ _ r X h x τ hx i` and use `dmin_sign_of_definite E r X h x τ hx i`.
-/
theorem definite_frame_leading_minors_sign : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (X.p0 = 0 ∨ X.p0 = r) → ∀ (x : Frame X.Ψ r) (τ : X.Ψ), (mat x τ).det ≠ 0 →
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re :=
  fun E _ _ _ r X h x τ hx i => dmin_sign_of_definite E r X h x τ hx i

end GlobalTheory.FlagDomain
