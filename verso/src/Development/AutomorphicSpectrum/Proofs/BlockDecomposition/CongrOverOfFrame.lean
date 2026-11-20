import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.HermitianHassePrincipleHolds
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsGlIsometryCompEqOfNondegenerate

noncomputable section

open scoped Matrix TensorProduct
open Matrix

namespace GlobalTheory.CompanionTheory.RswNoFrame

section Gen

variable {R : Type*} [CommRing R] (c : R →+* R)

def st {m n : Type*} (M : Matrix m n R) : Matrix n m R := (M.map c)ᵀ

variable {c}

/- English proof (translation)
Simplify using `only [st, Matrix.map_mul, Matrix.transpose_mul]`.
-/
theorem st_mul {l m n : Type*} [Fintype m] (A : Matrix l m R) (B : Matrix m n R) :
    st c (A * B) = st c B * st c A := by
  simp only [st, Matrix.map_mul, Matrix.transpose_mul]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[st]`.
-/
theorem st_add {m n : Type*} (A B : Matrix m n R) : st c (A + B) = st c A + st c B := by
  ext i j; simp [st]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[st]`.
-/
theorem st_sub {m n : Type*} (A B : Matrix m n R) : st c (A - B) = st c A - st c B := by
  ext i j; simp [st]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[st]`.
-/
theorem st_zero {m n : Type*} : st c (0 : Matrix m n R) = 0 := by
  ext i j; simp [st]

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[st]`. Simplify using `[st, Matrix.one_apply, h, Ne.symm h]`.
-/
theorem st_one {n : Type*} [DecidableEq n] : st c (1 : Matrix n n R) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [st]
  · simp [st, Matrix.one_apply, h, Ne.symm h]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[st]`.
-/
theorem st_smul {m n : Type*} (a : R) (A : Matrix m n R) : st c (a • A) = c a • st c A := by
  ext i j; simp [st]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[st, hc]`.
-/
theorem st_st (hc : ∀ x, c (c x) = x) {m n : Type*} (A : Matrix m n R) : st c (st c A) = A := by
  ext i j; simp [st, hc]

/- English proof (translation)
Rewrite using `[st_mul, st_mul, st_st hc, hG, Matrix.mul_assoc]`.
-/
theorem st_gram (hc : ∀ x, c (c x) = x) {N m n : Type*} [Fintype N] {G : Matrix N N R} (hG : st c G = G)
    (A : Matrix N m R) (B : Matrix N n R) : st c (st c A * G * B) = st c B * G * A := by
  rw [st_mul, st_mul, st_st hc, hG, Matrix.mul_assoc]

/- English proof (translation)
Apply the tactic sequence `ext (i | i) (j | j) <;>`. Simplify using `[st, Matrix.mul_apply, Matrix.fromCols, Matrix.fromBlocks, Finset.sum_comm]`.
-/
theorem gram_fromCols {N m n : Type*} [Fintype N] [Fintype m] [Fintype n] (G : Matrix N N R)
    (A : Matrix N m R) (B : Matrix N n R) :
    st c (fromCols A B) * G * fromCols A B =
      fromBlocks (st c A * G * A) (st c A * G * B) (st c B * G * A) (st c B * G * B) := by
  ext (i | i) (j | j) <;>
    simp [st, Matrix.mul_apply, Matrix.fromCols, Matrix.fromBlocks, Finset.sum_comm]

def hyp (R : Type*) [CommRing R] (t : ℕ) : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) R := fromBlocks 0 1 1 0

def hsum {r : ℕ} (t : ℕ) (b : Matrix (Fin r) (Fin r) R) :
    Matrix ((Fin t ⊕ Fin t) ⊕ Fin r) ((Fin t ⊕ Fin t) ⊕ Fin r) R := fromBlocks (hyp R t) 0 0 b

/- English proof (translation)
Establish `c1 : st c (fromCols y u) * G * x = 0`. Use extensionality with `(i | i) j`. Conclude with `congrFun (congrFun hyx i) j`. Conclude with `congrFun (congrFun hux i) j`. Establish `c2 : st c x * G * fromCols y u = 0`.

Rewrite using `[← st_gram hc hG, c1, st_zero]`. Establish `hyu : st c y * G * u = 1`. Rewrite using `[← st_gram hc hG, huy, st_one]`. Rewrite using `[gram_fromCols, gram_fromCols, c1, c2, hyy, hyu, huy, huu, hx, hsum, hyp]`.
-/
theorem gram_sum (hc : ∀ x, c (c x) = x) {N r t : ℕ} {G : Matrix (Fin N) (Fin N) R} (hG : st c G = G)
    {b : Matrix (Fin r) (Fin r) R} {x : Matrix (Fin N) (Fin r) R} {y u : Matrix (Fin N) (Fin t) R}
    (hyy : st c y * G * y = 0) (huu : st c u * G * u = 0) (huy : st c u * G * y = 1)
    (hyx : st c y * G * x = 0) (hux : st c u * G * x = 0) (hx : st c x * G * x = b) :
    st c (fromCols (fromCols y u) x) * G * fromCols (fromCols y u) x = hsum t b := by
  have c1 : st c (fromCols y u) * G * x = 0 := by
    ext (i | i) j
    · exact congrFun (congrFun hyx i) j
    · exact congrFun (congrFun hux i) j
  have c2 : st c x * G * fromCols y u = 0 := by
    rw [← st_gram hc hG, c1, st_zero]
  have hyu : st c y * G * u = 1 := by
    rw [← st_gram hc hG, huy, st_one]
  rw [gram_fromCols, gram_fromCols, c1, c2, hyy, hyu, huy, huu, hx, hsum, hyp]

/- English proof (translation)
Use `set w := bi * (st c x * G * y) with hw`. Use `set y' := y - x * w with hy'`. Establish `hxy : st c x * G * y' = 0`. Rewrite using `[hy', Matrix.mul_sub, ← Matrix.mul_assoc, hx, hw, ← Matrix.mul_assoc, hbi, Matrix.one_mul, sub_self]`. Establish `hyx : st c y' * G * x = 0`.

Rewrite using `[← st_gram hc hG, hxy, st_zero]`. Establish `hyy : st c y' * G * y' = 0`. Establish `e1 : st c y' * G * y' = st c y' * G * y - st c y' * G * (x * w)`. Rewrite using `[hy', Matrix.mul_sub]`. Establish `e2 : st c y' * G * (x * w) = 0`.

Rewrite using `[← Matrix.mul_assoc, hyx, Matrix.zero_mul]`. Establish `e3 : st c y' * G * y = st c y * G * y - st c w * (st c x * G * y)`. Rewrite using `[hy', st_sub, st_mul, Matrix.sub_mul, Matrix.sub_mul]`. Simplify using `only [Matrix.mul_assoc]`. Establish `e4 : st c x * G * y = b * w`.

Rewrite using `[hw, ← Matrix.mul_assoc, hbi, Matrix.one_mul]`. Rewrite using `[e1, e2, e3, e4, sub_zero, ← Matrix.mul_assoc]`. Conclude with `hq`. Establish `hLy' : L * y' = 1`. Rewrite using `[hy', Matrix.mul_sub, hLy, ← Matrix.mul_assoc, hLx, Matrix.zero_mul, sub_zero]`.

Use `set u₀ := Gi * st c L with hu₀`. Establish `hy0 : st c y' * G * u₀ = 1`. Rewrite using `[hu₀, Matrix.mul_assoc, ← Matrix.mul_assoc G, hGi, Matrix.one_mul, ← st_mul, hLy', st_one]`. Establish `hx0 : st c x * G * u₀ = 0`. Rewrite using `[hu₀, Matrix.mul_assoc, ← Matrix.mul_assoc G, hGi, Matrix.one_mul, ← st_mul, hLx, st_zero]`.

Establish `h0y : st c u₀ * G * y' = 1`. Rewrite using `[← st_gram hc hG, hy0, st_one]`. Establish `h0x : st c u₀ * G * x = 0`. Rewrite using `[← st_gram hc hG, hx0, st_zero]`. Use `clear_value u₀`.

Use `set h := st c u₀ * G * u₀ with hh`. Establish `hsth : st c h = h`. Rewrite using `[hh, st_gram hc hG]`. Establish `hhalf : c half = half`. Establish `h3 : 2 * c half = 1`.

Use `congrArg c h2` as an intermediate fact. Simplify `this` using `[map_ofNat]`. Combine the equalities or inequalities in the displayed calculation. Use `set a := (-half) • h with ha`. Establish `hsta : st c a = a`.

Rewrite using `[ha, st_smul, hsth, map_neg, hhalf]`. Use `set u := u₀ + y' * a with hu`. Establish `hyu : st c y' * G * u = 1`. Rewrite using `[hu, Matrix.mul_add, hy0, ← Matrix.mul_assoc, hyy, Matrix.zero_mul, add_zero]`. Establish `huy : st c u * G * y' = 1`.

Rewrite using `[← st_gram hc hG, hyu, st_one]`. Establish `hxu : st c x * G * u = 0`. Rewrite using `[hu, Matrix.mul_add, hx0, ← Matrix.mul_assoc, hxy, Matrix.zero_mul, add_zero]`. Establish `hux : st c u * G * x = 0`. Rewrite using `[← st_gram hc hG, hxu, st_zero]`.

Establish `huu : st c u * G * u = 0`. Establish `e1 : st c u * G * u = st c u * G * u₀ + st c u * G * y' * a` using `by conv_lhs => rw [hu, Matrix.mul_add, ← Matrix.mul_assoc]`. Establish `e2 : st c u * G * u₀ = h + a`. Rewrite using `[hu, st_add, st_mul, hsta, Matrix.add_mul, Matrix.add_mul, hh]`. Use `congr 1`.

Rewrite using `[Matrix.mul_assoc a, Matrix.mul_assoc a, hy0, Matrix.mul_one]`. Rewrite using `[e1, e2, huy, Matrix.one_mul, ha]`. Establish `e3 : (1 + -half + -half : R) = 0` using `by linear_combination -h2`. Combine the equalities or inequalities in the displayed calculation. Conclude with `⟨fromCols (fromCols y' u) x, gram_sum hc hG hyy huu huy hyx hux hx⟩`.
-/
theorem exists_frame (hc : ∀ x, c (c x) = x) {N r t : ℕ} {G Gi : Matrix (Fin N) (Fin N) R}
    (hGi : G * Gi = 1) (hG : st c G = G) {b bi : Matrix (Fin r) (Fin r) R} (hbi : b * bi = 1)
    {x : Matrix (Fin N) (Fin r) R} {y : Matrix (Fin N) (Fin t) R} {L : Matrix (Fin t) (Fin N) R}
    (hLx : L * x = 0) (hLy : L * y = 1) (hx : st c x * G * x = b)
    (hq : st c y * G * y - st c (bi * (st c x * G * y)) * b * (bi * (st c x * G * y)) = 0)
    {half : R} (h2 : 2 * half = 1) :
    ∃ T : Matrix (Fin N) ((Fin t ⊕ Fin t) ⊕ Fin r) R, st c T * G * T = hsum t b := by
  set w := bi * (st c x * G * y) with hw
  set y' := y - x * w with hy'
  have hxy : st c x * G * y' = 0 := by
    rw [hy', Matrix.mul_sub, ← Matrix.mul_assoc, hx, hw, ← Matrix.mul_assoc, hbi, Matrix.one_mul, sub_self]
  have hyx : st c y' * G * x = 0 := by
    rw [← st_gram hc hG, hxy, st_zero]
  have hyy : st c y' * G * y' = 0 := by
    have e1 : st c y' * G * y' = st c y' * G * y - st c y' * G * (x * w) := by
      rw [hy', Matrix.mul_sub]
    have e2 : st c y' * G * (x * w) = 0 := by
      rw [← Matrix.mul_assoc, hyx, Matrix.zero_mul]
    have e3 : st c y' * G * y = st c y * G * y - st c w * (st c x * G * y) := by
      rw [hy', st_sub, st_mul, Matrix.sub_mul, Matrix.sub_mul]
      simp only [Matrix.mul_assoc]
    have e4 : st c x * G * y = b * w := by
      rw [hw, ← Matrix.mul_assoc, hbi, Matrix.one_mul]
    rw [e1, e2, e3, e4, sub_zero, ← Matrix.mul_assoc]
    exact hq
  have hLy' : L * y' = 1 := by
    rw [hy', Matrix.mul_sub, hLy, ← Matrix.mul_assoc, hLx, Matrix.zero_mul, sub_zero]
  set u₀ := Gi * st c L with hu₀
  have hy0 : st c y' * G * u₀ = 1 := by
    rw [hu₀, Matrix.mul_assoc, ← Matrix.mul_assoc G, hGi, Matrix.one_mul, ← st_mul, hLy', st_one]
  have hx0 : st c x * G * u₀ = 0 := by
    rw [hu₀, Matrix.mul_assoc, ← Matrix.mul_assoc G, hGi, Matrix.one_mul, ← st_mul, hLx, st_zero]
  have h0y : st c u₀ * G * y' = 1 := by
    rw [← st_gram hc hG, hy0, st_one]
  have h0x : st c u₀ * G * x = 0 := by
    rw [← st_gram hc hG, hx0, st_zero]
  clear_value u₀
  set h := st c u₀ * G * u₀ with hh
  have hsth : st c h = h := by
    rw [hh, st_gram hc hG]
  have hhalf : c half = half := by
    have h3 : 2 * c half = 1 := by
      have := congrArg c h2
      simpa [map_ofNat] using this
    calc c half = (2 * half) * c half := by rw [h2, one_mul]
      _ = half * (2 * c half) := by ring
      _ = half := by rw [h3, mul_one]
  set a := (-half) • h with ha
  have hsta : st c a = a := by
    rw [ha, st_smul, hsth, map_neg, hhalf]
  set u := u₀ + y' * a with hu
  have hyu : st c y' * G * u = 1 := by
    rw [hu, Matrix.mul_add, hy0, ← Matrix.mul_assoc, hyy, Matrix.zero_mul, add_zero]
  have huy : st c u * G * y' = 1 := by
    rw [← st_gram hc hG, hyu, st_one]
  have hxu : st c x * G * u = 0 := by
    rw [hu, Matrix.mul_add, hx0, ← Matrix.mul_assoc, hxy, Matrix.zero_mul, add_zero]
  have hux : st c u * G * x = 0 := by
    rw [← st_gram hc hG, hxu, st_zero]
  have huu : st c u * G * u = 0 := by
    have e1 : st c u * G * u = st c u * G * u₀ + st c u * G * y' * a := by
      conv_lhs => rw [hu, Matrix.mul_add, ← Matrix.mul_assoc]
    have e2 : st c u * G * u₀ = h + a := by
      rw [hu, st_add, st_mul, hsta, Matrix.add_mul, Matrix.add_mul, hh]
      congr 1
      rw [Matrix.mul_assoc a, Matrix.mul_assoc a, hy0, Matrix.mul_one]
    rw [e1, e2, huy, Matrix.one_mul, ha]
    have e3 : (1 + -half + -half : R) = 0 := by linear_combination -h2
    calc h + -half • h + -half • h = (1 + -half + -half) • h := by rw [add_smul, add_smul, one_smul]
      _ = 0 := by rw [e3, zero_smul]
  exact ⟨fromCols (fromCols y' u) x, gram_sum hc hG hyy huu huy hyx hux hx⟩

end Gen

section Field

variable {E : Type*} [Field E]

/- English proof (translation)
Simplify using `[hyp, fromBlocks_multiply, Matrix.fromBlocks_one]`.
-/
theorem hyp_mul_self (t : ℕ) : hyp E t * hyp E t = 1 := by
  simp [hyp, fromBlocks_multiply, Matrix.fromBlocks_one]

/- English proof (translation)
Rewrite using `[hsum, det_fromBlocks_zero₂₁]`. Use `mul_ne_zero (fun h => ?_) hb` and prove the remaining obligations. Use `congrArg Matrix.det (hyp_mul_self (E := E) t)` as an intermediate fact. Rewrite `this` using `[det_mul, h]`. Simplify using `at this`.
-/
theorem det_hsum_ne_zero {r t : ℕ} {b : Matrix (Fin r) (Fin r) E} (hb : b.det ≠ 0) : (hsum t b).det ≠ 0 := by
  rw [hsum, det_fromBlocks_zero₂₁]
  refine mul_ne_zero (fun h => ?_) hb
  have := congrArg Matrix.det (hyp_mul_self (E := E) t)
  rw [det_mul, h] at this
  simp at this

def hhat {N r t : ℕ} (ε : (Fin t ⊕ Fin t) ⊕ Fin r ≃ Fin N) (b : Matrix (Fin r) (Fin r) E) :
    Matrix (Fin N) (Fin N) E := (hsum t b).submatrix ε.symm ε.symm

/- English proof (translation)
Apply the tactic sequence `rintro ((i | i) | i) ((j | j) | j) <;>`. Simplify using `[hsum, hyp, hb, Matrix.one_apply, eq_comm]`.
-/
theorem hsum_herm {r t : ℕ} {c : E →+* E} {b : Matrix (Fin r) (Fin r) E} (hb : ∀ i j, c (b i j) = b j i) :
    ∀ i j, c (hsum t b i j) = hsum t b j i := by
  rintro ((i | i) | i) ((j | j) | j) <;>
    simp [hsum, hyp, hb, Matrix.one_apply, eq_comm]

/- English proof (translation)
Use `set B := S.submatrix id ε.symm with hB`. Establish `hB1 : st c B * G * B = hhat ε w`. Establish `: st c B = (st c S).submatrix ε.symm id`. Use extensionality with `i j`. Simplify using `[st, hB]`.

Rewrite using `[this, hhat, ← hS, hB]`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply]`. Establish `hBd : B.det ≠ 0`. Introduce `h0`.

Establish `h1` using `congrArg Matrix.det hB1`. Rewrite `h1` using `[det_mul, h0, mul_zero, hhat, det_submatrix_equiv_self]`. Conclude with `det_hsum_ne_zero hwd h1.symm`. Use `set Bi := B⁻¹ with hBi`. Establish `hBB : B * Bi = 1` using `Matrix.mul_nonsing_inv _ hBd.isUnit`.

Establish `hBid : Bi.det ≠ 0`. Introduce `h0`. Establish `h1` using `congrArg Matrix.det hBB`. Rewrite `h1` using `[det_mul, h0, mul_zero, det_one]`. Conclude with `zero_ne_one h1`.

Use `set Q := Bi.map c * P with hQ`. Establish `hQd : Q.det ≠ 0`. Rewrite using `[hQ, det_mul, show (Bi.map c).det = c Bi.det from (RingHom.map_det c Bi).symm]`. Conclude with `mul_ne_zero ((map_ne_zero c).2 hBid) hP`. Establish `hQ1 : Qᵀ * hhat ε w * Q.map c = hhat ε b`.

Establish `e1 : Q.map c = Bi * P.map c`. Rewrite using `[hQ, Matrix.map_mul, Matrix.map_map]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `[hc]`.

Establish `e2 : Qᵀ = Pᵀ * st c Bi`. Rewrite using `[hQ, Matrix.transpose_mul]`. Both sides reduce to the same expression. Establish `e3 : st c Bi * st c B = 1`. Rewrite using `[← st_mul, hBB, st_one]`.

Rewrite using `[h, e1, e2, ← hB1]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Pᵀ * G * P.map c := by rw [e3, hBB, Matrix.mul_one, Matrix.mul_one]`. Use `GlobalTheory.HermWitt.congr_of_fromBlocks_congr h2 hc (D := hyp E t) (G₁ := w) (G₂ := b) (P := Q.submatrix ε ε) ?_ ?_ hw ?_ ?_` and prove the remaining obligations.

Introduce `i j`. Use `hsum_herm (t := t) (c := c) (b := w) hw (Sum.inl i) (Sum.inl j)` as an intermediate fact. Simplify `this` using `[hsum]`. Introduce `h0`. Establish `h1` using `det_hsum_ne_zero (t := t) hwd`.

Rewrite `h1` using `[hsum, det_fromBlocks_zero₂₁, h0, zero_mul]`. Conclude with `h1 rfl`. Rewrite using `[det_submatrix_equiv_self]` and apply the resulting hypothesis. Establish `h3 : hsum t b = (hhat ε b).submatrix ε ε`. Use extensionality with `i j`.

Simplify using `[hhat]`. Establish `h4 : hsum t w = (hhat ε w).submatrix ε ε`. Use extensionality with `i j`. Simplify using `[hhat]`. Express the relevant statement in the definitionally equal form `hsum t b = _ * hsum t w * _`.

Rewrite using `[h3, h4, ← hQ1, ← Matrix.submatrix_mul_equiv _ _ ε ε ε, ← Matrix.submatrix_mul_equiv _ _ ε ε ε]`. Both sides reduce to the same expression.
-/
theorem cancel {N r t : ℕ} (c : E →+* E) (hc : ∀ x, c (c x) = x) (h2 : (2 : E) ≠ 0)
    (ε : (Fin t ⊕ Fin t) ⊕ Fin r ≃ Fin N) {G : Matrix (Fin N) (Fin N) E}
    {w b : Matrix (Fin r) (Fin r) E} (hw : ∀ i j, c (w i j) = w j i) (hwd : w.det ≠ 0)
    {S : Matrix (Fin N) ((Fin t ⊕ Fin t) ⊕ Fin r) E} (hS : st c S * G * S = hsum t w)
    {P : Matrix (Fin N) (Fin N) E} (hP : P.det ≠ 0) (h : hhat ε b = Pᵀ * G * P.map c) :
    ∃ Q : Matrix (Fin r) (Fin r) E, Q.det ≠ 0 ∧ b = Qᵀ * w * Q.map c := by
  set B := S.submatrix id ε.symm with hB
  have hB1 : st c B * G * B = hhat ε w := by
    have : st c B = (st c S).submatrix ε.symm id := by
      ext i j; simp [st, hB]
    rw [this, hhat, ← hS, hB]
    ext i j
    simp [Matrix.mul_apply]
  have hBd : B.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hB1
    rw [det_mul, h0, mul_zero, hhat, det_submatrix_equiv_self] at h1
    exact det_hsum_ne_zero hwd h1.symm
  set Bi := B⁻¹ with hBi
  have hBB : B * Bi = 1 := Matrix.mul_nonsing_inv _ hBd.isUnit
  have hBid : Bi.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hBB
    rw [det_mul, h0, mul_zero, det_one] at h1
    exact zero_ne_one h1
  set Q := Bi.map c * P with hQ
  have hQd : Q.det ≠ 0 := by
    rw [hQ, det_mul, show (Bi.map c).det = c Bi.det from (RingHom.map_det c Bi).symm]
    exact mul_ne_zero ((map_ne_zero c).2 hBid) hP
  have hQ1 : Qᵀ * hhat ε w * Q.map c = hhat ε b := by
    have e1 : Q.map c = Bi * P.map c := by
      rw [hQ, Matrix.map_mul, Matrix.map_map]
      congr 1
      ext i j
      simp [hc]
    have e2 : Qᵀ = Pᵀ * st c Bi := by
      rw [hQ, Matrix.transpose_mul]
      rfl
    have e3 : st c Bi * st c B = 1 := by
      rw [← st_mul, hBB, st_one]
    rw [h, e1, e2, ← hB1]
    calc Pᵀ * st c Bi * (st c B * G * B) * (Bi * P.map c)
        = Pᵀ * (st c Bi * st c B) * G * (B * Bi) * P.map c := by
          simp only [Matrix.mul_assoc]
      _ = Pᵀ * G * P.map c := by rw [e3, hBB, Matrix.mul_one, Matrix.mul_one]
  refine GlobalTheory.HermWitt.congr_of_fromBlocks_congr h2 hc (D := hyp E t) (G₁ := w) (G₂ := b)
    (P := Q.submatrix ε ε) ?_ ?_ hw ?_ ?_
  · intro i j
    have := hsum_herm (t := t) (c := c) (b := w) hw (Sum.inl i) (Sum.inl j)
    simpa [hsum] using this
  · intro h0
    have h1 := det_hsum_ne_zero (t := t) hwd
    rw [hsum, det_fromBlocks_zero₂₁, h0, zero_mul] at h1
    exact h1 rfl
  · rwa [det_submatrix_equiv_self]
  · have h3 : hsum t b = (hhat ε b).submatrix ε ε := by
      ext i j; simp [hhat]
    have h4 : hsum t w = (hhat ε w).submatrix ε ε := by
      ext i j; simp [hhat]
    change hsum t b = _ * hsum t w * _
    rw [h3, h4, ← hQ1, ← Matrix.submatrix_mul_equiv _ _ ε ε ε, ← Matrix.submatrix_mul_equiv _ _ ε ε ε]
    rfl

end Field

section Loc

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E ≃ₐ[F] E) (A : Type*) [CommRing A] [Algebra F A]

/- English proof (translation)
Use `set c : A ⊗[F] E →+* A ⊗[F] E := (GlobalTheory.HermGlobal.baseConj σ A).toRingHom with hcdef`. Set `ι : E →+* A ⊗[F] E` to `Algebra.TensorProduct.includeRight.toRingHom`. Establish `hcc : ∀ x, c (c x) = x`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a y => simp [hcdef, hs]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`. Use `set T' := T.submatrix id ε.symm with hT'`. Establish `hst : st c T' = (st c T).submatrix ε.symm id`.

Use extensionality with `i j`. Simplify using `[st, hT']`. Establish `e1 : st c T' * G.map ι * T' = (hhat ε b).map ι`. Establish `h1 : (hhat ε b).map ι = ((hsum t b).map ι).submatrix ε.symm ε.symm`. Use extensionality with `i j`.

Simplify using `[hhat]`. Rewrite using `[h1, hst]`. Establish `h2 : (hsum t b).map ι = st c T * G.map ι * T` using `hT.symm`. Rewrite using `[h2, hT']`. Use extensionality with `i j`.

Simplify using `[Matrix.mul_apply]`. Establish `e2 : (T'.map c).map (GlobalTheory.HermGlobal.baseConj σ A) = T'`. Use extensionality with `i j`. Conclude with `hcc _`. Use `⟨T'.map c, ?_, ?_⟩` and prove the remaining obligations.

Establish `h1 : IsUnit ((hhat ε b).map ι).det`. Rewrite using `[show ((hhat ε b).map ι).det = ι (hhat ε b).det from (RingHom.map_det ι _).symm, hhat, det_submatrix_equiv_self]`. Conclude with `(det_hsum_ne_zero hbd).isUnit.map ι`. Rewrite `h1` using `[← e1, det_mul, det_mul]`. Establish `h2` using `isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h1)`.

Rewrite `h2` using `[st, det_transpose]`. Then use the resulting hypothesis. Rewrite using `[e2]`. Conclude with `e1.symm`.
-/
theorem congrOver_of_frame {N r t : ℕ} (hs : ∀ x, σ (σ x) = x) (ε : (Fin t ⊕ Fin t) ⊕ Fin r ≃ Fin N)
    {G : Matrix (Fin N) (Fin N) E} {b : Matrix (Fin r) (Fin r) E} (hbd : b.det ≠ 0)
    {T : Matrix (Fin N) ((Fin t ⊕ Fin t) ⊕ Fin r) (A ⊗[F] E)}
    (hT : st (GlobalTheory.HermGlobal.baseConj σ A).toRingHom T * G.map (fun x => (1 : A) ⊗ₜ[F] x) * T =
      (hsum t b).map (fun x => (1 : A) ⊗ₜ[F] x)) :
    GlobalTheory.HermGlobal.CongrOver σ A G (hhat ε b) := by
  set c : A ⊗[F] E →+* A ⊗[F] E := (GlobalTheory.HermGlobal.baseConj σ A).toRingHom with hcdef
  let ι : E →+* A ⊗[F] E := Algebra.TensorProduct.includeRight.toRingHom
  have hcc : ∀ x, c (c x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a y => simp [hcdef, hs]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  set T' := T.submatrix id ε.symm with hT'
  have hst : st c T' = (st c T).submatrix ε.symm id := by
    ext i j; simp [st, hT']
  have e1 : st c T' * G.map ι * T' = (hhat ε b).map ι := by
    have h1 : (hhat ε b).map ι = ((hsum t b).map ι).submatrix ε.symm ε.symm := by
      ext i j; simp [hhat]
    rw [h1, hst]
    have h2 : (hsum t b).map ι = st c T * G.map ι * T := hT.symm
    rw [h2, hT']
    ext i j
    simp [Matrix.mul_apply]
  have e2 : (T'.map c).map (GlobalTheory.HermGlobal.baseConj σ A) = T' := by
    ext i j
    exact hcc _
  refine ⟨T'.map c, ?_, ?_⟩
  · have h1 : IsUnit ((hhat ε b).map ι).det := by
      rw [show ((hhat ε b).map ι).det = ι (hhat ε b).det from (RingHom.map_det ι _).symm, hhat,
        det_submatrix_equiv_self]
      exact (det_hsum_ne_zero hbd).isUnit.map ι
    rw [← e1, det_mul, det_mul] at h1
    have h2 := isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h1)
    rwa [st, det_transpose] at h2
  · rw [e2]
    exact e1.symm

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a y`. Express the relevant statement in the definitionally equal form `(GlobalTheory.HermGlobal.baseConj σ A) ((GlobalTheory.HermGlobal.baseConj σ A) (a ⊗ₜ y)) = _`. Simplify using `[hs]`.

Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem baseConj_baseConj (hs : ∀ x, σ (σ x) = x) (x : A ⊗[F] E) :
    (GlobalTheory.HermGlobal.baseConj σ A).toRingHom ((GlobalTheory.HermGlobal.baseConj σ A).toRingHom x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    change (GlobalTheory.HermGlobal.baseConj σ A) ((GlobalTheory.HermGlobal.baseConj σ A) (a ⊗ₜ y)) = _
    simp [hs]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a y => simp [hs]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem map_baseConj {A' : Type*} [CommRing A'] [Algebra F A'] (s : E →ₐ[F] E) (hs : ∀ x, s x = σ x)
    (ev : A' →ₐ[F] A) (x : A' ⊗[F] E) :
    (Algebra.TensorProduct.map ev (AlgHom.id F E)).toRingHom
        ((Algebra.TensorProduct.map (AlgHom.id F A') s).toRingHom x) =
      (GlobalTheory.HermGlobal.baseConj σ A).toRingHom ((Algebra.TensorProduct.map ev (AlgHom.id F E)).toRingHom x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => simp [hs]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem map_one_tmul {A' : Type*} [CommRing A'] [Algebra F A'] {A : Type*} [CommRing A] [Algebra F A]
    (ev : A' →ₐ[F] A) (x : E) :
    (Algebra.TensorProduct.map ev (AlgHom.id F E)).toRingHom ((1 : A') ⊗ₜ[F] x) = (1 : A) ⊗ₜ[F] x := by
  simp

end Loc

section Ad

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.AdelicU GlobalTheory.MixModel
open PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Introduce `i j`. Conclude with `V.herm.eq _ _`.
-/
theorem gram_herm (V : HSp D) : ∀ i j, D.sp.cm.sig (V.gram i j) = V.gram j i := by
  intro i j
  exact V.herm.eq _ _

/- English proof (translation)
Take `⟨-, L, -, -, hL1, hL2⟩` from `hf`. Establish `mr : ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E), (rat M : Mx D m n).map π = M.map inc`. Introduce `m n M`. Use extensionality with `i j`. Simplify using `[rat, hπi]`.

Establish `ma : ∀ {m n : ℕ} (M : Mx D m n), (adj M).map π = st c (M.map π)`. Introduce `m n M`. Use extensionality with `i j`. Simplify using `[adj, st, hπc]`. Establish `mi : ∀ {m n : ℕ} (x : Mx D B.rank m) (y : Mx D B.rank n), (ip B x y).map π = st c (x.map π) * B.gram.map inc * y.map π`.

Introduce `m n x y`. Rewrite using `[ip, mm, mm, Matrix.map_mul, Matrix.map_mul, ma, gA, mr, Matrix.mul_assoc]`. Establish `hGi : B.gram.map inc * (B.gram⁻¹).map inc = 1`. Rewrite using `[← Matrix.map_mul, Matrix.mul_nonsing_inv _ (gram_det_ne B).isUnit]`. Simplify using the standard rewrite rules.

Establish `hbi : b₀.1.map inc * (b₀.1⁻¹).map inc = 1`. Rewrite using `[← Matrix.map_mul, Matrix.mul_nonsing_inv _ hb.isUnit]`. Simplify using the standard rewrite rules. Use `exists_frame hc hGi ?_ hbi (x := z.1.map π) (y := z.2.map π) (L := L.map π) ?_ ?_ ?_ ?_ (half := inc 2⁻¹) ?_` and prove the remaining obligations. Use extensionality with `i j`.

Simplify using `[st, hci, gram_herm]`. Rewrite using `[← Matrix.map_mul]`. Use `congrArg (fun M => Matrix.map M π) hL1` as an intermediate fact. Simplify `this` using `[mm]`. Establish `h3 : (e • (1 : Mx D t t)).map π = 1`.

Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[he]`. Simplify using `[Matrix.one_apply, hij]`.

Rewrite using `[← Matrix.map_mul, ← h3, ← hL2]`. Rewrite using `[← mi, h1]`. Use extensionality with `i j`. Simplify using `[rat, he, hπi]`. Establish `h5` using `congrArg (fun M => Matrix.map M π) h4`.

Establish `h6 : (yv B b₀ z).map π = (b₀.1⁻¹).map inc * (st c (z.1.map π) * B.gram.map inc * z.2.map π)`. Rewrite using `[yv, mm, Matrix.map_mul, mr, mi]`. Establish `h7 : (pr b₀ (yv B b₀ z) (yv B b₀ z)).map π = st c ((yv B b₀ z).map π) * b₀.1.map inc * (yv B b₀ z).map π`. Rewrite using `[pr]`. Express the relevant statement in the definitionally equal form `(HMul.hMul _ _ : Mx D t t).map π = _`.

Rewrite using `[Matrix.map_mul, Matrix.map_mul, ma, Matrix.mul_assoc]`. Use `congr 2`. Conclude with `mr b₀.1`. Simplify using `only [qv] at h5`. Establish `h8 : (ip B z.2 z.2 - pr b₀ (yv B b₀ z) (yv B b₀ z)).map π = (ip B z.2 z.2).map π - (pr b₀ (yv B b₀ z) (yv B b₀ z)).map π`.

Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite `h5` using `[h8, h7, mi, h6]`. Simplify using `using h5`. Rewrite using `[← map_ofNat inc 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]`.
-/
theorem frame_of_free {R : Type*} [CommRing R] (π : AE D →+* R) (c : R →+* R) (inc : D.host.E →+* R)
    (hc : ∀ x, c (c x) = x) (hπc : ∀ x, π (cA D x) = c (π x)) (hπi : ∀ x, π (incA D x) = inc x)
    (hci : ∀ x, c (inc x) = inc (D.sp.cm.sig x)) {B : HSp D} {r t : ℕ} (b₀ : HermE D r)
    (hb : b₀.1.det ≠ 0) {e : AE D} (he : π e = 1) {z : Mx D B.rank r × Mx D B.rank t} (hf : Free e z)
    (h1 : ip B z.1 z.1 = e • rat b₀.1) (h4 : qv B b₀ z = 0) :
    ∃ T : Matrix (Fin B.rank) ((Fin t ⊕ Fin t) ⊕ Fin r) R,
      st c T * B.gram.map inc * T = hsum t (b₀.1.map inc) := by
  obtain ⟨-, L, -, -, hL1, hL2⟩ := hf
  have mr : ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E), (rat M : Mx D m n).map π = M.map inc := by
    intro m n M
    ext i j
    simp [rat, hπi]
  have ma : ∀ {m n : ℕ} (M : Mx D m n), (adj M).map π = st c (M.map π) := by
    intro m n M
    ext i j
    simp [adj, st, hπc]
  have mi : ∀ {m n : ℕ} (x : Mx D B.rank m) (y : Mx D B.rank n),
      (ip B x y).map π = st c (x.map π) * B.gram.map inc * y.map π := by
    intro m n x y
    rw [ip, mm, mm, Matrix.map_mul, Matrix.map_mul, ma, gA, mr, Matrix.mul_assoc]
  have hGi : B.gram.map inc * (B.gram⁻¹).map inc = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (gram_det_ne B).isUnit]
    simp
  have hbi : b₀.1.map inc * (b₀.1⁻¹).map inc = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hb.isUnit]
    simp
  refine exists_frame hc hGi ?_ hbi (x := z.1.map π) (y := z.2.map π) (L := L.map π) ?_ ?_ ?_ ?_
    (half := inc 2⁻¹) ?_
  · ext i j
    simp [st, hci, gram_herm]
  · rw [← Matrix.map_mul]
    have := congrArg (fun M => Matrix.map M π) hL1
    simpa [mm] using this
  · have h3 : (e • (1 : Mx D t t)).map π = 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp [he]
      · simp [Matrix.one_apply, hij]
    rw [← Matrix.map_mul, ← h3, ← hL2]
  · rw [← mi, h1]
    ext i j
    simp [rat, he, hπi]
  · have h5 := congrArg (fun M => Matrix.map M π) h4
    have h6 : (yv B b₀ z).map π = (b₀.1⁻¹).map inc * (st c (z.1.map π) * B.gram.map inc * z.2.map π) := by
      rw [yv, mm, Matrix.map_mul, mr, mi]
    have h7 : (pr b₀ (yv B b₀ z) (yv B b₀ z)).map π =
        st c ((yv B b₀ z).map π) * b₀.1.map inc * (yv B b₀ z).map π := by
      rw [pr]
      change (HMul.hMul _ _ : Mx D t t).map π = _
      rw [Matrix.map_mul, Matrix.map_mul, ma, Matrix.mul_assoc]
      congr 2
      exact mr b₀.1
    simp only [qv] at h5
    have h8 : (ip B z.2 z.2 - pr b₀ (yv B b₀ z) (yv B b₀ z)).map π =
        (ip B z.2 z.2).map π - (pr b₀ (yv B b₀ z) (yv B b₀ z)).map π := by
      ext i j; simp
    rw [h8, h7, mi, h6] at h5
    simpa using h5
  · rw [← map_ofNat inc 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]

/- English proof (translation)
Apply the tactic sequence `ext ((i | i) | i) ((j | j) | j) <;> simp [hsum, hyp, Matrix.one_apply, apply_ite f]`.
-/
theorem hsum_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {r : ℕ} (t : ℕ)
    (b : Matrix (Fin r) (Fin r) R) : (hsum t b).map f = hsum t (b.map f) := by
  ext ((i | i) | i) ((j | j) | j) <;> simp [hsum, hyp, Matrix.one_apply, apply_ite f]

def sgE (D : D7) : D.host.E ≃ₐ[D.host.F] D.host.E :=
  AlgEquiv.ofAlgHom D.sp.cm.sig D.sp.cm.sig (AlgHom.ext fun x => star_star x) (AlgHom.ext fun x => star_star x)

/- English proof (translation)
The claim follows from `star_star x`.
-/
theorem sgE_sgE (x : D.host.E) : sgE D (sgE D x) = x := star_star x

/- English proof (translation)
Set `π : AE D →+* A ⊗[D.host.F] D.host.E` to `(Algebra.TensorProduct.map ev (AlgHom.id D.host.F D.host.E)).toRingHom`. Set `c : A ⊗[D.host.F] D.host.E →+* A ⊗[D.host.F] D.host.E` to `(GlobalTheory.HermGlobal.baseConj (sgE D) A).toRingHom`. Set `inc : D.host.E →+* A ⊗[D.host.F] D.host.E` to `Algebra.TensorProduct.includeRight.toRingHom`. Establish `hcc : ∀ x, c (c x) = x` using `baseConj_baseConj (sgE D) A sgE_sgE`. Establish `hπc : ∀ x, π (cA D x) = c (π x)` using `map_baseConj (sgE D) A D.sp.cm.sig (fun _ => rfl) ev`.

Establish `hπi : ∀ x, π (incA D x) = inc x` using `fun x => map_one_tmul ev x`. Establish `hci : ∀ x, c (inc x) = inc (D.sp.cm.sig x)` using `fun x => rfl`. Take `⟨T, hT⟩` from `frame_of_free π c inc hcc hπc hπi hci b₀ hb he hf h1 h4`. Use `congrOver_of_frame (sgE D) A sgE_sgE ε hb (T := T) ?_` and prove the remaining obligations. Rewrite `hT` using `[← hsum_map inc]`.

Conclude with `hT`.
-/
theorem congrOver_of_free (A : Type*) [CommRing A] [Algebra D.host.F A] (ev : AF D.host.F →ₐ[D.host.F] A)
    {B : HSp D} {r t : ℕ} (ε : (Fin t ⊕ Fin t) ⊕ Fin r ≃ Fin B.rank) (b₀ : HermE D r) (hb : b₀.1.det ≠ 0)
    {e : AE D} (he : Algebra.TensorProduct.map ev (AlgHom.id D.host.F D.host.E) e = 1)
    {z : Mx D B.rank r × Mx D B.rank t} (hf : Free e z)
    (h1 : ip B z.1 z.1 = e • rat b₀.1) (h4 : qv B b₀ z = 0) :
    GlobalTheory.HermGlobal.CongrOver (sgE D) A B.gram (hhat ε b₀.1) := by
  let π : AE D →+* A ⊗[D.host.F] D.host.E :=
    (Algebra.TensorProduct.map ev (AlgHom.id D.host.F D.host.E)).toRingHom
  let c : A ⊗[D.host.F] D.host.E →+* A ⊗[D.host.F] D.host.E := (GlobalTheory.HermGlobal.baseConj (sgE D) A).toRingHom
  let inc : D.host.E →+* A ⊗[D.host.F] D.host.E := Algebra.TensorProduct.includeRight.toRingHom
  have hcc : ∀ x, c (c x) = x := baseConj_baseConj (sgE D) A sgE_sgE
  have hπc : ∀ x, π (cA D x) = c (π x) := map_baseConj (sgE D) A D.sp.cm.sig (fun _ => rfl) ev
  have hπi : ∀ x, π (incA D x) = inc x := fun x => map_one_tmul ev x
  have hci : ∀ x, c (inc x) = inc (D.sp.cm.sig x) := fun x => rfl
  obtain ⟨T, hT⟩ := frame_of_free π c inc hcc hπc hπi hci b₀ hb he hf h1 h4
  refine congrOver_of_frame (sgE D) A sgE_sgE ε hb (T := T) ?_
  rw [← hsum_map inc] at hT
  exact hT

/- English proof (translation)
Introduce `D t B W ⟨d⟩ b₀ hb hno`. Use `haveI : Algebra.IsQuadraticExtension D.host.F D.host.E := { finrank_eq_two' := D.sp.cm.deg2 }`. Establish `hσ : sgE D ≠ 1`. Introduce `h`. Establish `h1 : Module.finrank D.host.F D.host.E = 1`.

Use `(Algebra.finrank_eq_one_iff_bijective_algebraMap).2 ⟨(algebraMap D.host.F D.host.E).injective, fun a => ?_⟩` and prove the remaining obligations. Conclude with `(D.sp.cm.fixed a).1 (congrArg (fun f : D.host.E ≃ₐ[D.host.F] D.host.E => f a) h)`. Establish `h2` using `D.sp.cm.deg2`. Use linear arithmetic over natural numbers and integers. Establish `hcard : Fintype.card ((Fin t ⊕ Fin t) ⊕ Fin W.rank) = Fintype.card (Fin B.rank)`.

Use `d.rank_add` as an intermediate fact. Simplify using `only [Fintype.card_sum, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers. Set `ε : (Fin t ⊕ Fin t) ⊕ Fin W.rank ≃ Fin B.rank` to `Fintype.equivOfCardEq hcard`. Set `c : D.host.E →+* D.host.E` to `(sgE D : D.host.E →+* D.host.E)`.

Establish `hcc : ∀ x, c (c x) = x` using `sgE_sgE`. Establish `hstar : ∀ {m n : Type} (M : Matrix m n D.host.E), st c M = Mᴴ` using `fun M => by`. Use extensionality with `i j`. Both sides reduce to the same expression. Establish `hGB : st c B.gram = B.gram`.

Conclude with `Matrix.ext fun i j => gram_herm B j i`. Establish `hS : st c (fromCols (fromCols d.e d.e') d.i₀) * B.gram * fromCols (fromCols d.e d.e') d.i₀ = hsum t W.gram`. Use `gram_sum hcc hGB ?_ ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[hstar]`. Conclude with `d.ee`.

Rewrite using `[hstar]`. Conclude with `d.e'e'`. Rewrite using `[hstar]`. Conclude with `d.e'e`. Rewrite using `[← st_gram hcc hGB, hstar d.i₀, d.i₀e, st_zero]`.

Rewrite using `[← st_gram hcc hGB, hstar d.i₀, d.i₀e', st_zero]`. Rewrite using `[hstar]`. Conclude with `d.iso`. Establish `hbh : ∀ i j, sgE D (b₀.1 i j) = b₀.1 j i` using `fun i j => congrFun (congrFun b₀.2 j) i`. Establish `key : ¬ ((∀ v : HeightOneSpectrum (𝓞 D.host.F), GlobalTheory.HermGlobal.CongrOver (sgE D) (v.adicCompletion D.host.F) B.gram (hhat ε b₀.1)) ∧ ∀ w : InfinitePlace D.host.F, GlobalTheory.HermGlobal.CongrOver (sgE D) w.Completion B.gram (hhat ε b₀.1))`.

Introduce and unpack `⟨hf, hi⟩`. Take `⟨P, hP, h⟩` from `GlobalTheory.Published.hermitianHassePrinciple_holds D.host.F D.host.E (sgE D) hσ _ B.gram (hhat ε b₀.1) (gram_herm B) (fun i j => hsum_herm (c := c) hbh _ _) (gram_det_ne B) (by rw [hhat, det_submatrix_equiv_self]; exact det_hsum_ne_zero hb) hf hi`. Take `⟨Q, -, hQ⟩` from `cancel c hcc two_ne_zero ε (gram_herm W) (gram_det_ne W) hS hP h`. Use `hno ⟨Q.map c, ?_⟩` and prove the remaining obligations. Rewrite using `[hQ, gramQ, Matrix.map_map]`.

Establish `: (Q.map (⇑D.sp.cm.sig ∘ ⇑c)) = Q` using `Matrix.ext fun i j => hcc _`. Rewrite using `[this, Matrix.mul_assoc]`. Rewrite `key` using `[not_and_or]`. Break down `key with h | h` into its components or cases. Use `push Not at h`.

Take `⟨v, hv⟩` from `h`. Use `⟨{v}, fun S hS e he z hz hh => hv ?_⟩` and prove the remaining obligations. Use `congrOver_of_free _ (evFin D.host.F v) ε b₀ hb ?_ hz hh.1 hh.2.2.2` and prove the remaining obligations. Use `he.2 v` as an intermediate fact. Rewrite `this` using `[if_pos (hS (Finset.mem_singleton_self v))]`.

Conclude with `this`. Use `push Not at h`. Take `⟨w, hw⟩` from `h`. Use `⟨∅, fun S _ e he z hz hh => hw ?_⟩` and prove the remaining obligations. Conclude with `congrOver_of_free _ (evInf D.host.F w) ε b₀ hb (he.1 w) hz hh.1 hh.2.2.2`.
-/
theorem noFrame (_ : IdemEx) : NoFrame := by
  intro D t B W ⟨d⟩ b₀ hb hno
  haveI : Algebra.IsQuadraticExtension D.host.F D.host.E := { finrank_eq_two' := D.sp.cm.deg2 }
  have hσ : sgE D ≠ 1 := by
    intro h
    have h1 : Module.finrank D.host.F D.host.E = 1 := by
      refine (Algebra.finrank_eq_one_iff_bijective_algebraMap).2 ⟨(algebraMap D.host.F D.host.E).injective, fun a => ?_⟩
      exact (D.sp.cm.fixed a).1 (congrArg (fun f : D.host.E ≃ₐ[D.host.F] D.host.E => f a) h)
    have h2 := D.sp.cm.deg2
    omega
  have hcard : Fintype.card ((Fin t ⊕ Fin t) ⊕ Fin W.rank) = Fintype.card (Fin B.rank) := by
    have := d.rank_add
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  let ε : (Fin t ⊕ Fin t) ⊕ Fin W.rank ≃ Fin B.rank := Fintype.equivOfCardEq hcard
  let c : D.host.E →+* D.host.E := (sgE D : D.host.E →+* D.host.E)
  have hcc : ∀ x, c (c x) = x := sgE_sgE
  have hstar : ∀ {m n : Type} (M : Matrix m n D.host.E), st c M = Mᴴ := fun M => by
    ext i j; rfl
  have hGB : st c B.gram = B.gram := by
    exact Matrix.ext fun i j => gram_herm B j i
  have hS : st c (fromCols (fromCols d.e d.e') d.i₀) * B.gram * fromCols (fromCols d.e d.e') d.i₀ =
      hsum t W.gram := by
    refine gram_sum hcc hGB ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hstar]; exact d.ee
    · rw [hstar]; exact d.e'e'
    · rw [hstar]; exact d.e'e
    · rw [← st_gram hcc hGB, hstar d.i₀, d.i₀e, st_zero]
    · rw [← st_gram hcc hGB, hstar d.i₀, d.i₀e', st_zero]
    · rw [hstar]; exact d.iso
  have hbh : ∀ i j, sgE D (b₀.1 i j) = b₀.1 j i := fun i j =>
    congrFun (congrFun b₀.2 j) i
  have key : ¬ ((∀ v : HeightOneSpectrum (𝓞 D.host.F), GlobalTheory.HermGlobal.CongrOver (sgE D) (v.adicCompletion D.host.F)
      B.gram (hhat ε b₀.1)) ∧ ∀ w : InfinitePlace D.host.F, GlobalTheory.HermGlobal.CongrOver (sgE D) w.Completion
      B.gram (hhat ε b₀.1)) := by
    rintro ⟨hf, hi⟩
    obtain ⟨P, hP, h⟩ := GlobalTheory.Published.hermitianHassePrinciple_holds D.host.F D.host.E (sgE D) hσ _ B.gram (hhat ε b₀.1)
      (gram_herm B) (fun i j => hsum_herm (c := c) hbh _ _) (gram_det_ne B)
      (by rw [hhat, det_submatrix_equiv_self]; exact det_hsum_ne_zero hb) hf hi
    obtain ⟨Q, -, hQ⟩ := cancel c hcc two_ne_zero ε (gram_herm W) (gram_det_ne W) hS hP h
    refine hno ⟨Q.map c, ?_⟩
    rw [hQ, gramQ, Matrix.map_map]
    have : (Q.map (⇑D.sp.cm.sig ∘ ⇑c)) = Q := Matrix.ext fun i j => hcc _
    rw [this, Matrix.mul_assoc]
  rw [not_and_or] at key
  rcases key with h | h
  · push Not at h
    obtain ⟨v, hv⟩ := h
    refine ⟨{v}, fun S hS e he z hz hh => hv ?_⟩
    refine congrOver_of_free _ (evFin D.host.F v) ε b₀ hb ?_ hz hh.1 hh.2.2.2
    have := he.2 v
    rw [if_pos (hS (Finset.mem_singleton_self v))] at this
    exact this
  · push Not at h
    obtain ⟨w, hw⟩ := h
    refine ⟨∅, fun S _ e he z hz hh => hw ?_⟩
    exact congrOver_of_free _ (evInf D.host.F w) ε b₀ hb (he.1 w) hz hh.1 hh.2.2.2

end Ad

end GlobalTheory.CompanionTheory.RswNoFrame
