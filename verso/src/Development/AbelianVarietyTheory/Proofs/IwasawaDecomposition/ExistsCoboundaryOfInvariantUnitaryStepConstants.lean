import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormFiniteZerosOnLineCmExt

noncomputable section

namespace GlobalTheory.GaugeAlg

open Matrix Formalism.UG

section Lin

variable {E : Type} [Field E] (s : E →+* E)

def HN {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Prop := (∀ i j, s (J j i) = J i j) ∧ J.det ≠ 0

def blk {n : ℕ} (a : E) (J : Matrix (Fin n) (Fin n) E) : Matrix (Fin (n + 1)) (Fin (n + 1)) E :=
  Matrix.of (Fin.cons (α := fun _ => Fin (n + 1) → E) (Fin.cons (α := fun _ => E) a 0)
    fun i => Fin.cons (α := fun _ => E) 0 (J i))

def two {n : ℕ} (p q r u : E) : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) E :=
  Matrix.of (Fin.cons (α := fun _ => Fin (n + 1 + 1) → E)
    (Fin.cons (α := fun _ => E) p (Fin.cons (α := fun _ => E) q 0))
    (Fin.cons (α := fun _ => Fin (n + 1 + 1) → E)
      (Fin.cons (α := fun _ => E) r (Fin.cons (α := fun _ => E) u 0))
      fun i => Fin.cons (α := fun _ => E) 0 (Fin.cons (α := fun _ => E) 0
        ((1 : Matrix (Fin n) (Fin n) E) i))))

def Cong {n : ℕ} (J K : Matrix (Fin n) (Fin n) E) : Prop :=
  ∃ P : Matrix (Fin n) (Fin n) E, P.det ≠ 0 ∧ cT s P * J * P = K

def Bin (a b a' b' : E) : Prop :=
  ∃ p q r u : E, s p * a * p + s r * b * r = a' ∧ s p * a * q + s r * b * u = 0 ∧
    s q * a * p + s u * b * r = 0 ∧ s q * a * q + s u * b * u = b'

section
variable {n : ℕ} (a b : E) (J K : Matrix (Fin n) (Fin n) E)
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem blk_00 : blk a J 0 0 = a := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem blk_0s (j : Fin n) : blk a J 0 j.succ = 0 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem cornerScalarBlockMatrix_apply_succ_zero (i : Fin n) : blk a J i.succ 0 = 0 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem blk_ss (i j : Fin n) : blk a J i.succ j.succ = J i j := rfl

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `cases i using Fin.cases <;> cases j using Fin.cases <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]`.
-/
theorem blk_mul : blk a J * blk b K = blk (a * b) (J * K) := by
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `cases i using Fin.cases <;> cases j using Fin.cases <;> simp [cT]`.
-/
theorem cT_blk : cT s (blk a J) = blk (s a) (cT s J) := by
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases <;> simp [cT]

/- English proof (translation)
Rewrite using `[Matrix.det_succ_row_zero, Fin.sum_univ_succ]`. Establish `: (blk a J).submatrix Fin.succ Fin.succ = J`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Simplify using `[this]`.
-/
theorem det_blk : (blk a J).det = a * J.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have : (blk a J).submatrix Fin.succ Fin.succ = J := by
    ext i j; simp
  simp [this]

/- English proof (translation)
Assemble the required witnesses or components as `⟨by simpa using congrFun (congrFun h 0) 0, by ext i j; simpa using congrFun (congrFun h i.succ) j.succ⟩`.
-/
theorem blk_inj {a b : E} {J K : Matrix (Fin n) (Fin n) E} (h : blk a J = blk b K) : a = b ∧ J = K :=
  ⟨by simpa using congrFun (congrFun h 0) 0, by
    ext i j; simpa using congrFun (congrFun h i.succ) j.succ⟩

/- English proof (translation)
Unfold `HN`. Rewrite using `[det_blk, mul_ne_zero_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, h1, h2⟩`. Conclude with `⟨by simpa using h 0 0, h1, fun i j => by simpa using h i.succ j.succ, h2⟩`.

Introduce and unpack `⟨h, h1, h2, h3⟩`. Use `⟨fun i j => ?_, h1, h3⟩` and prove the remaining obligations. Apply the tactic sequence `cases i using Fin.cases <;> cases j using Fin.cases <;> simp [h, h2]`.
-/
theorem hn_blk : HN s (blk a J) ↔ s a = a ∧ a ≠ 0 ∧ HN s J := by
  unfold HN
  rw [det_blk, mul_ne_zero_iff]
  constructor
  · rintro ⟨h, h1, h2⟩
    exact ⟨by simpa using h 0 0, h1, fun i j => by simpa using h i.succ j.succ, h2⟩
  · rintro ⟨h, h1, h2, h3⟩
    refine ⟨fun i j => ?_, h1, h3⟩
    cases i using Fin.cases <;> cases j using Fin.cases <;> simp [h, h2]

/- English proof (translation)
Rewrite using `[cT, Matrix.det_transpose, RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem det_cT : (cT s J).det = s J.det := by
  rw [cT, Matrix.det_transpose, RingHom.map_det]; rfl

/- English proof (translation)
Simplify using `[hform, Fin.sum_univ_succ, Fin.tail]`.
-/
theorem hform_blk (x y : Fin (n + 1) → E) :
    hform s (blk a J) x y = s (x 0) * a * y 0 + hform s J (Fin.tail x) (Fin.tail y) := by
  simp [hform, Fin.sum_univ_succ, Fin.tail]
end

/- English proof (translation)
Simplify using `only [hform, Matrix.mul_apply, cT, transpose_apply, map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.
-/
theorem gram_apply {n m : ℕ} (J : Matrix (Fin n) (Fin n) E) (P Q : Matrix (Fin n) (Fin m) E)
    (i j : Fin m) : (cT s P * J * Q) i j = hform s J (fun k => P k i) (fun k => Q k j) := by
  simp only [hform, Matrix.mul_apply, cT, transpose_apply, map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

variable {s}

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, by simp, by simp [cT_one]⟩`.
-/
theorem Cong.refl {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Cong s J J :=
  ⟨1, by simp, by simp [cT_one]⟩

/- English proof (translation)
Take `⟨P, hP, rfl⟩` from `h`. Take `⟨Q, hQ, rfl⟩` from `h'`. Conclude with `⟨P * Q, by simp [hP, hQ], by simp [cT_mul, Matrix.mul_assoc]⟩`.
-/
theorem Cong.trans {n : ℕ} {J K L : Matrix (Fin n) (Fin n) E} (h : Cong s J K) (h' : Cong s K L) :
    Cong s J L := by
  obtain ⟨P, hP, rfl⟩ := h
  obtain ⟨Q, hQ, rfl⟩ := h'
  exact ⟨P * Q, by simp [hP, hQ], by simp [cT_mul, Matrix.mul_assoc]⟩

/- English proof (translation)
Establish `h1 : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv _ (Ne.isUnit hP)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem gram_inv {n : ℕ} {J P : Matrix (Fin n) (Fin n) E} (hP : P.det ≠ 0) :
    cT s P⁻¹ * (cT s P * J * P) * P⁻¹ = J := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ (Ne.isUnit hP)
  calc _ = cT s (P * P⁻¹) * J * (P * P⁻¹) := by simp only [cT_mul, Matrix.mul_assoc]
    _ = J := by simp [h1, cT_one]

/- English proof (translation)
Take `⟨P, hP, rfl⟩` from `h`. Conclude with `⟨P⁻¹, by simp [hP], gram_inv hP⟩`.
-/
theorem Cong.symm {n : ℕ} {J K : Matrix (Fin n) (Fin n) E} (h : Cong s J K) : Cong s K J := by
  obtain ⟨P, hP, rfl⟩ := h
  exact ⟨P⁻¹, by simp [hP], gram_inv hP⟩

/- English proof (translation)
Take `⟨P, hP, rfl⟩` from `h`. Use `⟨fun i j => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[gram_apply, gram_apply]`. Simplify using `only [hform, map_sum, map_mul, hs, hJ.1]`. Rewrite using `[Finset.sum_comm]`.

Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Simplify using `[det_cT, hP, hJ.2]`.
-/
theorem Cong.hn (hs : ∀ x, s (s x) = x) {n : ℕ} {J K : Matrix (Fin n) (Fin n) E} (h : Cong s J K)
    (hJ : HN s J) : HN s K := by
  obtain ⟨P, hP, rfl⟩ := h
  refine ⟨fun i j => ?_, ?_⟩
  · rw [gram_apply, gram_apply]
    simp only [hform, map_sum, map_mul, hs, hJ.1]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · simp [det_cT, hP, hJ.2]

/- English proof (translation)
Take `⟨P, hP, rfl⟩` from `h`. Conclude with `⟨GlobalTheory.GaugeAlg.blk 1 P, by simp [det_blk, hP], by simp [cT_blk, blk_mul]⟩`.
-/
theorem Cong.blk {n : ℕ} {J K : Matrix (Fin n) (Fin n) E} (h : Cong s J K) (a : E) :
    Cong s (blk a J) (blk a K) := by
  obtain ⟨P, hP, rfl⟩ := h
  exact ⟨GlobalTheory.GaugeAlg.blk 1 P, by simp [det_blk, hP], by simp [cT_blk, blk_mul]⟩

/- English proof (translation)
Introduce `h0`. Simplify using `[h0] at h`.
-/
theorem det_ne_of_gram {n : ℕ} {J P : Matrix (Fin n) (Fin n) E} (h : (cT s P * J * P).det ≠ 0) :
    P.det ≠ 0 := by
  intro h0
  simp [h0] at h

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[gram_apply, hform_blk, hform_blk]`. Proceed by induction on `i using Fin.cases with`. Consider the case `zero`. Proceed by induction on `j using Fin.cases with`.

Consider the case `zero => simp [two, Fin.tail, hform, h1, -Fin.succ_zero_eq_one, -Fin.succ_zero_eq_one', ← add_assoc]`. Consider the case `succ j`. Apply the tactic sequence `cases j using Fin.cases <;>`. Simplify using `[two, Fin.tail, hform, h2, -Fin.succ_zero_eq_one, -Fin.succ_zero_eq_one', ← add_assoc]`. Consider the case `succ i`.

Proceed by induction on `j using Fin.cases with`. Consider the case `zero`. Apply the tactic sequence `cases i using Fin.cases <;>`. Simplify using `[two, Fin.tail, hform, h3, -Fin.succ_zero_eq_one, -Fin.succ_zero_eq_one', ← add_assoc]`. Consider the case `succ j`.

Apply the tactic sequence `cases i using Fin.cases <;> cases j using Fin.cases <;>`. Simplify using `[two, Fin.tail, hform, h4, -Fin.succ_zero_eq_one, -Fin.succ_zero_eq_one', ← add_assoc, Matrix.one_apply, apply_ite s]`.
-/
theorem two_gram {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {a b a' b' p q r u : E}
    (h1 : s p * a * p + s r * b * r = a') (h2 : s p * a * q + s r * b * u = 0)
    (h3 : s q * a * p + s u * b * r = 0) (h4 : s q * a * q + s u * b * u = b') :
    cT s (two p q r u) * blk a (blk b J) * two p q r u = blk a' (blk b' J) := by
  ext i j
  rw [gram_apply, hform_blk, hform_blk]
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => simp [two, Fin.tail, hform, h1, -Fin.succ_zero_eq_one, -Fin.succ_zero_eq_one', ← add_assoc]
    | succ j =>
      cases j using Fin.cases <;>
        simp [two, Fin.tail, hform, h2, -Fin.succ_zero_eq_one, -Fin.succ_zero_eq_one', ← add_assoc]
  | succ i =>
    induction j using Fin.cases with
    | zero =>
      cases i using Fin.cases <;>
        simp [two, Fin.tail, hform, h3, -Fin.succ_zero_eq_one, -Fin.succ_zero_eq_one', ← add_assoc]
    | succ j =>
      cases i using Fin.cases <;> cases j using Fin.cases <;>
        simp [two, Fin.tail, hform, h4, -Fin.succ_zero_eq_one, -Fin.succ_zero_eq_one', ← add_assoc,
          Matrix.one_apply, apply_ite s]

/- English proof (translation)
Take `⟨p, q, r, u, h1, h2, h3, h4⟩` from `h`. Use `two_gram J h1 h2 h3 h4` as an intermediate fact. Conclude with `⟨_, det_ne_of_gram (by rw [this]; simp [det_blk, ha, hb, hJ]), this⟩`.
-/
theorem Bin.cong {a b a' b' : E} (h : Bin s a b a' b') (ha : a' ≠ 0) (hb : b' ≠ 0) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0) : Cong s (blk a (blk b J)) (blk a' (blk b' J)) := by
  obtain ⟨p, q, r, u, h1, h2, h3, h4⟩ := h
  have := two_gram J h1 h2 h3 h4
  exact ⟨_, det_ne_of_gram (by rw [this]; simp [det_blk, ha, hb, hJ]), this⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, 1, 1, 0, by simp⟩`.
-/
theorem bin_swap (a b : E) : Bin s a b b a := ⟨0, 1, 1, 0, by simp⟩

/- English proof (translation)
Establish `hU : cT s (R⁻¹ * S) * blk a J₁ * (R⁻¹ * S) = blk a' J₂`. Rewrite using `[← h1, ← h2]`. Use `conv_rhs => rw [← gram_inv (s := s) (J := J) hR]`. Simplify using `only [cT_mul, Matrix.mul_assoc]`. Establish `hd : (R⁻¹ * S).det ≠ 0` using `by simp [hR, hS]`.

Establish `hc : ∀ i, (R⁻¹ * S) i 0 = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) i 0`. Introduce `i`. Rewrite using `[← Matrix.nonsing_inv_mul R (Ne.isUnit hR)]`. Simplify using `[Matrix.mul_apply, h0]`. Generalize the expression as in `R⁻¹ * S = U at hU hd hc`.

Establish `hr : ∀ j : Fin n, U 0 j.succ = 0`. Introduce `j`. Use `congrFun (congrFun hU 0) j.succ` as an intermediate fact. Rewrite `this` using `[gram_apply, hform_blk]`. Simplify `this` using `[hform, Fin.tail, hc, ha, Matrix.one_apply, Fin.succ_ne_zero]`.

Establish `hU' : U = blk 1 (U.submatrix Fin.succ Fin.succ)`. Use extensionality with `i j`. Apply the tactic sequence `cases i using Fin.cases <;> cases j using Fin.cases <;>`. Simplify using `[hc, hr, Matrix.one_apply, Fin.succ_ne_zero]`. Rewrite `hU` using `[hU', cT_blk, blk_mul, blk_mul]`.

Rewrite `hd` using `[hU', det_blk, one_mul]`. Conclude with `⟨_, hd, (blk_inj hU).2⟩`.
-/
theorem cong_of_col {n : ℕ} {J R S : Matrix (Fin (n + 1)) (Fin (n + 1)) E} {a a' : E}
    {J₁ J₂ : Matrix (Fin n) (Fin n) E} (hR : R.det ≠ 0) (hS : S.det ≠ 0) (ha : a ≠ 0)
    (h1 : cT s R * J * R = blk a J₁) (h2 : cT s S * J * S = blk a' J₂)
    (h0 : ∀ i, R i 0 = S i 0) : Cong s J₁ J₂ := by
  have hU : cT s (R⁻¹ * S) * blk a J₁ * (R⁻¹ * S) = blk a' J₂ := by
    rw [← h1, ← h2]
    conv_rhs => rw [← gram_inv (s := s) (J := J) hR]
    simp only [cT_mul, Matrix.mul_assoc]
  have hd : (R⁻¹ * S).det ≠ 0 := by simp [hR, hS]
  have hc : ∀ i, (R⁻¹ * S) i 0 = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) i 0 := by
    intro i
    rw [← Matrix.nonsing_inv_mul R (Ne.isUnit hR)]
    simp [Matrix.mul_apply, h0]
  generalize R⁻¹ * S = U at hU hd hc
  have hr : ∀ j : Fin n, U 0 j.succ = 0 := by
    intro j
    have := congrFun (congrFun hU 0) j.succ
    rw [gram_apply, hform_blk] at this
    simpa [hform, Fin.tail, hc, ha, Matrix.one_apply, Fin.succ_ne_zero] using this
  have hU' : U = blk 1 (U.submatrix Fin.succ Fin.succ) := by
    ext i j
    cases i using Fin.cases <;> cases j using Fin.cases <;>
      simp [hc, hr, Matrix.one_apply, Fin.succ_ne_zero]
  rw [hU', cT_blk, blk_mul, blk_mul] at hU
  rw [hU', det_blk, one_mul] at hd
  exact ⟨_, hd, (blk_inj hU).2⟩

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, x k ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Simplify using `[hform, h] at hx`. Set `P₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) E` to `((1 : Matrix _ _ E).updateCol k x).submatrix id (Equiv.swap 0 k)`.

Establish `hd : P₀.det ≠ 0`. Rewrite using `[Matrix.det_permute', ← Matrix.cramer_apply, Matrix.cramer_one]`. Use `mul_ne_zero ?_ hk` and prove the remaining obligations. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap 0 k)) with h | h <;> simp [h]`. Establish `h0 : ∀ i, P₀ i 0 = x i` using `fun i => by simp [P₀]`.

Establish `hK : HN s (cT s P₀ * J * P₀)` using `Cong.hn hs ⟨P₀, hd, rfl⟩ hJ`. Establish `hK0 : (cT s P₀ * J * P₀) 0 0 = hform s J x x`. Rewrite using `[gram_apply]`. Simplify using `only [h0]`. Use `set K := cT s P₀ * J * P₀ with hKdef`.

Use `set a := hform s J x x`. Set `U : Matrix (Fin (n + 1)) (Fin (n + 1)) E` to `(1 : Matrix _ _ E).updateRow 0 (Fin.cons (α := fun _ => E) 1 fun j => - K 0 j.succ / a)`. Establish `hUd : U.det = 1`. Rewrite using `[← Matrix.det_transpose, ← Matrix.updateCol_transpose, ← Matrix.cramer_apply, Matrix.transpose_one, Matrix.cramer_one]`. Both sides reduce to the same expression.

Establish `U0 : ∀ i, U i 0 = (Pi.single 0 1 : Fin (n + 1) → E) i` using `fun i => by`. Apply the tactic sequence `cases i using Fin.cases <;> simp [U, Fin.succ_ne_zero]`. Establish `hG : HN s (cT s U * K * U)` using `Cong.hn hs ⟨U, by simp [hUd], rfl⟩ hK`. Establish `hr : ∀ j : Fin n, (cT s U * K * U) 0 j.succ = 0`. Introduce `j`.

Rewrite using `[gram_apply]`. Simplify using `only [U0]`. Simplify using `[hform, Pi.single_apply, Fin.sum_univ_succ, U, Fin.succ_ne_zero, Matrix.one_apply, hK0]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Use `⟨P₀ * U, (cT s U * K * U).submatrix Fin.succ Fin.succ, by simp [hd, hUd], fun i => ?_, ?_⟩` and prove the remaining obligations. Simplify using `[Matrix.mul_apply, U0, Pi.single_apply, h0]`. Establish `: cT s (P₀ * U) * J * (P₀ * U) = cT s U * K * U`. Simplify using `only [hKdef, cT_mul, Matrix.mul_assoc]`. Rewrite using `[this]`.

Use extensionality with `i j`. Apply the tactic sequence `cases i using Fin.cases <;> cases j using Fin.cases`. Rewrite using `[gram_apply]`. Simplify using `only [U0]`. Simplify using `[hform, Pi.single_apply, hK0]`.

Simplify using `[hr]`. Rewrite using `[← hG.1, hr]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem exists_compl (hs : ∀ x, s (s x) = x) {n : ℕ} {J : Matrix (Fin (n + 1)) (Fin (n + 1)) E}
    (hJ : HN s J) (x : Fin (n + 1) → E) (hx : hform s J x x ≠ 0) :
    ∃ (P : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (J' : Matrix (Fin n) (Fin n) E),
      P.det ≠ 0 ∧ (∀ i, P i 0 = x i) ∧ cT s P * J * P = blk (hform s J x x) J' := by
  obtain ⟨k, hk⟩ : ∃ k, x k ≠ 0 := by
    by_contra h
    push_neg at h
    simp [hform, h] at hx
  let P₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) E :=
    ((1 : Matrix _ _ E).updateCol k x).submatrix id (Equiv.swap 0 k)
  have hd : P₀.det ≠ 0 := by
    rw [Matrix.det_permute', ← Matrix.cramer_apply, Matrix.cramer_one]
    refine mul_ne_zero ?_ hk
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap 0 k)) with h | h <;> simp [h]
  have h0 : ∀ i, P₀ i 0 = x i := fun i => by simp [P₀]
  have hK : HN s (cT s P₀ * J * P₀) := Cong.hn hs ⟨P₀, hd, rfl⟩ hJ
  have hK0 : (cT s P₀ * J * P₀) 0 0 = hform s J x x := by
    rw [gram_apply]; simp only [h0]
  set K := cT s P₀ * J * P₀ with hKdef
  set a := hform s J x x
  let U : Matrix (Fin (n + 1)) (Fin (n + 1)) E :=
    (1 : Matrix _ _ E).updateRow 0 (Fin.cons (α := fun _ => E) 1 fun j => - K 0 j.succ / a)
  have hUd : U.det = 1 := by
    rw [← Matrix.det_transpose, ← Matrix.updateCol_transpose, ← Matrix.cramer_apply,
      Matrix.transpose_one, Matrix.cramer_one]
    rfl
  have U0 : ∀ i, U i 0 = (Pi.single 0 1 : Fin (n + 1) → E) i := fun i => by
    cases i using Fin.cases <;> simp [U, Fin.succ_ne_zero]
  have hG : HN s (cT s U * K * U) := Cong.hn hs ⟨U, by simp [hUd], rfl⟩ hK
  have hr : ∀ j : Fin n, (cT s U * K * U) 0 j.succ = 0 := by
    intro j
    rw [gram_apply]
    simp only [U0]
    simp [hform, Pi.single_apply, Fin.sum_univ_succ, U, Fin.succ_ne_zero, Matrix.one_apply, hK0]
    field_simp
    ring
  refine ⟨P₀ * U, (cT s U * K * U).submatrix Fin.succ Fin.succ, by simp [hd, hUd], fun i => ?_, ?_⟩
  · simp [Matrix.mul_apply, U0, Pi.single_apply, h0]
  · have : cT s (P₀ * U) * J * (P₀ * U) = cT s U * K * U := by
      simp only [hKdef, cT_mul, Matrix.mul_assoc]
    rw [this]
    ext i j
    cases i using Fin.cases <;> cases j using Fin.cases
    · rw [gram_apply]
      simp only [U0]
      simp [hform, Pi.single_apply, hK0]
    · simp [hr]
    · rw [← hG.1, hr]; simp
    · simp

end Lin

section Chain

variable {E : Type} [Field E] [CharZero E] {s : E →+* E}

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `hd : ∀ i, J i i = 0` using `fun i => by`. Simplify `h (Pi.single i 1)` using `[hform, Pi.single_apply, apply_ite s]`. Establish `h0 : J = 0`.

Use extensionality with `i j`. Use `h (Pi.single i (J i j) + Pi.single j 1)` as an intermediate fact. Simplify using `only [hform, Pi.add_apply, map_add, add_mul, mul_add, Finset.sum_add_distrib] at this`. Simplify using `[Pi.single_apply, apply_ite s, hd] at this`. Rewrite `this` using `[← hJ.1 j i]`.

Establish `h2 : (2 : E) * (s (J i j) * J i j) = 0` using `by linear_combination this`. Simplify using `using h2`. Conclude with `hJ.2 (by simp [h0])`.
-/
theorem exists_aniso (hs : ∀ x, s (s x) = x) {n : ℕ} {J : Matrix (Fin (n + 1)) (Fin (n + 1)) E}
    (hJ : HN s J) : ∃ x, hform s J x x ≠ 0 := by
  by_contra h
  push_neg at h
  have hd : ∀ i, J i i = 0 := fun i => by
    simpa [hform, Pi.single_apply, apply_ite s] using h (Pi.single i 1)
  have h0 : J = 0 := by
    ext i j
    have := h (Pi.single i (J i j) + Pi.single j 1)
    simp only [hform, Pi.add_apply, map_add, add_mul, mul_add, Finset.sum_add_distrib] at this
    simp [Pi.single_apply, apply_ite s, hd] at this
    rw [← hJ.1 j i] at this
    have h2 : (2 : E) * (s (J i j) * J i j) = 0 := by linear_combination this
    simpa using h2
  exact hJ.2 (by simp [h0])

def Quad {V : Type} [AddCommGroup V] [Module E V] (g : V → E) : Prop :=
  ∀ u v : V, ∃ b : E, ∀ t : ℕ, g (u + (t : E) • v) = g u + b * t + g v * t ^ 2

/- English proof (translation)
Take `⟨b, hb⟩` from `h u v`. Set `p : Polynomial E` to `Polynomial.C (g u) + Polynomial.C b * Polynomial.X + Polynomial.C (g v) * Polynomial.X ^ 2`. Establish `hp : p ≠ 0`. Introduce `h0`. Establish `h1` using `congrArg (fun q => Polynomial.coeff q 0) h0`.

Establish `h2` using `congrArg (fun q => Polynomial.coeff q 2) h0`. Simplify using `[p, Polynomial.coeff_X, Polynomial.coeff_C] at h1 h2`. The claim follows by propositional logic. Use `(Polynomial.finite_setOf_isRoot hp).preimage (f := fun t : ℕ => (t : E)) (Nat.cast_injective.injOn)` as an intermediate fact. Use `this.subset fun t ht => ?_` and prove the remaining obligations.

Simplify using `only [Set.mem_setOf_eq, hb] at ht`. Simplify `ht` using `[p]`.
-/
theorem Quad.finite {V : Type} [AddCommGroup V] [Module E V] {g : V → E} (h : Quad g) {u v : V}
    (huv : g u ≠ 0 ∨ g v ≠ 0) : {t : ℕ | g (u + (t : E) • v) = 0}.Finite := by
  obtain ⟨b, hb⟩ := h u v
  let p : Polynomial E := Polynomial.C (g u) + Polynomial.C b * Polynomial.X +
    Polynomial.C (g v) * Polynomial.X ^ 2
  have hp : p ≠ 0 := by
    intro h0
    have h1 := congrArg (fun q => Polynomial.coeff q 0) h0
    have h2 := congrArg (fun q => Polynomial.coeff q 2) h0
    simp [p, Polynomial.coeff_X, Polynomial.coeff_C] at h1 h2
    tauto
  have := (Polynomial.finite_setOf_isRoot hp).preimage
    (f := fun t : ℕ => (t : E)) (Nat.cast_injective.injOn)
  refine this.subset fun t ht => ?_
  simp only [Set.mem_setOf_eq, hb] at ht
  simpa [p] using ht

/- English proof (translation)
Introduce `u v`. Use `⟨hform s J (f u) (f v) + hform s J (f v) (f u), fun t => ?_⟩` and prove the remaining obligations. Simplify using `only [hform, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, Finset.sum_mul, add_mul, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem quad_hform {V : Type} [AddCommGroup V] [Module E V] {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (f : V →ₗ[E] (Fin n → E)) : Quad fun z => hform s J (f z) (f z) := by
  intro u v
  refine ⟨hform s J (f u) (f v) + hform s J (f v) (f u), fun t => ?_⟩
  simp only [hform, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast,
    Finset.sum_mul, add_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Take `⟨u, hu⟩` from `e₁`. Take `⟨v, hv⟩` from `e₂`. Take `⟨w, hw⟩` from `e₃`. Take `⟨t, ht⟩` from `((h₁.finite (v := v) (Or.inl hu)).union (h₂.finite (u := u) (Or.inr hv))).exists_notMem`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq, not_or] at ht`.

Take `⟨t', ht'⟩` from `((h₁.finite (v := w) (Or.inl ht.1)).union ((h₂.finite (v := w) (Or.inl ht.2)).union (h₃.finite (u := u + (t : E) • v) (Or.inr hw)))).exists_notMem`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq, not_or] at ht'`. Conclude with `⟨_, ht'⟩`.
-/
theorem exists_three {V : Type} [AddCommGroup V] [Module E V] {g₁ g₂ g₃ : V → E} (h₁ : Quad g₁)
    (h₂ : Quad g₂) (h₃ : Quad g₃) (e₁ : ∃ u, g₁ u ≠ 0) (e₂ : ∃ u, g₂ u ≠ 0) (e₃ : ∃ u, g₃ u ≠ 0) :
    ∃ z, g₁ z ≠ 0 ∧ g₂ z ≠ 0 ∧ g₃ z ≠ 0 := by
  obtain ⟨u, hu⟩ := e₁
  obtain ⟨v, hv⟩ := e₂
  obtain ⟨w, hw⟩ := e₃
  obtain ⟨t, ht⟩ := ((h₁.finite (v := v) (Or.inl hu)).union
    (h₂.finite (u := u) (Or.inr hv))).exists_notMem
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at ht
  obtain ⟨t', ht'⟩ := ((h₁.finite (v := w) (Or.inl ht.1)).union
    ((h₂.finite (v := w) (Or.inl ht.2)).union
      (h₃.finite (u := u + (t : E) • v) (Or.inr hw)))).exists_notMem
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at ht'
  exact ⟨_, ht'⟩

def Adj (s : E →+* E) {n : ℕ} (a : E) (J₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (a' : E)
    (J₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) E) : Prop :=
  ∃ (b b' : E) (J₀ : Matrix (Fin n) (Fin n) E), Cong s J₁ (blk b J₀) ∧ Cong s J₂ (blk b' J₀) ∧
    Bin s a b a' b'

omit [CharZero E] in
/- English proof (translation)
Establish `h₂ : HN s (blk a' J₂)` using `Cong.hn hs ⟨R, hR, h⟩ h₁`. Rewrite `h₁`, `h₂` using `[hn_blk]`. Take `⟨P, J₀, hP, hP0, hPJ⟩` from `exists_compl hs h₁.2.2 _ hv`. Establish `ha' : a' = s (R 0 0) * a * R 0 0 + hform s J₁ (fun i => R i.succ 0) (fun i => R i.succ 0)`. Use `congrFun (congrFun h 0) 0` as an intermediate fact.

Rewrite `this` using `[gram_apply, hform_blk]`. Conclude with `this.symm`. Use `set b := hform s J₁ (fun i => R i.succ 0) (fun i => R i.succ 0)`. Establish `hb` using `(hn_blk s _ _).1 (Cong.hn hs ⟨P, hP, hPJ⟩ h₁.2.2)`. Use `set t := R 0 0 with ht`.

Establish `e1 : s t * a * t + s 1 * b * 1 = a'` using `by simp [ha']`. Establish `e2 : s t * a * (-b) + s 1 * b * (a * s t) = 0` using `by simp; ring`. Establish `e3 : s (-b) * a * t + s (a * s t) * b * 1 = 0` using `by simp [hs, hb.1, h₁.1]; ring`. Establish `e4 : s (-b) * a * (-b) + s (a * s t) * b * (a * s t) = a * b * a'`. Simplify using `[hs, hb.1, h₁.1, ha']`.

Expand and normalize the polynomial expressions, which then agree. Establish `hT` using `two_gram J₀ e1 e2 e3 e4`. Establish `hTd` using `det_ne_of_gram (s := s) (J := blk a (blk b J₀)) (P := two t (-b) 1 (a * s t)) (by rw [hT]; simp [det_blk, h₂.2.1, h₁.2.1, hb.2.1, hb.2.2.2])`. Use `⟨b, a * b * a', J₀, ⟨P, hP, hPJ⟩, ?_, t, -b, 1, a * s t, e1, e2, e3, e4⟩` and prove the remaining obligations. Use `cong_of_col (S := blk 1 P * two t (-b) 1 (a * s t)) (a' := a') hR (by simp [det_blk, hP, hTd]) h₂.2.1 h ?_ ?_` and prove the remaining obligations.

Rewrite using `[← hT, ← hPJ]`. Establish `: blk a (cT s P * J₁ * P) = cT s (blk 1 P) * blk a J₁ * blk 1 P` using `by simp [cT_blk, blk_mul]`. Rewrite using `[this]`. Simplify using `only [cT_mul, Matrix.mul_assoc]`. Introduce `i`.

Apply the tactic sequence `cases i using Fin.cases <;>`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_succ, two, hP0, ← ht, -Fin.succ_zero_eq_one, -Fin.succ_zero_eq_one']`.
-/
theorem adj_of (hs : ∀ x, s (s x) = x) {n : ℕ} {a a' : E} {J₁ J₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) E}
    (h₁ : HN s (blk a J₁)) {R : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) E} (hR : R.det ≠ 0)
    (h : cT s R * blk a J₁ * R = blk a' J₂)
    (hv : hform s J₁ (fun i => R i.succ 0) (fun i => R i.succ 0) ≠ 0) : Adj s a J₁ a' J₂ := by
  have h₂ : HN s (blk a' J₂) := Cong.hn hs ⟨R, hR, h⟩ h₁
  rw [hn_blk] at h₁ h₂
  obtain ⟨P, J₀, hP, hP0, hPJ⟩ := exists_compl hs h₁.2.2 _ hv
  have ha' : a' = s (R 0 0) * a * R 0 0 + hform s J₁ (fun i => R i.succ 0) (fun i => R i.succ 0) := by
    have := congrFun (congrFun h 0) 0
    rw [gram_apply, hform_blk] at this
    exact this.symm
  set b := hform s J₁ (fun i => R i.succ 0) (fun i => R i.succ 0)
  have hb := (hn_blk s _ _).1 (Cong.hn hs ⟨P, hP, hPJ⟩ h₁.2.2)
  set t := R 0 0 with ht
  have e1 : s t * a * t + s 1 * b * 1 = a' := by simp [ha']
  have e2 : s t * a * (-b) + s 1 * b * (a * s t) = 0 := by simp; ring
  have e3 : s (-b) * a * t + s (a * s t) * b * 1 = 0 := by simp [hs, hb.1, h₁.1]; ring
  have e4 : s (-b) * a * (-b) + s (a * s t) * b * (a * s t) = a * b * a' := by
    simp [hs, hb.1, h₁.1, ha']; ring
  have hT := two_gram J₀ e1 e2 e3 e4
  have hTd := det_ne_of_gram (s := s) (J := blk a (blk b J₀)) (P := two t (-b) 1 (a * s t))
    (by rw [hT]; simp [det_blk, h₂.2.1, h₁.2.1, hb.2.1, hb.2.2.2])
  refine ⟨b, a * b * a', J₀, ⟨P, hP, hPJ⟩, ?_, t, -b, 1, a * s t, e1, e2, e3, e4⟩
  refine cong_of_col (S := blk 1 P * two t (-b) 1 (a * s t)) (a' := a') hR
    (by simp [det_blk, hP, hTd]) h₂.2.1 h ?_ ?_
  · rw [← hT, ← hPJ]
    have : blk a (cT s P * J₁ * P) = cT s (blk 1 P) * blk a J₁ * blk 1 P := by simp [cT_blk, blk_mul]
    rw [this]
    simp only [cT_mul, Matrix.mul_assoc]
  · intro i
    cases i using Fin.cases <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, two, hP0, ← ht, -Fin.succ_zero_eq_one,
        -Fin.succ_zero_eq_one']

/- English proof (translation)
Establish `h₂ : HN s (blk a' J₂)` using `h.hn hs h₁`. Take `⟨R, hR, hRJ⟩` from `h.symm`. Set `tl : (Fin (n + 1 + 1) → E) →ₗ[E] (Fin (n + 1) → E)` to `LinearMap.funLeft E E Fin.succ`. Take `⟨w₁, hw₁⟩` from `exists_aniso hs ((hn_blk s _ _).1 h₁).2.2`. Take `⟨w₂, hw₂⟩` from `exists_aniso hs ((hn_blk s _ _).1 h₂).2.2`.

Take `⟨z, hz, hz₁, hz₂⟩` from `exists_three (quad_hform (s := s) (blk a J₁) LinearMap.id) (quad_hform (s := s) J₁ tl) (quad_hform (s := s) J₂ (tl ∘ₗ R.mulVecLin)) (exists_aniso hs h₁) ⟨Fin.cons 0 w₁, hw₁⟩ ⟨R⁻¹ *ᵥ Fin.cons 0 w₂, by`. Simplify using `only [LinearMap.comp_apply, mulVecLin_apply, mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit hR), one_mulVec]`. Conclude with `hw₂⟩`. Take `⟨P, J₃, hP, hP0, hPJ⟩` from `exists_compl hs h₁ z hz`. Use `⟨_, J₃, ⟨P, hP, hPJ⟩, adj_of hs h₁ hP hPJ ?_, adj_of hs h₂ (R := R * P) (by simp [hR, hP]) ?_ ?_⟩` and prove the remaining obligations.

Simplify using `only [hP0]`. Conclude with `hz₁`. Rewrite using `[← hPJ, ← hRJ]`. Simplify using `only [cT_mul, Matrix.mul_assoc]`. Simplify using `only [Matrix.mul_apply, hP0]`.

Conclude with `hz₂`.
-/
theorem chain (hs : ∀ x, s (s x) = x) {n : ℕ} {a a' : E} {J₁ J₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) E}
    (h₁ : HN s (blk a J₁)) (h : Cong s (blk a J₁) (blk a' J₂)) :
    ∃ (a'' : E) (J₃ : Matrix (Fin (n + 1)) (Fin (n + 1)) E), Cong s (blk a J₁) (blk a'' J₃) ∧
      Adj s a J₁ a'' J₃ ∧ Adj s a' J₂ a'' J₃ := by
  have h₂ : HN s (blk a' J₂) := h.hn hs h₁
  obtain ⟨R, hR, hRJ⟩ := h.symm
  let tl : (Fin (n + 1 + 1) → E) →ₗ[E] (Fin (n + 1) → E) := LinearMap.funLeft E E Fin.succ
  obtain ⟨w₁, hw₁⟩ := exists_aniso hs ((hn_blk s _ _).1 h₁).2.2
  obtain ⟨w₂, hw₂⟩ := exists_aniso hs ((hn_blk s _ _).1 h₂).2.2
  obtain ⟨z, hz, hz₁, hz₂⟩ := exists_three (quad_hform (s := s) (blk a J₁) LinearMap.id)
    (quad_hform (s := s) J₁ tl) (quad_hform (s := s) J₂ (tl ∘ₗ R.mulVecLin)) (exists_aniso hs h₁)
    ⟨Fin.cons 0 w₁, hw₁⟩ ⟨R⁻¹ *ᵥ Fin.cons 0 w₂, by
      simp only [LinearMap.comp_apply, mulVecLin_apply, mulVec_mulVec,
        Matrix.mul_nonsing_inv _ (Ne.isUnit hR), one_mulVec]
      exact hw₂⟩
  obtain ⟨P, J₃, hP, hP0, hPJ⟩ := exists_compl hs h₁ z hz
  refine ⟨_, J₃, ⟨P, hP, hPJ⟩, adj_of hs h₁ hP hPJ ?_, adj_of hs h₂ (R := R * P) (by simp [hR, hP]) ?_ ?_⟩
  · simp only [hP0]; exact hz₁
  · rw [← hPJ, ← hRJ]; simp only [cT_mul, Matrix.mul_assoc]
  · simp only [Matrix.mul_apply, hP0]; exact hz₂

end Chain

section Cob

variable {E : Type} [Field E] {s : E →+* E} {Γ : Type} [CommGroup Γ]

open Classical in

def pot (s : E →+* E) (C : ∀ n : ℕ, E → Matrix (Fin n) (Fin n) E → Γ) :
    ∀ n : ℕ, Matrix (Fin n) (Fin n) E → Γ :=
  fun n => Nat.rec (motive := fun n => Matrix (Fin n) (Fin n) E → Γ) (fun _ => 1)
    (fun n A J => if h : ∃ p : E × Matrix (Fin n) (Fin n) E, Cong s J (blk p.1 p.2) then
      C n h.choose.1 h.choose.2 * A h.choose.2 else 1) n

/- English proof (translation)
The claim follows from `dif_pos h`.
-/
theorem pot_succ (C : ∀ n : ℕ, E → Matrix (Fin n) (Fin n) E → Γ) {n : ℕ}
    {J : Matrix (Fin (n + 1)) (Fin (n + 1)) E}
    (h : ∃ p : E × Matrix (Fin n) (Fin n) E, Cong s J (blk p.1 p.2)) :
    pot s C (n + 1) J = C n h.choose.1 h.choose.2 * pot s C n h.choose.2 := dif_pos h

/- English proof (translation)
Take `⟨x, hx⟩` from `exists_aniso hs hJ`. Take `⟨P, J', h1, -, h2⟩` from `exists_compl hs hJ x hx`. Conclude with `⟨(_, J'), P, h1, h2⟩`.
-/
theorem exists_blk [CharZero E] (hs : ∀ x, s (s x) = x) {n : ℕ}
    {J : Matrix (Fin (n + 1)) (Fin (n + 1)) E} (hJ : HN s J) :
    ∃ p : E × Matrix (Fin n) (Fin n) E, Cong s J (blk p.1 p.2) := by
  obtain ⟨x, hx⟩ := exists_aniso hs hJ
  obtain ⟨P, J', h1, -, h2⟩ := exists_compl hs hJ x hx
  exact ⟨(_, J'), P, h1, h2⟩

/- English proof (translation)
Establish `step : ∀ n, (∀ a J₁ a' J₂, HN s (blk a J₁) → Cong s (blk a J₁) (blk a' J₂) → C n a J₁ * pot s C n J₁ = C n a' J₂ * pot s C n J₂) → ∀ J a J', HN s J → Cong s J (blk a J') → pot s C (n + 1) J = C n a J' * pot s C n J'`. Introduce `n key J a J' hJ h`. Establish `he` using `exists_blk hs hJ`. Rewrite using `[pot_succ C he]`. Conclude with `key _ _ _ _ (he.choose_spec.hn hs hJ) (he.choose_spec.symm.trans h)`.

Establish `key : ∀ n a J₁ a' J₂, HN s (blk a J₁) → Cong s (blk a J₁) (blk a' J₂) → C n a J₁ * pot s C n J₁ = C n a' J₂ * pot s C n J₂`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `a J₁ a' J₂ hJ h`.

Take `rfl : J₁ = J₂` from `Subsingleton.elim _ _`. Establish `hJ'` using `h.hn hs hJ`. Establish `ho : ∀ K : Matrix (Fin 1) (Fin 1) E, HN s K → HN s (blk 1 K)` using `fun K hK => (hn_blk s _ _).2 ⟨map_one s, one_ne_zero, hK⟩`. Establish `hb : Bin s 1 a 1 a'`. Take `⟨P, -, hP⟩` from `h`.

Use `congrFun (congrFun hP 0) 0` as an intermediate fact. Rewrite `this` using `[gram_apply, hform_blk]`. Conclude with `⟨1, 0, 0, P 0 0, by simp, by simp, by simp, by simpa [hform] using this⟩`. Use `h2 0 1 a 1 a' J₁ (ho _ hJ) (ho _ hJ') hb` as an intermediate fact. Rewrite `this` using `[h1 _ 1 _ _ (ho _ hJ) h]`.

Rewrite using `[mul_left_cancel this]`. Consider the case `succ n ih`. Establish `adj : ∀ a J₁ a' J₂, HN s (blk a J₁) → HN s (blk a' J₂) → Adj s a J₁ a' J₂ → C (n + 1) a J₁ * pot s C (n + 1) J₁ = C (n + 1) a' J₂ * pot s C (n + 1) J₂`. Introduce and unpack `a J₁ a' J₂ g₁ g₂ ⟨b, b', J₀, c₁, c₂, hb⟩`. Rewrite using `[step n ih J₁ b J₀ ((hn_blk s _ _).1 g₁).2.2 c₁, step n ih J₂ b' J₀ ((hn_blk s _ _).1 g₂).2.2 c₂, h1 _ a _ _ g₁ c₁, h1 _ a' _ _ g₂ c₂, ← mul_assoc, ← mul_assoc, h2 n a b a' b' J₀ ((c₁.blk a).hn hs g₁) ((c₂.blk a').hn hs g₂) hb]`.

Introduce `a J₁ a' J₂ hJ h`. Take `⟨a'', J₃, c, d₁, d₂⟩` from `chain hs hJ h`. Rewrite using `[adj _ _ _ _ hJ (c.hn hs hJ) d₁, adj _ _ _ _ (h.hn hs hJ) (c.hn hs hJ) d₂]`. Use `⟨pot s C, fun n J K hJ h => ?_, fun n => step n (key n)⟩` and prove the remaining obligations. Consider the cases of `n with`.

Consider the case `zero => rfl`. Consider the case `succ n`. Take `⟨p, hp⟩` from `exists_blk hs hJ`. Rewrite using `[step n (key n) J _ _ hJ hp, step n (key n) K _ _ (h.hn hs hJ) (h.symm.trans hp)]`.
-/
theorem cob_all [CharZero E] (hs : ∀ x, s (s x) = x) (C : ∀ n : ℕ, E → Matrix (Fin n) (Fin n) E → Γ)
    (h1 : ∀ n a J K, HN s (blk a J) → Cong s J K → C n a J = C n a K)
    (h2 : ∀ n a b a' b' J, HN s (blk a (blk b J)) → HN s (blk a' (blk b' J)) → Bin s a b a' b' →
      C (n + 1) a (blk b J) * C n b J = C (n + 1) a' (blk b' J) * C n b' J) :
    ∃ A : ∀ n : ℕ, Matrix (Fin n) (Fin n) E → Γ, (∀ n J K, HN s J → Cong s J K → A n J = A n K) ∧
      ∀ n J a J', HN s J → Cong s J (blk a J') → A (n + 1) J = C n a J' * A n J' := by
  have step : ∀ n, (∀ a J₁ a' J₂, HN s (blk a J₁) → Cong s (blk a J₁) (blk a' J₂) →
      C n a J₁ * pot s C n J₁ = C n a' J₂ * pot s C n J₂) →
      ∀ J a J', HN s J → Cong s J (blk a J') → pot s C (n + 1) J = C n a J' * pot s C n J' := by
    intro n key J a J' hJ h
    have he := exists_blk hs hJ
    rw [pot_succ C he]
    exact key _ _ _ _ (he.choose_spec.hn hs hJ) (he.choose_spec.symm.trans h)
  have key : ∀ n a J₁ a' J₂, HN s (blk a J₁) → Cong s (blk a J₁) (blk a' J₂) →
      C n a J₁ * pot s C n J₁ = C n a' J₂ * pot s C n J₂ := by
    intro n
    induction n with
    | zero =>
      intro a J₁ a' J₂ hJ h
      obtain rfl : J₁ = J₂ := Subsingleton.elim _ _
      have hJ' := h.hn hs hJ
      have ho : ∀ K : Matrix (Fin 1) (Fin 1) E, HN s K → HN s (blk 1 K) := fun K hK =>
        (hn_blk s _ _).2 ⟨map_one s, one_ne_zero, hK⟩
      have hb : Bin s 1 a 1 a' := by
        obtain ⟨P, -, hP⟩ := h
        have := congrFun (congrFun hP 0) 0
        rw [gram_apply, hform_blk] at this
        exact ⟨1, 0, 0, P 0 0, by simp, by simp, by simp, by simpa [hform] using this⟩
      have := h2 0 1 a 1 a' J₁ (ho _ hJ) (ho _ hJ') hb
      rw [h1 _ 1 _ _ (ho _ hJ) h] at this
      rw [mul_left_cancel this]
    | succ n ih =>
      have adj : ∀ a J₁ a' J₂, HN s (blk a J₁) → HN s (blk a' J₂) → Adj s a J₁ a' J₂ →
          C (n + 1) a J₁ * pot s C (n + 1) J₁ = C (n + 1) a' J₂ * pot s C (n + 1) J₂ := by
        rintro a J₁ a' J₂ g₁ g₂ ⟨b, b', J₀, c₁, c₂, hb⟩
        rw [step n ih J₁ b J₀ ((hn_blk s _ _).1 g₁).2.2 c₁, step n ih J₂ b' J₀ ((hn_blk s _ _).1 g₂).2.2 c₂,
          h1 _ a _ _ g₁ c₁, h1 _ a' _ _ g₂ c₂, ← mul_assoc, ← mul_assoc,
          h2 n a b a' b' J₀ ((c₁.blk a).hn hs g₁) ((c₂.blk a').hn hs g₂) hb]
      intro a J₁ a' J₂ hJ h
      obtain ⟨a'', J₃, c, d₁, d₂⟩ := chain hs hJ h
      rw [adj _ _ _ _ hJ (c.hn hs hJ) d₁, adj _ _ _ _ (h.hn hs hJ) (c.hn hs hJ) d₂]
  refine ⟨pot s C, fun n J K hJ h => ?_, fun n => step n (key n)⟩
  cases n with
  | zero => rfl
  | succ n =>
    obtain ⟨p, hp⟩ := exists_blk hs hJ
    rw [step n (key n) J _ _ hJ hp, step n (key n) K _ _ (h.hn hs hJ) (h.symm.trans hp)]

/- English proof (translation)
Establish `ho : ∀ {n : ℕ} {K : Matrix (Fin n) (Fin n) E}, HN s K → HN s (blk 1 K)` using `fun hK => (hn_blk s _ _).2 ⟨map_one s, one_ne_zero, hK⟩`. Establish `sw : ∀ {n : ℕ} {a : E} {K : Matrix (Fin n) (Fin n) E}, HN s (blk a K) → Cong s (blk 1 (blk a K)) (blk a (blk 1 K))` using `fun hK => (bin_swap 1 _).cong ((hn_blk s _ _).1 hK).2.1 one_ne_zero ((hn_blk s _ _).1 hK).2.2.2`. Establish `hs1 : ∀ {n : ℕ} {a : E} {K : Matrix (Fin n) (Fin n) E}, HN s (blk a K) → HN s (blk a (blk 1 K))` using `fun hK => (sw hK).hn hs (ho hK)`. Take `⟨A, hA1, hA2⟩` from `cob_all hs (fun n a J => C (n + 1 + 1) a (blk 1 (blk 1 J))) (fun n a J K hJ h => h1 _ a _ _ (by omega) (hs1 (hs1 hJ)) ((h.blk 1).blk 1)) (fun n a b a' b' J g g' hb => by`. Establish `e : ∀ {a b : E}, HN s (blk a (blk b J)) → Cong s (blk 1 (blk 1 (blk b J))) (blk b (blk 1 (blk 1 J)))` using `fun g => ((sw ((hn_blk s _ _).1 g).2.2).blk 1).trans (sw (hs1 ((hn_blk s _ _).1 g).2.2))`.

Rewrite using `[h1 _ a _ _ (by omega) (hs1 (hs1 g)) (e g), h1 _ a' _ _ (by omega) (hs1 (hs1 g')) (e g')]`. Conclude with `h2 _ a b a' b' _ (by omega) (((e g).blk a).hn hs (hs1 (hs1 g))) (((e g').blk a').hn hs (hs1 (hs1 g'))) hb)`. Establish `inv : ∀ n J K, 2 ≤ n → HN s J → Cong s J K → A n J / (C n 1 J * C (n + 1) 1 (blk 1 J)) = A n K / (C n 1 K * C (n + 1) 1 (blk 1 K))`. Introduce `n J K hn hJ h`. Rewrite using `[hA1 n J K hJ h, h1 n 1 J K hn (ho hJ) h, h1 (n + 1) 1 _ _ (by omega) (ho (ho hJ)) (h.blk 1)]`.

Use `⟨fun n J => if 2 ≤ n then A n J / (C n 1 J * C (n + 1) 1 (blk 1 J)) else 1, fun n J K hJ h => ?_, fun n J a J' hn hJ h => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hn : 2 ≤ n`. Simplify using `only [hn, if_true]`. Conclude with `inv n J K hn hJ h`. Simplify using `only [hn, if_false]`.

Establish `hn' : 2 ≤ n + 1` using `by omega`. Establish `g` using `h.hn hs hJ`. Simplify using `only [hn, hn', if_true]`. Rewrite using `[inv _ _ _ hn' hJ h, hA2 n _ a J' g (Cong.refl _), h1 _ 1 _ _ (by omega) (ho (ho g)) (sw g)]`. Establish `q1` using `h2 n 1 a a 1 J' hn (ho g) (hs1 g) (bin_swap _ _)`.

Establish `q2` using `h2 (n + 1) 1 a a 1 (blk 1 J') hn' (ho (hs1 g)) (hs1 (hs1 g)) (bin_swap _ _)`. Rewrite `q1`, `q2` using `[← eq_mul_inv_iff_mul_eq]`. Rewrite using `[q1, q2]`. Simplify using `only [div_eq_mul_inv, _root_.mul_inv_rev, inv_inv]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws.
-/
theorem cob_two [CharZero E] (hs : ∀ x, s (s x) = x) (C : ∀ n : ℕ, E → Matrix (Fin n) (Fin n) E → Γ)
    (h1 : ∀ n a J K, 2 ≤ n → HN s (blk a J) → Cong s J K → C n a J = C n a K)
    (h2 : ∀ n a b a' b' J, 2 ≤ n → HN s (blk a (blk b J)) → HN s (blk a' (blk b' J)) → Bin s a b a' b' →
      C (n + 1) a (blk b J) * C n b J = C (n + 1) a' (blk b' J) * C n b' J) :
    ∃ A : ∀ n : ℕ, Matrix (Fin n) (Fin n) E → Γ, (∀ n J K, HN s J → Cong s J K → A n J = A n K) ∧
      ∀ n J a J', 2 ≤ n → HN s J → Cong s J (blk a J') → A (n + 1) J = C n a J' * A n J' := by
  have ho : ∀ {n : ℕ} {K : Matrix (Fin n) (Fin n) E}, HN s K → HN s (blk 1 K) := fun hK =>
    (hn_blk s _ _).2 ⟨map_one s, one_ne_zero, hK⟩
  have sw : ∀ {n : ℕ} {a : E} {K : Matrix (Fin n) (Fin n) E}, HN s (blk a K) →
      Cong s (blk 1 (blk a K)) (blk a (blk 1 K)) := fun hK =>
    (bin_swap 1 _).cong ((hn_blk s _ _).1 hK).2.1 one_ne_zero ((hn_blk s _ _).1 hK).2.2.2
  have hs1 : ∀ {n : ℕ} {a : E} {K : Matrix (Fin n) (Fin n) E}, HN s (blk a K) →
      HN s (blk a (blk 1 K)) := fun hK => (sw hK).hn hs (ho hK)
  obtain ⟨A, hA1, hA2⟩ := cob_all hs (fun n a J => C (n + 1 + 1) a (blk 1 (blk 1 J)))
    (fun n a J K hJ h => h1 _ a _ _ (by omega) (hs1 (hs1 hJ)) ((h.blk 1).blk 1))
    (fun n a b a' b' J g g' hb => by
      have e : ∀ {a b : E}, HN s (blk a (blk b J)) →
          Cong s (blk 1 (blk 1 (blk b J))) (blk b (blk 1 (blk 1 J))) := fun g =>
        ((sw ((hn_blk s _ _).1 g).2.2).blk 1).trans (sw (hs1 ((hn_blk s _ _).1 g).2.2))
      rw [h1 _ a _ _ (by omega) (hs1 (hs1 g)) (e g), h1 _ a' _ _ (by omega) (hs1 (hs1 g')) (e g')]
      exact h2 _ a b a' b' _ (by omega) (((e g).blk a).hn hs (hs1 (hs1 g)))
        (((e g').blk a').hn hs (hs1 (hs1 g'))) hb)
  have inv : ∀ n J K, 2 ≤ n → HN s J → Cong s J K →
      A n J / (C n 1 J * C (n + 1) 1 (blk 1 J)) = A n K / (C n 1 K * C (n + 1) 1 (blk 1 K)) := by
    intro n J K hn hJ h
    rw [hA1 n J K hJ h, h1 n 1 J K hn (ho hJ) h, h1 (n + 1) 1 _ _ (by omega) (ho (ho hJ)) (h.blk 1)]
  refine ⟨fun n J => if 2 ≤ n then A n J / (C n 1 J * C (n + 1) 1 (blk 1 J)) else 1,
    fun n J K hJ h => ?_, fun n J a J' hn hJ h => ?_⟩
  · by_cases hn : 2 ≤ n
    · simp only [hn, if_true]; exact inv n J K hn hJ h
    · simp only [hn, if_false]
  · have hn' : 2 ≤ n + 1 := by omega
    have g := h.hn hs hJ
    simp only [hn, hn', if_true]
    rw [inv _ _ _ hn' hJ h, hA2 n _ a J' g (Cong.refl _), h1 _ 1 _ _ (by omega) (ho (ho g)) (sw g)]
    have q1 := h2 n 1 a a 1 J' hn (ho g) (hs1 g) (bin_swap _ _)
    have q2 := h2 (n + 1) 1 a a 1 (blk 1 J') hn' (ho (hs1 g)) (hs1 (hs1 g)) (bin_swap _ _)
    rw [← eq_mul_inv_iff_mul_eq] at q1 q2
    rw [q1, q2]
    simp only [div_eq_mul_inv, _root_.mul_inv_rev, inv_inv]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

end Cob

section Main

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}

def incl (E : Type) [Field E] (n : ℕ) : Matrix (Fin (n + 1)) (Fin n) E :=
  (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) E).submatrix id Fin.succ

def e0 (E : Type) [Field E] (n : ℕ) : Fin 1 → Fin (n + 1) → E := fun _ => Pi.single 0 1

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[incl, Matrix.mul_apply, Matrix.one_apply]`.
-/
theorem mul_incl {m n : ℕ} (P : Matrix (Fin m) (Fin (n + 1)) E) :
    P * incl E n = P.submatrix id Fin.succ := by
  ext i j
  simp [incl, Matrix.mul_apply, Matrix.one_apply]

/- English proof (translation)
Rewrite `h'` using `[hn_blk]`. Rewrite using `[mul_incl]`. Use `⟨hJ, fun h0 => h'.2.1 (by simp [h0]), ?_, fun j => ?_, ?_, h'.2.2⟩` and prove the remaining obligations. Use `congrFun (congrFun h 0) 0` as an intermediate fact. Rewrite `this` using `[gram_apply]`. Then use the resulting hypothesis.

Use `congrFun (congrFun h 0) j.succ` as an intermediate fact. Rewrite `this` using `[gram_apply]`. Then use the resulting hypothesis. Use extensionality with `i j`. Use `congrFun (congrFun h i.succ) j.succ` as an intermediate fact. Rewrite `this` using `[gram_apply]`.

Rewrite using `[gram_apply]`. Conclude with `this.symm`.
-/
theorem stepData_of {n : ℕ} {J P : Matrix (Fin (n + 1)) (Fin (n + 1)) E} {a : F}
    {J' : Matrix (Fin n) (Fin n) E} (hJ : HN (σ : E →+* E) J)
    (h' : HN (σ : E →+* E) (blk (algebraMap F E a) J'))
    (h : cT (σ : E →+* E) P * J * P = blk (algebraMap F E a) J') :
    StepData σ J (fun _ i => P i 0) a (P * incl E n) J' := by
  rw [hn_blk] at h'
  rw [mul_incl]
  refine ⟨hJ, fun h0 => h'.2.1 (by simp [h0]), ?_, fun j => ?_, ?_, h'.2.2⟩
  · have := congrFun (congrFun h 0) 0
    rwa [gram_apply] at this
  · have := congrFun (congrFun h 0) j.succ
    rwa [gram_apply] at this
  · ext i j
    have := congrFun (congrFun h i.succ) j.succ
    rw [gram_apply] at this
    rw [gram_apply]
    exact this.symm

/- English proof (translation)
Use `stepData_of (P := 1) h' h' (by simp [cT_one])` as an intermediate fact. Rewrite `this` using `[Matrix.one_mul]`. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `_ i`. Simplify using `[e0, Pi.single_apply, Matrix.one_apply]`.
-/
theorem stepData_std {n : ℕ} {a : F} {J' : Matrix (Fin n) (Fin n) E}
    (h' : HN (σ : E →+* E) (blk (algebraMap F E a) J')) :
    StepData σ (blk (algebraMap F E a) J') (e0 E n) a (incl E n) J' := by
  have := stepData_of (P := 1) h' h' (by simp [cT_one])
  rw [Matrix.one_mul] at this
  convert this using 1
  ext _ i
  simp [e0, Pi.single_apply, Matrix.one_apply]

/- English proof (translation)
Take `⟨hJ, ha, h1, h2, h3, h4⟩` from `h`. Establish `e : cT (σ : E →+* E) (consCol x B) * J * consCol x B = blk (algebraMap F E a) J'`. Use extensionality with `i j`. Rewrite using `[gram_apply]`. Apply the tactic sequence `cases i using Fin.cases <;> cases j using Fin.cases`.

Conclude with `h1`. Conclude with `h2 _`. Name the introduced variables `i`. Use `congrArg σ (h2 i)` as an intermediate fact. Simplify using `only [hE, hform, map_sum, map_mul, RingHom.coe_coe, hs, hJ.1, map_zero] at this`.

Rewrite `this` using `[Finset.sum_comm]`. Rewrite using `[cornerScalarBlockMatrix_apply_succ_zero, ← this]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by`. Simplify using `[consCol]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[blk_ss, h3, gram_apply]`. Both sides reduce to the same expression. Conclude with `⟨det_ne_of_gram (by rw [e]; simp [det_blk, ha, h4.2]), e⟩`.
-/
theorem gram_consCol (hs : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin (n + 1)) (Fin (n + 1)) E}
    {x : Fin 1 → Fin (n + 1) → E} {a : F} {B : Matrix (Fin (n + 1)) (Fin n) E}
    {J' : Matrix (Fin n) (Fin n) E} (h : StepData σ J x a B J') :
    (consCol x B).det ≠ 0 ∧
      cT (σ : E →+* E) (consCol x B) * J * consCol x B = blk (algebraMap F E a) J' := by
  obtain ⟨hJ, ha, h1, h2, h3, h4⟩ := h
  have e : cT (σ : E →+* E) (consCol x B) * J * consCol x B = blk (algebraMap F E a) J' := by
    ext i j
    rw [gram_apply]
    cases i using Fin.cases <;> cases j using Fin.cases
    · exact h1
    · exact h2 _
    · rename_i i
      have := congrArg σ (h2 i)
      simp only [hE, hform, map_sum, map_mul, RingHom.coe_coe, hs, hJ.1, map_zero] at this
      rw [Finset.sum_comm] at this
      rw [cornerScalarBlockMatrix_apply_succ_zero, ← this]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
        simp [consCol]; ring
    · rw [blk_ss, h3, gram_apply]; rfl
  exact ⟨det_ne_of_gram (by rw [e]; simp [det_blk, ha, h4.2]), e⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ Γ _ c H1 H2`. Establish `hs : ∀ x, σ (σ x) = x` using `GlobalTheory.HermLineZeros.conj_invol hσ`. Establish `hF : ∀ {n : ℕ} {a : E} {J : Matrix (Fin n) (Fin n) E}, HN (σ : E →+* E) (blk a J) → ∃ a₀ : F, algebraMap F E a₀ = a` using `fun h => GlobalTheory.HermLineZeros.exists_of_fixed hσ _ ((hn_blk _ _ _).1 h).1`. Establish `std : ∀ M J x a B J', 2 ≤ M → StepData σ J x a B J' → c M J x B = c M (blk (algebraMap F E a) J') (e0 E M) (incl E M)`. Introduce `M J x a B J' hM h`.

Take `⟨hd, e⟩` from `gram_consCol hs h`. Use `H1 M J x a B J' (e0 E M) (incl E M) (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd) 1 hM h (by ext i; simp [e0, consCol]) (by ext i j; simp [mul_incl, consCol])` as an intermediate fact. Rewrite using `[← this, ← e]`. Both sides reduce to the same expression. Take `⟨A, hA1, hA2⟩` from `cob_two (s := (σ : E →+* E)) hs (fun n a J => c n (blk a J) (e0 E n) (incl E n)) (by`.

Introduce and unpack `n a J K hn hJ ⟨Q, hQ, rfl⟩`. Take `⟨a, rfl⟩` from `hF hJ`. Establish `hd : (blk 1 Q).det ≠ 0` using `by simp [det_blk, hQ]`. Apply the tactic sequence `have := H1 n _ _ a _ J (e0 E n) (incl E n) (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd) (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hQ) hn (stepData_std hJ) (by ext i; cases i using Fin.cases <;> simp [e0]) (by`. Use extensionality with `i j`.

Rewrite using `[mul_incl]`. Apply the tactic sequence `cases i using Fin.cases <;>`. Simplify using `[incl, Matrix.mul_apply, Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm])`. Rewrite using `[← this]`. Simplify using `[cT_blk, blk_mul])`.

Use the proof step `(by`. Introduce and unpack `n a b a' b' J hn g g' ⟨p, q, r, u, e1, e2, e3, e4⟩`. Establish `hT` using `two_gram J e1 e2 e3 e4`. Establish `g1` using `((hn_blk _ _ _).1 g).2.2`. Establish `g1'` using `((hn_blk _ _ _).1 g').2.2`.

Take `⟨a, rfl⟩` from `hF g`. Take `⟨b, rfl⟩` from `hF g1`. Take `⟨a', rfl⟩` from `hF g'`. Take `⟨b', rfl⟩` from `hF g1'`. Establish `sd` using `stepData_of g g' hT`.

Use `H2 n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J hn (stepData_std g) (stepData_std g1) sd (stepData_std g1') (by` as an intermediate fact. Rewrite using `[mul_incl, mul_incl, mul_incl]`. Use extensionality with `i j`. Proceed by induction on `i using Fin.cases with`. Consider the case `zero => simp [two, incl, (Fin.succ_ne_zero _).symm]`.

Consider the case `succ i`. Apply the tactic sequence `cases i using Fin.cases <;>`. Simplify using `[two, incl, (Fin.succ_ne_zero _).symm, Matrix.one_apply, -Fin.succ_zero_eq_one, -Fin.succ_zero_eq_one'])`. Rewrite using `[this, std _ _ _ _ _ _ (by omega) sd])`. Use `⟨A, fun M J P hJ => (hA1 M J _ hJ ⟨P, P.det_ne_zero, rfl⟩).symm, fun M J x a B J' hM h => ?_⟩` and prove the remaining obligations.

Take `⟨hd, e⟩` from `gram_consCol hs h`. Rewrite using `[hA2 M J _ J' hM h.1 ⟨_, hd, e⟩, std M J x a B J' hM h]`.
-/
theorem exists_coboundary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (Γ : Type) [CommGroup Γ] (c : ∀ M : ℕ, Matrix (Fin (M + 1)) (Fin (M + 1)) E → (Fin 1 → Fin (M + 1) → E) → Matrix (Fin (M + 1)) (Fin M) E → Γ), (∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (x₂ : Fin 1 → Fin (M + 1) → E) (B₂ : Matrix (Fin (M + 1)) (Fin M) E) (P : GL (Fin (M + 1)) E) (Q : GL (Fin M) E), 2 ≤ M → StepData σ J x a B J' → (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E).mulVec (x₂ 0) = x 0 → (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) * B₂ = B * (Q : Matrix (Fin M) (Fin M) E) → c M (Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) * J * (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E)) x₂ B₂ = c M J x B) → (∀ (M : ℕ) (J : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) E) (x₁ x₂ : Fin 1 → Fin (M + 1 + 1) → E) (a₁ a₂ : F) (B₁ B₂ : Matrix (Fin (M + 1 + 1)) (Fin (M + 1)) E) (J₁ J₂ : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (y₁ y₂ : Fin 1 → Fin (M + 1) → E) (b₁ b₂ : F) (C₁ C₂ : Matrix (Fin (M + 1)) (Fin M) E) (J₀ : Matrix (Fin M) (Fin M) E), 2 ≤ M → StepData σ J x₁ a₁ B₁ J₁ → StepData σ J₁ y₁ b₁ C₁ J₀ → StepData σ J x₂ a₂ B₂ J₂ → StepData σ J₂ y₂ b₂ C₂ J₀ → B₁ * C₁ = B₂ * C₂ → c (M + 1) J x₁ B₁ * c M J₁ y₁ C₁ = c (M + 1) J x₂ B₂ * c M J₂ y₂ C₂) → ∃ α : ∀ M : ℕ, Matrix (Fin M) (Fin M) E → Γ, (∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E), IsHermND σ J → α M (Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin M) (Fin M) E) * J * (P : Matrix (Fin M) (Fin M) E)) = α M J) ∧ ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), 2 ≤ M → StepData σ J x a B J' → α (M + 1) J = c M J x B * α M J' := by
  intro F E _ _ _ _ _ σ hσ Γ _ c H1 H2
  have hs : ∀ x, σ (σ x) = x := GlobalTheory.HermLineZeros.conj_invol hσ
  have hF : ∀ {n : ℕ} {a : E} {J : Matrix (Fin n) (Fin n) E}, HN (σ : E →+* E) (blk a J) →
      ∃ a₀ : F, algebraMap F E a₀ = a := fun h => GlobalTheory.HermLineZeros.exists_of_fixed hσ _ ((hn_blk _ _ _).1 h).1
  have std : ∀ M J x a B J', 2 ≤ M → StepData σ J x a B J' →
      c M J x B = c M (blk (algebraMap F E a) J') (e0 E M) (incl E M) := by
    intro M J x a B J' hM h
    obtain ⟨hd, e⟩ := gram_consCol hs h
    have := H1 M J x a B J' (e0 E M) (incl E M) (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd) 1 hM h
      (by ext i; simp [e0, consCol]) (by ext i j; simp [mul_incl, consCol])
    rw [← this, ← e]
    rfl
  obtain ⟨A, hA1, hA2⟩ := cob_two (s := (σ : E →+* E)) hs
    (fun n a J => c n (blk a J) (e0 E n) (incl E n))
    (by
      rintro n a J K hn hJ ⟨Q, hQ, rfl⟩
      obtain ⟨a, rfl⟩ := hF hJ
      have hd : (blk 1 Q).det ≠ 0 := by simp [det_blk, hQ]
      have := H1 n _ _ a _ J (e0 E n) (incl E n) (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd)
        (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hQ) hn (stepData_std hJ)
        (by ext i; cases i using Fin.cases <;> simp [e0])
        (by
          ext i j
          rw [mul_incl]
          cases i using Fin.cases <;>
            simp [incl, Matrix.mul_apply, Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm])
      rw [← this]
      simp [cT_blk, blk_mul])
    (by
      rintro n a b a' b' J hn g g' ⟨p, q, r, u, e1, e2, e3, e4⟩
      have hT := two_gram J e1 e2 e3 e4
      have g1 := ((hn_blk _ _ _).1 g).2.2
      have g1' := ((hn_blk _ _ _).1 g').2.2
      obtain ⟨a, rfl⟩ := hF g
      obtain ⟨b, rfl⟩ := hF g1
      obtain ⟨a', rfl⟩ := hF g'
      obtain ⟨b', rfl⟩ := hF g1'
      have sd := stepData_of g g' hT
      have := H2 n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J hn (stepData_std g) (stepData_std g1) sd
        (stepData_std g1') (by
          rw [mul_incl, mul_incl, mul_incl]
          ext i j
          induction i using Fin.cases with
          | zero => simp [two, incl, (Fin.succ_ne_zero _).symm]
          | succ i =>
            cases i using Fin.cases <;>
              simp [two, incl, (Fin.succ_ne_zero _).symm, Matrix.one_apply, -Fin.succ_zero_eq_one,
                -Fin.succ_zero_eq_one'])
      rw [this, std _ _ _ _ _ _ (by omega) sd])
  refine ⟨A, fun M J P hJ => (hA1 M J _ hJ ⟨P, P.det_ne_zero, rfl⟩).symm, fun M J x a B J' hM h => ?_⟩
  obtain ⟨hd, e⟩ := gram_consCol hs h
  rw [hA2 M J _ J' hM h.1 ⟨_, hd, e⟩, std M J x a B J' hM h]

end Main

end GlobalTheory.GaugeAlg
