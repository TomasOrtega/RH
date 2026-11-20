import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DTauFacts

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def upPart (B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => if a < b then B a b else 0

def lowPart (B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => if b < a then B a b else 0

def diagPart (B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a => B a a

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, lowMinusUp, upPart, diagPart, Matrix.of_apply, Matrix.diagonal_apply, smul_eq_mul]`. Break down `lt_trichotomy a b with h | rfl | h` into its components or cases. Rewrite using `[if_neg (lt_asymm h), if_pos h, if_pos h, if_neg h.ne]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules. Rewrite using `[if_pos h, if_neg (lt_asymm h), if_neg h.ne']`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma decomp_up (B : Matrix (Fin n) (Fin n) ℂ) :
    B = lowMinusUp B + (2 : ℂ) • upPart B + diagPart B := by
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, lowMinusUp, upPart, diagPart, Matrix.of_apply,
    Matrix.diagonal_apply, smul_eq_mul]
  rcases lt_trichotomy a b with h | rfl | h
  · rw [if_neg (lt_asymm h), if_pos h, if_pos h, if_neg h.ne]
    ring
  · simp
  · rw [if_pos h, if_neg (lt_asymm h), if_neg h.ne']
    ring

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, lowMinusUp, lowPart, diagPart, Matrix.of_apply, Matrix.diagonal_apply, smul_eq_mul]`. Break down `lt_trichotomy a b with h | rfl | h` into its components or cases. Rewrite using `[if_neg (lt_asymm h), if_pos h, if_neg (lt_asymm h), if_neg h.ne]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules. Rewrite using `[if_pos h, if_pos h, if_neg h.ne']`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma decomp_low (B : Matrix (Fin n) (Fin n) ℂ) :
    B = -lowMinusUp B + (2 : ℂ) • lowPart B + diagPart B := by
  ext a b
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, lowMinusUp, lowPart, diagPart,
    Matrix.of_apply, Matrix.diagonal_apply, smul_eq_mul]
  rcases lt_trichotomy a b with h | rfl | h
  · rw [if_neg (lt_asymm h), if_pos h, if_neg (lt_asymm h), if_neg h.ne]
    ring
  · simp
  · rw [if_pos h, if_pos h, if_neg h.ne']
    ring

/- English proof (translation)
Rewrite using `[Matrix.smul_single, smul_eq_mul, mul_one]`.
-/
lemma single_eq_smul (a b : Fin n) (c : ℂ) :
    Matrix.single a b c = c • Matrix.single a b (1 : ℂ) := by
  rw [Matrix.smul_single, smul_eq_mul, mul_one]

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

/- English proof (translation)
Rewrite using `[Matrix.matrix_eq_sum_single (upPart B), map_sum, _root_.sum_apply]`. Use `Finset.sum_eq_zero (fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[map_sum, _root_.sum_apply]`. Use `Finset.sum_eq_zero (fun b _ => ?_)` and prove the remaining obligations. Rewrite using `[single_eq_smul, map_smul, ContinuousLinearMap.smul_apply]`.

Simplify using `only [upPart, Matrix.of_apply]`. Use `split_ifs with h`. Distinguish the cases in `he : ε a = ε b`. Rewrite using `[T.w_hw a b h he, smul_zero]`. Rewrite using `[hB a b he, zero_smul]`.

Rewrite using `[zero_smul]`.
-/
lemma dtau_upPart_w (T : KType ε Λ) {B : Matrix (Fin n) (Fin n) ℂ} (hB : IsBlock ε B) :
    T.dτ (upPart B) T.w = 0 := by
  rw [Matrix.matrix_eq_sum_single (upPart B), map_sum, _root_.sum_apply]
  refine Finset.sum_eq_zero (fun a _ => ?_)
  rw [map_sum, _root_.sum_apply]
  refine Finset.sum_eq_zero (fun b _ => ?_)
  rw [single_eq_smul, map_smul, ContinuousLinearMap.smul_apply]
  simp only [upPart, Matrix.of_apply]
  split_ifs with h
  · by_cases he : ε a = ε b
    · rw [T.w_hw a b h he, smul_zero]
    · rw [hB a b he, zero_smul]
  · rw [zero_smul]

/- English proof (translation)
Rewrite using `[Matrix.matrix_eq_sum_single (diagPart B), map_sum, _root_.sum_apply, Finset.sum_smul]`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[map_sum, _root_.sum_apply, Finset.sum_eq_single a]`. Rewrite using `[single_eq_smul, map_smul, ContinuousLinearMap.smul_apply, T.w_wt, smul_smul]`. Simplify using `only [diagPart, Matrix.diagonal_apply_eq]`.

Rewrite using `[mul_comm]`. Introduce `b _ hb`. Rewrite using `[single_eq_smul, map_smul, ContinuousLinearMap.smul_apply]`. Simplify using `only [diagPart, Matrix.diagonal_apply_ne _ (Ne.symm hb)]`. Rewrite using `[zero_smul]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ a) h`.
-/
lemma dtau_diagPart_w (T : KType ε Λ) (B : Matrix (Fin n) (Fin n) ℂ) :
    T.dτ (diagPart B) T.w = (∑ a, ((Λ a : ℝ) : ℂ) * B a a) • T.w := by
  rw [Matrix.matrix_eq_sum_single (diagPart B), map_sum, _root_.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [map_sum, _root_.sum_apply, Finset.sum_eq_single a]
  · rw [single_eq_smul, map_smul, ContinuousLinearMap.smul_apply, T.w_wt, smul_smul]
    simp only [diagPart, Matrix.diagonal_apply_eq]
    rw [mul_comm]
  · intro b _ hb
    rw [single_eq_smul, map_smul, ContinuousLinearMap.smul_apply]
    simp only [diagPart, Matrix.diagonal_apply_ne _ (Ne.symm hb)]
    rw [zero_smul]
  · intro h
    exact absurd (Finset.mem_univ a) h

/- English proof (translation)
Introduce `a b h`. Simplify using `only [lowPart, Matrix.of_apply]`. Use `split_ifs`. Conclude with `hB a b h`. Both sides reduce to the same expression.
-/
lemma isBlock_lowPart {B : Matrix (Fin n) (Fin n) ℂ} (hB : IsBlock ε B) : IsBlock ε (lowPart B) := by
  intro a b h
  simp only [lowPart, Matrix.of_apply]
  split_ifs
  · exact hB a b h
  · rfl

/- English proof (translation)
Introduce `a b h`. Establish `hab : a ≠ b`. Introduce and unpack `rfl`. Conclude with `h rfl`. Simplify using `only [diagPart]`.

Conclude with `Matrix.diagonal_apply_ne _ hab`.
-/
lemma isBlock_diagPart (B : Matrix (Fin n) (Fin n) ℂ) : IsBlock ε (diagPart B) := by
  intro a b h
  have hab : a ≠ b := by
    rintro rfl
    exact h rfl
  simp only [diagPart]
  exact Matrix.diagonal_apply_ne _ hab

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Matrix.conjTranspose_apply, lowPart, upPart, Matrix.of_apply]`. Use `split_ifs`. Establish `h` using `congrFun (congrFun hBh a) b`. Rewrite `h` using `[Matrix.conjTranspose_apply]`.

Conclude with `h`. Conclude with `star_zero _`.
-/
lemma lowPart_conjTranspose {B : Matrix (Fin n) (Fin n) ℂ} (hBh : Bᴴ = B) :
    (lowPart B)ᴴ = upPart B := by
  ext a b
  simp only [Matrix.conjTranspose_apply, lowPart, upPart, Matrix.of_apply]
  split_ifs
  · have h := congrFun (congrFun hBh a) b
    rw [Matrix.conjTranspose_apply] at h
    exact h
  · exact star_zero _

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[Matrix.conjTranspose_apply]`. Simplify using `only [diagPart]`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality.

Rewrite using `[Matrix.diagonal_apply_eq]`. Establish `h'` using `congrFun (congrFun hBh a) a`. Rewrite `h'` using `[Matrix.conjTranspose_apply]`. Conclude with `h'`. Rewrite using `[Matrix.diagonal_apply_ne _ (Ne.symm h), Matrix.diagonal_apply_ne _ h, star_zero]`.
-/
lemma diagPart_conjTranspose {B : Matrix (Fin n) (Fin n) ℂ} (hBh : Bᴴ = B) :
    (diagPart B)ᴴ = diagPart B := by
  ext a b
  rw [Matrix.conjTranspose_apply]
  simp only [diagPart]
  by_cases h : a = b
  · subst h
    rw [Matrix.diagonal_apply_eq]
    have h' := congrFun (congrFun hBh a) a
    rw [Matrix.conjTranspose_apply] at h'
    exact h'
  · rw [Matrix.diagonal_apply_ne _ (Ne.symm h), Matrix.diagonal_apply_ne _ h, star_zero]

/- English proof (translation)
Establish `hP : ∀ v, projW T v = inner ℂ T.w v • T.w` using `fun v => by`. Simplify using `only [projW, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]`. Establish `hBaa : ∀ a, (starRingEnd ℂ) (B a a) = B a a` using `fun a => by`. Establish `h` using `congrFun (congrFun hBh a) a`. Rewrite `h` using `[Matrix.conjTranspose_apply]`.

Conclude with `h`. Establish `hc : (starRingEnd ℂ) (∑ a, ((Λ a : ℝ) : ℂ) * B a a) = ∑ a, ((Λ a : ℝ) : ℂ) * B a a`. Simplify using `only [map_sum, map_mul, Complex.conj_ofReal, hBaa]`. Establish `h1 : T.dτ (upPart B) * projW T = 0`. Use extensionality with `v`.

Rewrite using `[ContinuousLinearMap.mul_apply, hP, map_smul, dtau_upPart_w T hB, smul_zero, ContinuousLinearMap.zero_apply]`. Establish `h2 : T.dτ (diagPart B) * projW T = (∑ a, ((Λ a : ℝ) : ℂ) * B a a) • projW T`. Use extensionality with `v`. Rewrite using `[ContinuousLinearMap.mul_apply, hP, map_smul, dtau_diagPart_w, ContinuousLinearMap.smul_apply, hP, smul_comm]`. Establish `h3 : projW T * T.dτ (lowPart B) = 0`.

Use extensionality with `v`. Rewrite using `[ContinuousLinearMap.mul_apply, hP, ← ContinuousLinearMap.adjoint_inner_left, dtau_adj T (isBlock_lowPart hB), lowPart_conjTranspose hBh, dtau_upPart_w T hB, inner_zero_left, zero_smul, ContinuousLinearMap.zero_apply]`. Establish `h4 : projW T * T.dτ (diagPart B) = (∑ a, ((Λ a : ℝ) : ℂ) * B a a) • projW T`. Use extensionality with `v`. Rewrite using `[ContinuousLinearMap.mul_apply, hP, ← ContinuousLinearMap.adjoint_inner_left, dtau_adj T (isBlock_diagPart B), diagPart_conjTranspose hBh, dtau_diagPart_w, inner_smul_left, hc, ContinuousLinearMap.smul_apply, hP, mul_smul]`.

Establish `eB1 : T.dτ B = T.dτ (lowMinusUp B) + (2 : ℂ) • T.dτ (upPart B) + T.dτ (diagPart B)` using `by conv_lhs => rw [decomp_up B]`. Rewrite using `[map_add, map_add, map_smul]`. Establish `eB2 : T.dτ B = -T.dτ (lowMinusUp B) + (2 : ℂ) • T.dτ (lowPart B) + T.dτ (diagPart B)` using `by conv_lhs => rw [decomp_low B]`. Rewrite using `[map_add, map_add, map_smul, map_neg]`. Establish `hL : T.dτ B * projW T = T.dτ (lowMinusUp B) * projW T + (∑ a, ((Λ a : ℝ) : ℂ) * B a a) • projW T`.

Rewrite using `[eB1, add_mul, add_mul, smul_mul_assoc, h1, smul_zero, add_zero, h2]`. Establish `hR : projW T * T.dτ B = -(projW T * T.dτ (lowMinusUp B)) + (∑ a, ((Λ a : ℝ) : ℂ) * B a a) • projW T`. Rewrite using `[eB2, mul_add, mul_add, mul_smul_comm, h3, smul_zero, add_zero, h4, mul_neg]`. Rewrite using `[hL, hR, two_mul, add_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem tau_part {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {B : Matrix (Fin n) (Fin n) ℂ}
    (hB : IsBlock ε B) (hBh : Bᴴ = B) :
    T.dτ B * projW T + projW T * T.dτ B =
      (T.dτ (lowMinusUp B) * projW T - projW T * T.dτ (lowMinusUp B)) +
        (2 * ∑ a, ((Λ a : ℝ) : ℂ) * B a a) • projW T := by
  have hP : ∀ v, projW T v = inner ℂ T.w v • T.w := fun v => by
    simp only [projW, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  have hBaa : ∀ a, (starRingEnd ℂ) (B a a) = B a a := fun a => by
    have h := congrFun (congrFun hBh a) a
    rw [Matrix.conjTranspose_apply] at h
    exact h
  have hc : (starRingEnd ℂ) (∑ a, ((Λ a : ℝ) : ℂ) * B a a) = ∑ a, ((Λ a : ℝ) : ℂ) * B a a := by
    simp only [map_sum, map_mul, Complex.conj_ofReal, hBaa]
  have h1 : T.dτ (upPart B) * projW T = 0 := by
    ext v
    rw [ContinuousLinearMap.mul_apply, hP, map_smul, dtau_upPart_w T hB, smul_zero,
      ContinuousLinearMap.zero_apply]
  have h2 : T.dτ (diagPart B) * projW T = (∑ a, ((Λ a : ℝ) : ℂ) * B a a) • projW T := by
    ext v
    rw [ContinuousLinearMap.mul_apply, hP, map_smul, dtau_diagPart_w, ContinuousLinearMap.smul_apply,
      hP, smul_comm]
  have h3 : projW T * T.dτ (lowPart B) = 0 := by
    ext v
    rw [ContinuousLinearMap.mul_apply, hP, ← ContinuousLinearMap.adjoint_inner_left,
      dtau_adj T (isBlock_lowPart hB), lowPart_conjTranspose hBh, dtau_upPart_w T hB, inner_zero_left,
      zero_smul, ContinuousLinearMap.zero_apply]
  have h4 : projW T * T.dτ (diagPart B) = (∑ a, ((Λ a : ℝ) : ℂ) * B a a) • projW T := by
    ext v
    rw [ContinuousLinearMap.mul_apply, hP, ← ContinuousLinearMap.adjoint_inner_left,
      dtau_adj T (isBlock_diagPart B), diagPart_conjTranspose hBh, dtau_diagPart_w, inner_smul_left, hc,
      ContinuousLinearMap.smul_apply, hP, mul_smul]
  have eB1 : T.dτ B = T.dτ (lowMinusUp B) + (2 : ℂ) • T.dτ (upPart B) + T.dτ (diagPart B) := by
    conv_lhs => rw [decomp_up B]
    rw [map_add, map_add, map_smul]
  have eB2 : T.dτ B = -T.dτ (lowMinusUp B) + (2 : ℂ) • T.dτ (lowPart B) + T.dτ (diagPart B) := by
    conv_lhs => rw [decomp_low B]
    rw [map_add, map_add, map_smul, map_neg]
  have hL : T.dτ B * projW T =
      T.dτ (lowMinusUp B) * projW T + (∑ a, ((Λ a : ℝ) : ℂ) * B a a) • projW T := by
    rw [eB1, add_mul, add_mul, smul_mul_assoc, h1, smul_zero, add_zero, h2]
  have hR : projW T * T.dτ B =
      -(projW T * T.dτ (lowMinusUp B)) + (∑ a, ((Λ a : ℝ) : ℂ) * B a a) • projW T := by
    rw [eB2, mul_add, mul_add, mul_smul_comm, h3, smul_zero, add_zero, h4, mul_neg]
  rw [hL, hR, two_mul, add_smul]
  abel

end ReciprocityTheory.ChartRestriction.DS.S7
