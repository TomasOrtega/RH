import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandSeriesShiftIdentityStatement
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.ValPhi

open PowerSeries

section
variable {A : Type} [Ring A] (N : A) (τ : ℕ → A)

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `j h`. Consider the cases of `j with`.

Consider the case `zero => omega`. Consider the case `succ j => simp [bco]`. Consider the case `succ m ih`. Introduce `j h`. Consider the cases of `j with`.

Consider the case `zero => omega`. Consider the case `succ j => rw [bco, ih j (by omega), ih (j + 1) (by omega)]; simp`.
-/
theorem bco_of_lt : ∀ (m j : ℕ), m < j → bco N τ m j = 0 := by
  intro m
  induction m with
  | zero =>
    intro j h
    cases j with
    | zero => omega
    | succ j => simp [bco]
  | succ m ih =>
    intro j h
    cases j with
    | zero => omega
    | succ j => rw [bco, ih j (by omega), ih (j + 1) (by omega)]; simp

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [bco]`. Consider the case `succ m ih => rw [bco, ih, bco_of_lt N τ m (m + 1) (by omega)]; simp`.
-/
theorem bco_self (m : ℕ) : bco N τ m m = 1 := by
  induction m with
  | zero => simp [bco]
  | succ m ih => rw [bco, ih, bco_of_lt N τ m (m + 1) (by omega)]; simp

/- English proof (translation)
Proceed by induction on `m using Nat.strong_induction_on with`. Consider the case `_ m ih`. Establish `e : ∑ j ∈ range m, bco N τ m j * phiSeq N τ j = ∑ j ∈ range m, bco N τ m j * p j` using `sum_congr rfl fun j hj => by rw [ih j (mem_range.1 hj)]`. Rewrite using `[phiSeq, Fin.sum_univ_eq_sum_range (fun j => bco N τ m j * phiSeq N τ j) m, e, ← h m, sum_range_succ, bco_self, one_mul]`. Normalize the expressions using the abelian group laws.
-/
theorem eq_phiSeq (p : ℕ → A) (h : ∀ m, ∑ j ∈ range (m + 1), bco N τ m j * p j = τ m) (m : ℕ) :
    p m = phiSeq N τ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have e : ∑ j ∈ range m, bco N τ m j * phiSeq N τ j = ∑ j ∈ range m, bco N τ m j * p j :=
      sum_congr rfl fun j hj => by rw [ih j (mem_range.1 hj)]
    rw [phiSeq, Fin.sum_univ_eq_sum_range (fun j => bco N τ m j * phiSeq N τ j) m, e, ← h m,
      sum_range_succ, bco_self, one_mul]
    abel
end

section
variable (N : ℂ) (τ : ℕ → ℂ)

noncomputable def bser (j : ℕ) : PowerSeries ℂ := PowerSeries.mk (fun m => bco N τ m j)

/- English proof (translation)
Simplify using `[bser]`.
-/
theorem coeff_bser (j m : ℕ) : coeff m (bser N τ j) = bco N τ m j := by simp [bser]

/- English proof (translation)
Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_bser]`.
-/
theorem constantCoeff_bser (j : ℕ) : constantCoeff (bser N τ j) = bco N τ 0 j := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_bser]

/- English proof (translation)
Establish `e : ∀ f : PowerSeries ℂ, (1 - C N * X) * f = f - C N * (X * f)` using `fun f => by ring`. Rewrite using `[e]`. Use extensionality with `k`. Consider the cases of `k with`. Consider the case `zero => simp [constantCoeff_bser, bco]`.

Consider the case `succ k`. Simplify using `[coeff_bser, bco, coeff_succ_X_mul, coeff_one]`.
-/
theorem bser_zero : (1 - C N * X) * bser N τ 0 = 1 - X * PowerSeries.mk τ := by
  have e : ∀ f : PowerSeries ℂ, (1 - C N * X) * f = f - C N * (X * f) := fun f => by ring
  rw [e]
  ext k
  cases k with
  | zero => simp [constantCoeff_bser, bco]
  | succ k =>
    simp [coeff_bser, bco, coeff_succ_X_mul, coeff_one]

/- English proof (translation)
Establish `e : ∀ f : PowerSeries ℂ, (1 - C N * X) * f = f - C N * (X * f)` using `fun f => by ring`. Rewrite using `[e]`. Use extensionality with `k`. Consider the cases of `k with`. Consider the case `zero => simp [constantCoeff_bser, bco]`.

Consider the case `succ k`. Simplify using `[coeff_bser, bco, coeff_succ_X_mul]`.
-/
theorem bser_succ (j : ℕ) : (1 - C N * X) * bser N τ (j + 1) = X * bser N τ j := by
  have e : ∀ f : PowerSeries ℂ, (1 - C N * X) * f = f - C N * (X * f) := fun f => by ring
  rw [e]
  ext k
  cases k with
  | zero => simp [constantCoeff_bser, bco]
  | succ k =>
    simp [coeff_bser, bco, coeff_succ_X_mul]

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero`. Use `bser_zero N τ` as an intermediate fact. Rewrite using `[← this]`. Take the linear combination `(-(bser N τ 0)) * hw`.

Consider the case `succ j ih`. Use `bser_succ N τ j` as an intermediate fact. Rewrite `this` using `[ih]`. Take the linear combination `(-(bser N τ (j + 1))) * hw + w * this`.
-/
theorem bser_eq {w : PowerSeries ℂ} (hw : (1 - C N * X) * w = 1) (j : ℕ) :
    bser N τ j = (1 - X * PowerSeries.mk τ) * w ^ (j + 1) * X ^ j := by
  induction j with
  | zero =>
    have := bser_zero N τ
    rw [← this]
    linear_combination (-(bser N τ 0)) * hw
  | succ j ih =>
    have := bser_succ N τ j
    rw [ih] at this
    linear_combination (-(bser N τ (j + 1))) * hw + w * this

end

/- English proof (translation)
Use extensionality with `k`. Simplify using `only [map_add, map_sum, coeff_mk, coeff_X_pow_mul', LinearMap.map_smul, coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Distinguish the cases in `hk : m + 1 ≤ k`. Rewrite using `[if_pos hk, Nat.sub_add_cancel hk, sum_ite_eq]`. Simplify using `[mem_range]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg hk, sum_ite_eq, if_pos (mem_range.2 (by omega))]`. Simplify using the standard rewrite rules.
-/
theorem mk_decomp (g : ℕ → ℂ) (m : ℕ) :
    PowerSeries.mk g = ∑ j ∈ range (m + 1), g j • (X : PowerSeries ℂ) ^ j
      + X ^ (m + 1) * PowerSeries.mk (fun i => g (i + (m + 1))) := by
  ext k
  simp only [map_add, map_sum, coeff_mk, coeff_X_pow_mul', LinearMap.map_smul, coeff_X_pow,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hk : m + 1 ≤ k
  · rw [if_pos hk, Nat.sub_add_cancel hk, sum_ite_eq]
    simp [mem_range]
    omega
  · rw [if_neg hk, sum_ite_eq, if_pos (mem_range.2 (by omega))]
    simp

/- English proof (translation)
Set `θ : PowerSeries ℂ →ₐ[ℂ] PowerSeries ℂ` to `substAlgHom ha`. Establish `hθ : ∀ f, subst (-(X * w)) f = θ f` using `fun f => by simp [θ, coe_substAlgHom]`. Establish `hX : θ X = -(X * w)` using `by rw [← hθ]; exact subst_X ha`. Use `set H := PowerSeries.mk (fun i => g (i + (m + 1))) with hH`. Use `set Q := 1 - X * PowerSeries.mk τ with hQ`.

Establish `hG : θ (PowerSeries.mk g) = ∑ j ∈ range (m + 1), g j • (-(X * w)) ^ j + (-(X * w)) ^ (m + 1) * θ H` using `by conv_lhs => rw [mk_decomp g m]`. Simplify using `only [map_add, map_sum, map_smul, map_mul, map_pow, hX, hH]`. Rewrite `h` using `[hθ, map_sub, map_one, map_mul, hX, hG]`. Establish `hterm : ∀ j, Q * (X * w) * (g j • (-(X * w)) ^ j) = (g j * (-1) ^ j) • (X * bser N τ j)`. Introduce `j`.

Rewrite using `[bser_eq N τ hw j, neg_pow]`. Simplify using `only [smul_eq_C_mul, map_mul, map_pow, map_neg, map_one]`. Expand and normalize the polynomial expressions, which then agree. Establish `hfin : Q + ∑ j ∈ range (m + 1), (g j * (-1) ^ j) • (X * bser N τ j) + X ^ (m + 2) * (Q * w * (-w) ^ (m + 1) * θ H) = 1`. Rewrite using `[← h, ← sum_congr rfl fun j _ => hterm j, ← mul_sum, neg_mul_eq_mul_neg X w, mul_pow]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hc` using `congrArg (coeff (m + 1)) hfin`. Simplify using `only [map_add, map_sum, LinearMap.map_smul, coeff_succ_X_mul, coeff_bser, coeff_X_pow_mul', smul_eq_mul, hQ, map_sub, coeff_mk, coeff_one] at hc`. Simplify using `at hc`. Establish `e : ∑ j ∈ range (m + 1), bco N τ m j * ((-1) ^ j * g j) = ∑ x ∈ range (m + 1), g x * (-1) ^ x * bco N τ m x` using `sum_congr rfl fun j _ => by ring`.

Rewrite using `[e]`. Take the linear combination `hc`.
-/
theorem sum_of_subst (N : ℂ) (τ g : ℕ → ℂ) {w : PowerSeries ℂ} (hw : (1 - C N * X) * w = 1)
    (ha : HasSubst (-(X * w)))
    (h : (1 - X * PowerSeries.mk τ) * subst (-(X * w)) (1 - X * PowerSeries.mk g) = 1) (m : ℕ) :
    ∑ j ∈ range (m + 1), bco N τ m j * ((-1) ^ j * g j) = τ m := by
  let θ : PowerSeries ℂ →ₐ[ℂ] PowerSeries ℂ := substAlgHom ha
  have hθ : ∀ f, subst (-(X * w)) f = θ f := fun f => by simp [θ, coe_substAlgHom]
  have hX : θ X = -(X * w) := by rw [← hθ]; exact subst_X ha
  set H := PowerSeries.mk (fun i => g (i + (m + 1))) with hH
  set Q := 1 - X * PowerSeries.mk τ with hQ
  have hG : θ (PowerSeries.mk g) = ∑ j ∈ range (m + 1), g j • (-(X * w)) ^ j
      + (-(X * w)) ^ (m + 1) * θ H := by
    conv_lhs => rw [mk_decomp g m]
    simp only [map_add, map_sum, map_smul, map_mul, map_pow, hX, hH]
  rw [hθ, map_sub, map_one, map_mul, hX, hG] at h
  have hterm : ∀ j, Q * (X * w) * (g j • (-(X * w)) ^ j)
      = (g j * (-1) ^ j) • (X * bser N τ j) := by
    intro j
    rw [bser_eq N τ hw j, neg_pow]
    simp only [smul_eq_C_mul, map_mul, map_pow, map_neg, map_one]
    ring
  have hfin : Q + ∑ j ∈ range (m + 1), (g j * (-1) ^ j) • (X * bser N τ j)
      + X ^ (m + 2) * (Q * w * (-w) ^ (m + 1) * θ H) = 1 := by
    rw [← h, ← sum_congr rfl fun j _ => hterm j, ← mul_sum, neg_mul_eq_mul_neg X w, mul_pow]
    ring
  have hc := congrArg (coeff (m + 1)) hfin
  simp only [map_add, map_sum, LinearMap.map_smul, coeff_succ_X_mul, coeff_bser, coeff_X_pow_mul',
    smul_eq_mul, hQ, map_sub, coeff_mk, coeff_one] at hc
  simp at hc
  have e : ∑ j ∈ range (m + 1), bco N τ m j * ((-1) ^ j * g j)
      = ∑ x ∈ range (m + 1), g x * (-1) ^ x * bco N τ m x :=
    sum_congr rfl fun j _ => by ring
  rw [e]
  linear_combination hc

/- English proof (translation)
Set `θ : PowerSeries ℂ →ₐ[ℂ] PowerSeries ℂ` to `substAlgHom ha`. Establish `hθ : ∀ f, subst (-(X * w)) f = θ f` using `fun f => by simp [θ, coe_substAlgHom]`. Establish `hX : θ X = -(X * w)` using `by rw [← hθ]; exact subst_X ha`. Establish `hC : ∀ c : ℂ, θ (C c) = C c` using `fun c => θ.commutes c`. Establish `e1 : ∀ i, 1 - C (-cc i + ((n : ℂ) - 1) / 2) * -(X * w) = w * (1 - C (cc i + ((n : ℂ) - 1) / 2 + 1) * X)`.

Introduce `i`. Establish `hn : C (n : ℂ) = C (-cc i + ((n : ℂ) - 1) / 2) + C (cc i + ((n : ℂ) - 1) / 2 + 1)`. Rewrite using `[← map_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Take the linear combination `(-1 : PowerSeries ℂ) * hw - X * w * hn`. Establish `e2 : ∀ i, 1 - C (-cc i + ((n : ℂ) - 1) / 2 + 1) * -(X * w) = w * (1 - C (cc i + ((n : ℂ) - 1) / 2) * X)`. Introduce `i`. Establish `hn : C (n : ℂ) = C (-cc i + ((n : ℂ) - 1) / 2 + 1) + C (cc i + ((n : ℂ) - 1) / 2)`. Rewrite using `[← map_add]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Take the linear combination `(-1 : PowerSeries ℂ) * hw - X * w * hn`. Establish `h1` using `GlobalTheory.T.gelfand_series_shift_identity n cc`. Establish `h2` using `congrArg θ (GlobalTheory.T.gelfand_series_shift_identity n (fun a => - cc a))`.

Simplify using `only [map_mul, map_prod, map_sub, map_one, hC, hX, e1, e2, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin] at h2`. Use `set D := ∏ a, (1 - C (cc a + ((n : ℂ) - 1) / 2 + 1) * (X : PowerSeries ℂ)) with hD`. Use `set E := ∏ a, (1 - C (cc a + ((n : ℂ) - 1) / 2) * (X : PowerSeries ℂ)) with hE`. Establish `hw0 : w ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at hw`. Establish `hD0 : D ≠ 0`. Use `prod_ne_zero_iff.2 fun i _ h0 => ?_` and prove the remaining obligations. Use `congrArg constantCoeff h0` as an intermediate fact. Simplify using `at this`.

Rewrite using `[hθ, map_sub, map_one, map_mul, hX]`. Use `mul_right_cancel₀ (mul_ne_zero (pow_ne_zero n hw0) hD0) ?_` and prove the remaining obligations. Take the linear combination `(1 - X * gser cc) * h2 + w ^ n * h1`.
-/
theorem mul_subst_eq_one (n : ℕ) (cc : Fin n → ℂ) {w : PowerSeries ℂ}
    (hw : (1 - C (n : ℂ) * X) * w = 1) (ha : HasSubst (-(X * w))) :
    (1 - X * gser cc) * subst (-(X * w)) (1 - X * gser (fun a => - cc a)) = 1 := by
  let θ : PowerSeries ℂ →ₐ[ℂ] PowerSeries ℂ := substAlgHom ha
  have hθ : ∀ f, subst (-(X * w)) f = θ f := fun f => by simp [θ, coe_substAlgHom]
  have hX : θ X = -(X * w) := by rw [← hθ]; exact subst_X ha
  have hC : ∀ c : ℂ, θ (C c) = C c := fun c => θ.commutes c
  have e1 : ∀ i, 1 - C (-cc i + ((n : ℂ) - 1) / 2) * -(X * w)
      = w * (1 - C (cc i + ((n : ℂ) - 1) / 2 + 1) * X) := by
    intro i
    have hn : C (n : ℂ) = C (-cc i + ((n : ℂ) - 1) / 2) + C (cc i + ((n : ℂ) - 1) / 2 + 1) := by
      rw [← map_add]; congr 1; ring
    linear_combination (-1 : PowerSeries ℂ) * hw - X * w * hn
  have e2 : ∀ i, 1 - C (-cc i + ((n : ℂ) - 1) / 2 + 1) * -(X * w)
      = w * (1 - C (cc i + ((n : ℂ) - 1) / 2) * X) := by
    intro i
    have hn : C (n : ℂ) = C (-cc i + ((n : ℂ) - 1) / 2 + 1) + C (cc i + ((n : ℂ) - 1) / 2) := by
      rw [← map_add]; congr 1; ring
    linear_combination (-1 : PowerSeries ℂ) * hw - X * w * hn
  have h1 := GlobalTheory.T.gelfand_series_shift_identity n cc
  have h2 := congrArg θ (GlobalTheory.T.gelfand_series_shift_identity n (fun a => - cc a))
  simp only [map_mul, map_prod, map_sub, map_one, hC, hX, e1, e2, prod_mul_distrib, prod_const,
    card_univ, Fintype.card_fin] at h2
  set D := ∏ a, (1 - C (cc a + ((n : ℂ) - 1) / 2 + 1) * (X : PowerSeries ℂ)) with hD
  set E := ∏ a, (1 - C (cc a + ((n : ℂ) - 1) / 2) * (X : PowerSeries ℂ)) with hE
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  have hD0 : D ≠ 0 := by
    refine prod_ne_zero_iff.2 fun i _ h0 => ?_
    have := congrArg constantCoeff h0
    simp at this
  rw [hθ, map_sub, map_one, map_mul, hX]
  refine mul_right_cancel₀ (mul_ne_zero (pow_ne_zero n hw0) hD0) ?_
  linear_combination (1 - X * gser cc) * h2 + w ^ n * h1

/- English proof (translation)
Introduce `n cc m`. Establish `hu : constantCoeff (1 - C (n : ℂ) * X : PowerSeries ℂ) ≠ 0` using `by simp`. Establish `hw` using `PowerSeries.mul_inv_cancel _ hu`. Establish `ha : HasSubst (-(X * (1 - C (n : ℂ) * X : PowerSeries ℂ)⁻¹))` using `HasSubst.of_constantCoeff_zero' (by simp)`. Conclude with `eq_phiSeq (n : ℂ) (GlobalTheory.Dec.gelfVal cc) (fun m => (-1 : ℂ) ^ m * GlobalTheory.Dec.gelfVal (fun a => - cc a) m) (sum_of_subst (n : ℂ) _ _ hw ha (mul_subst_eq_one n cc hw ha)) m`.
-/
theorem gelfVal_neg_eq_phiSeq : ∀ (n : ℕ) (cc : Fin n → ℂ) (m : ℕ),
    (-1 : ℂ) ^ m * GlobalTheory.Dec.gelfVal (fun a => - cc a) m = phiSeq (n : ℂ) (GlobalTheory.Dec.gelfVal cc) m := by
  intro n cc m
  have hu : constantCoeff (1 - C (n : ℂ) * X : PowerSeries ℂ) ≠ 0 := by simp
  have hw := PowerSeries.mul_inv_cancel _ hu
  have ha : HasSubst (-(X * (1 - C (n : ℂ) * X : PowerSeries ℂ)⁻¹)) :=
    HasSubst.of_constantCoeff_zero' (by simp)
  exact eq_phiSeq (n : ℂ) (GlobalTheory.Dec.gelfVal cc)
    (fun m => (-1 : ℂ) ^ m * GlobalTheory.Dec.gelfVal (fun a => - cc a) m)
    (sum_of_subst (n : ℂ) _ _ hw ha (mul_subst_eq_one n cc hw ha)) m

end GlobalTheory.CompanionTheory.WaveMult.ValPhi
