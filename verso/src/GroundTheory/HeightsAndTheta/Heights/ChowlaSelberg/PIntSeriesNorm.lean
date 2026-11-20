import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.IntSeries
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.IntSeriesRing
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.IntSeriesNorm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open PowerSeries
open scoped Real

noncomputable section

namespace IntSeriesNorm

/- English proof (translation)
Rewrite using `[intSeriesEval, tsum_eq_single 0]`. Simplify using the standard rewrite rules. Introduce `n hn`. Simplify using `[coeff_one, hn]`.
-/
theorem intSeriesEval_one (z : ℂ) : intSeriesEval 1 z = 1 := by
  rw [intSeriesEval, tsum_eq_single 0]
  · simp
  · intro n hn; simp [coeff_one, hn]

/- English proof (translation)
Rewrite using `[intSeriesEval, tsum_eq_single 1]`. Simplify using the standard rewrite rules. Introduce `n hn`. Simplify using `[coeff_X, hn]`.
-/
theorem intSeriesEval_X (z : ℂ) : intSeriesEval X z = z := by
  rw [intSeriesEval, tsum_eq_single 1]
  · simp
  · intro n hn; simp [coeff_X, hn]

/- English proof (translation)
Apply `summable_of_ne_finset_zero (s := {1})` to reduce the goal to its premises. Introduce `n hn`. Simplify using `only [Finset.mem_singleton] at hn`. Simplify using `[coeff_X, hn]`.
-/
theorem intSeriesConv_X (r : ℝ) : IntSeriesConv X r := by
  apply summable_of_ne_finset_zero (s := {1})
  intro n hn
  simp only [Finset.mem_singleton] at hn
  simp [coeff_X, hn]

def residuePart (F : PowerSeries ℤ) (p i : ℕ) : PowerSeries ℤ :=
  mk fun m ↦ coeff (m * p + i) F

/- English proof (translation)
Unfold `IntSeriesConv at *`. Establish `hinj : Function.Injective fun m : ℕ ↦ m * p + i` using `fun a b h ↦ Nat.eq_of_mul_eq_mul_right hp (Nat.add_right_cancel h)`. Establish `h1` using `(hF.comp_injective hinj).mul_left ((r ^ i)⁻¹)`. Use `h1.congr fun m ↦ ?_` and prove the remaining obligations. Establish `hri : r ^ i ≠ 0` using `pow_ne_zero _ hr.ne'`.

Simplify using `only [Function.comp_apply, residuePart, coeff_mk]`. Rewrite using `[pow_add, pow_mul']`. Clear the denominators using the available nonvanishing facts.
-/
theorem residuePart_conv {F : PowerSeries ℤ} {r : ℝ} (hr : 0 < r) (hF : IntSeriesConv F r)
    {p : ℕ} (hp : 0 < p) (i : ℕ) : IntSeriesConv (residuePart F p i) (r ^ p) := by
  unfold IntSeriesConv at *
  have hinj : Function.Injective fun m : ℕ ↦ m * p + i := fun a b h ↦
    Nat.eq_of_mul_eq_mul_right hp (Nat.add_right_cancel h)
  have h1 := (hF.comp_injective hinj).mul_left ((r ^ i)⁻¹)
  refine h1.congr fun m ↦ ?_
  have hri : r ^ i ≠ 0 := pow_ne_zero _ hr.ne'
  simp only [Function.comp_apply, residuePart, coeff_mk]
  rw [pow_add, pow_mul']
  field_simp

/- English proof (translation)
Establish `: NeZero p` using `⟨hp.ne'⟩`. Establish `hq : ‖s ^ p‖ ≤ r ^ p` using `by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hs p`. Establish `hsum` using `(hR r hr.le).2.2.1 F hF s hs`. Establish `hparts : ∀ i : Fin p, HasSum (fun m : ℕ ↦ ((coeff (m * p + i) F : ℤ) : ℂ) * s ^ (m * p + i)) (s ^ (i : ℕ) * intSeriesEval (residuePart F p i) (s ^ p))`. Introduce `i`.

Establish `h` using `((hR (r ^ p) (pow_nonneg hr.le p)).2.2.1 _ (residuePart_conv hr hF hp i) _ hq).mul_left (s ^ (i : ℕ))`. Establish `hf : (fun m : ℕ ↦ ((coeff (m * p + i) F : ℤ) : ℂ) * s ^ (m * p + i)) = fun m ↦ s ^ (i : ℕ) * (((coeff m (residuePart F p i) : ℤ) : ℂ) * (s ^ p) ^ m)`. Use function extensionality and compare the values at `m`. Simplify using `only [residuePart, coeff_mk]`. Rewrite using `[pow_add, pow_mul']`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hf]`. Conclude with `h`. Set `e : ℕ ≃ Fin p × ℕ` to `(Nat.divModEquiv p).trans (Equiv.prodComm _ _)`. Establish `hfe : ∀ x : Fin p × ℕ, e.symm x = x.2 * p + x.1` using `fun x ↦ rfl`.

Establish `htot` using `(e.symm.hasSum_iff).mpr hsum`. Simplify using `only [Function.comp_def, hfe] at htot`. Conclude with `(htot.prod_fiberwise hparts).unique (hasSum_fintype _)`.
-/
theorem intSeriesEval_split (hR : IntSeriesRing.Statement) {F : PowerSeries ℤ} {r : ℝ}
    (hr : 0 < r) (hF : IntSeriesConv F r) {p : ℕ} (hp : 0 < p) (s : ℂ) (hs : ‖s‖ ≤ r) :
    intSeriesEval F s = ∑ i : Fin p, s ^ (i : ℕ) * intSeriesEval (residuePart F p i) (s ^ p) := by
  have : NeZero p := ⟨hp.ne'⟩
  have hq : ‖s ^ p‖ ≤ r ^ p := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hs p
  have hsum := (hR r hr.le).2.2.1 F hF s hs
  have hparts : ∀ i : Fin p, HasSum (fun m : ℕ ↦ ((coeff (m * p + i) F : ℤ) : ℂ) * s ^ (m * p + i))
      (s ^ (i : ℕ) * intSeriesEval (residuePart F p i) (s ^ p)) := by
    intro i
    have h := ((hR (r ^ p) (pow_nonneg hr.le p)).2.2.1 _ (residuePart_conv hr hF hp i) _ hq).mul_left
      (s ^ (i : ℕ))
    have hf : (fun m : ℕ ↦ ((coeff (m * p + i) F : ℤ) : ℂ) * s ^ (m * p + i)) =
        fun m ↦ s ^ (i : ℕ) * (((coeff m (residuePart F p i) : ℤ) : ℂ) * (s ^ p) ^ m) := by
      funext m
      simp only [residuePart, coeff_mk]
      rw [pow_add, pow_mul']
      ring
    rw [hf]
    exact h
  let e : ℕ ≃ Fin p × ℕ := (Nat.divModEquiv p).trans (Equiv.prodComm _ _)
  have hfe : ∀ x : Fin p × ℕ, e.symm x = x.2 * p + x.1 := fun x ↦ rfl
  have htot := (e.symm.hasSum_iff).mpr hsum
  simp only [Function.comp_def, hfe] at htot
  exact (htot.prod_fiberwise hparts).unique (hasSum_fintype _)

def evalHom (S : Subring (PowerSeries ℤ)) (z : ℂ)
    (hmul : ∀ F G : S, intSeriesEval ((F : PowerSeries ℤ) * G) z =
      intSeriesEval F z * intSeriesEval G z)
    (hhas : ∀ F : S, HasSum (fun n ↦ ((coeff n (F : PowerSeries ℤ) : ℤ) : ℂ) * z ^ n)
      (intSeriesEval F z)) : S →+* ℂ where
  toFun f := intSeriesEval f z
  map_one' := by simp only [Subring.coe_one, intSeriesEval_one]
  map_mul' F G := by simp only [Subring.coe_mul]; exact hmul F G
  map_zero' := by simp [intSeriesEval]
  map_add' F G := by
    have h := hhas (F + G)
    simp only [Subring.coe_add, map_add, Int.cast_add, add_mul] at h
    exact h.unique ((hhas F).add (hhas G))

def normMatrix (F : PowerSeries ℤ) (p : ℕ) [NeZero p] : Matrix (Fin p) (Fin p) (PowerSeries ℤ) :=
  Matrix.of fun i k ↦ (if i ≤ k then 1 else X) * residuePart F p ((k - i : Fin p) : ℕ)

/- English proof (translation)
Establish `hp : 0 < p` using `Nat.pos_of_ne_zero (NeZero.ne p)`. Take `⟨-, hmul, -, -, -⟩` from `hR (r ^ p) (pow_nonneg hr.le p)`. Establish `hq : ‖s ^ p‖ ≤ r ^ p` using `by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hs p`. Apply the tactic sequence `have hentry : ∀ k : Fin p, intSeriesEval (normMatrix F p i k) (s ^ p) = (if i ≤ k then 1 else s ^ p) * intSeriesEval (residuePart F p ((k - i : Fin p) : ℕ)) (s ^ p) := by`. Introduce `k`.

Simplify using `only [normMatrix, Matrix.of_apply]`. Use `split_ifs`. Rewrite using `[one_mul, one_mul]`. Rewrite using `[hmul _ _ (intSeriesConv_X _) (residuePart_conv hr hF hp _) _ hq, intSeriesEval_X]`. Rewrite using `[intSeriesEval_split hR hr hF hp s hs, Finset.mul_sum]`.

Use `symm`. Apply `Fintype.sum_equiv (Equiv.addLeft i)` to reduce the goal to its premises. Introduce `k`. Simplify using `only [Equiv.coe_addLeft]`. Rewrite using `[hentry, add_sub_cancel_left]`.

Establish `hi` using `i.is_lt`. Establish `hk` using `k.is_lt`. Distinguish the cases in `h : (i : ℕ) + k < p`. Establish `hv : ((i + k : Fin p) : ℕ) = i + k` using `by rw [Fin.val_add, Nat.mod_eq_of_lt h]`. Establish `hle : i ≤ i + k` using `by rw [Fin.le_iff_val_le_val, hv]; omega`.

Rewrite using `[if_pos hle, hv, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Establish `hv : ((i + k : Fin p) : ℕ) = i + k - p`. Rewrite using `[Fin.val_add, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]`. Establish `hnle : ¬ i ≤ i + k` using `by rw [Fin.le_iff_val_le_val, hv]; omega`.

Rewrite using `[if_neg hnle, hv]`. Establish `hpow : s ^ ((i : ℕ) + k) = s ^ p * s ^ ((i : ℕ) + k - p)`. Rewrite using `[← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Generalize the expression as in `intSeriesEval (residuePart F p k) (s ^ p) = G`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem normMatrix_row (hR : IntSeriesRing.Statement) {F : PowerSeries ℤ} {r : ℝ} (hr : 0 < r)
    (hF : IntSeriesConv F r) {p : ℕ} [NeZero p] (s : ℂ) (hs : ‖s‖ ≤ r) (i : Fin p) :
    ∑ k : Fin p, intSeriesEval (normMatrix F p i k) (s ^ p) * s ^ (k : ℕ) =
      s ^ (i : ℕ) * intSeriesEval F s := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  obtain ⟨-, hmul, -, -, -⟩ := hR (r ^ p) (pow_nonneg hr.le p)
  have hq : ‖s ^ p‖ ≤ r ^ p := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hs p
  have hentry : ∀ k : Fin p, intSeriesEval (normMatrix F p i k) (s ^ p) =
      (if i ≤ k then 1 else s ^ p) * intSeriesEval (residuePart F p ((k - i : Fin p) : ℕ)) (s ^ p) := by
    intro k
    simp only [normMatrix, Matrix.of_apply]
    split_ifs
    · rw [one_mul, one_mul]
    · rw [hmul _ _ (intSeriesConv_X _) (residuePart_conv hr hF hp _) _ hq, intSeriesEval_X]
  rw [intSeriesEval_split hR hr hF hp s hs, Finset.mul_sum]
  symm
  apply Fintype.sum_equiv (Equiv.addLeft i)
  intro k
  simp only [Equiv.coe_addLeft]
  rw [hentry, add_sub_cancel_left]
  have hi := i.is_lt
  have hk := k.is_lt
  by_cases h : (i : ℕ) + k < p
  · have hv : ((i + k : Fin p) : ℕ) = i + k := by rw [Fin.val_add, Nat.mod_eq_of_lt h]
    have hle : i ≤ i + k := by rw [Fin.le_iff_val_le_val, hv]; omega
    rw [if_pos hle, hv, pow_add]
    ring
  · have hv : ((i + k : Fin p) : ℕ) = i + k - p := by
      rw [Fin.val_add, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have hnle : ¬ i ≤ i + k := by rw [Fin.le_iff_val_le_val, hv]; omega
    rw [if_neg hnle, hv]
    have hpow : s ^ ((i : ℕ) + k) = s ^ p * s ^ ((i : ℕ) + k - p) := by
      rw [← pow_add]; congr 1; omega
    generalize intSeriesEval (residuePart F p k) (s ^ p) = G
    calc s ^ (i : ℕ) * (s ^ (k : ℕ) * G) = s ^ ((i : ℕ) + k) * G := by rw [pow_add]; ring
      _ = _ := by rw [hpow]; ring

/- English proof (translation)
Introduce `F r hr hF p hp j`. Establish `: NeZero p` using `⟨hp.ne'⟩`. Take `⟨⟨S, hS⟩, hmul, hhas, -, -⟩` from `hR (r ^ p) (pow_nonneg hr.le p)`. Distinguish the cases in `hj : p < j`. Use `⟨0, ?_, fun t _ _ ↦ ?_⟩` and prove the remaining obligations.

Simplify using `[IntSeriesConv]`. Rewrite using `[Multiset.esymm, Multiset.powersetCard_eq_empty _ (by simpa using hj)]`. Simplify using `[intSeriesEval]`. Use `push Not at hj`. Establish `hmem : ∀ i k, normMatrix F p i k ∈ S`.

Introduce `i k`. Simplify using `only [normMatrix, Matrix.of_apply]`. Use `split_ifs`. Rewrite using `[one_mul, hS]`. Conclude with `residuePart_conv hr hF hp _`.

Conclude with `S.mul_mem ((hS _).2 (intSeriesConv_X _)) ((hS _).2 (residuePart_conv hr hF hp _))`. Set `M : Matrix (Fin p) (Fin p) S` to `Matrix.of fun i k ↦ ⟨normMatrix F p i k, hmem i k⟩`. Set `e : S` to `(-1) ^ j * M.charpoly.coeff (p - j)`. Use `⟨e, (hS _).1 e.2, fun t ht htr ↦ ?_⟩` and prove the remaining obligations. Establish `hq : ‖t ^ p‖ ≤ r ^ p` using `by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) htr p`.

Set `φ : S →+* ℂ` to `evalHom S (t ^ p) (fun F G ↦ hmul F G ((hS _).1 F.2) ((hS _).1 G.2) _ hq) (fun F ↦ hhas F ((hS _).1 F.2) _ hq)`. Establish `hφ : ∀ f : S, φ f = intSeriesEval f (t ^ p)` using `fun _ ↦ rfl`. Use `set ζ := Complex.exp (2 * π * Complex.I / p) with hζdef`. Establish `hζ : IsPrimitiveRoot ζ p` using `Complex.isPrimitiveRoot_exp p hp.ne'`. Establish `hexp : ∀ a : ℕ, Complex.exp (2 * π * Complex.I * a / p) = ζ ^ a`.

Introduce `a`. Rewrite using `[hζdef, ← Complex.exp_nat_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Set `v : Fin p → ℂ` to `fun a ↦ ζ ^ (a : ℕ) * t`.

Establish `hvnorm : ∀ a, ‖v a‖ ≤ r`. Introduce `a`. Simplify `htr` using `[v, norm_pow, hζ.norm'_eq_one hp.ne']`. Establish `hvpow : ∀ a, v a ^ p = t ^ p`. Introduce `a`.

Simplify using `only [v]`. Rewrite using `[mul_pow, ← pow_mul, mul_comm (a : ℕ) p, pow_mul, hζ.pow_eq_one, one_pow, one_mul]`. Establish `hvinj : Function.Injective v`. Introduce `a b hab`. Conclude with `Fin.ext (hζ.pow_inj a.is_lt b.is_lt (mul_right_cancel₀ ht hab))`.

Set `d : Fin p → ℂ` to `fun a ↦ intSeriesEval F (v a)`. Set `A` to `M.map φ`. Establish `hA : ∀ i k, A i k = intSeriesEval (normMatrix F p i k) (t ^ p)` using `fun _ _ ↦ rfl`. Set `V` to `(Matrix.vandermonde v).transpose`. Establish `hAV : A * V = V * Matrix.diagonal d`.

Use extensionality with `i a`. Rewrite using `[Matrix.mul_apply, Matrix.mul_diagonal]`. Simplify using `only [V, Matrix.transpose_apply, Matrix.vandermonde_apply, hA]`. Rewrite using `[← hvpow a]`. Conclude with `normMatrix_row hR hr hF (v a) (hvnorm a) i`.

Establish `hdet : IsUnit V.det`. Rewrite using `[Matrix.det_transpose, isUnit_iff_ne_zero]`. Conclude with `Matrix.det_vandermonde_ne_zero_iff.mpr hvinj`. Establish `hchar : A.charpoly = (Matrix.diagonal d).charpoly`. Establish `hconj : A = V * Matrix.diagonal d * V⁻¹`.

Rewrite using `[← hAV, mul_assoc, Matrix.mul_nonsing_inv _ hdet, mul_one]`. Rewrite using `[hconj, Matrix.charpoly_mul_comm, ← mul_assoc, Matrix.nonsing_inv_mul _ hdet, one_mul]`. Establish `hmset : (Multiset.range p).map (fun a : ℕ ↦ intSeriesEval F (Complex.exp (2 * π * Complex.I * a / p) * t)) = (Multiset.range p).map (fun a : ℕ ↦ intSeriesEval F (ζ ^ a * t))` using `Multiset.map_congr rfl fun a _ ↦ by rw [hexp]`. Rewrite using `[hmset]`. Use `set m := (Multiset.range p).map (fun a : ℕ ↦ intSeriesEval F (ζ ^ a * t)) with hm`.

Establish `hcard : Multiset.card m = p` using `by simp [hm]`. Establish `hprod : (m.map fun x ↦ Polynomial.X - Polynomial.C x).prod = A.charpoly`. Rewrite using `[hchar, Matrix.charpoly_diagonal]`. Use `(((Fin.prod_univ_eq_prod_range (fun a : ℕ ↦ Polynomial.X - Polynomial.C (intSeriesEval F (ζ ^ a * t))) p)).trans ?_).symm` and prove the remaining obligations. Rewrite using `[hm, Multiset.map_map]`.

Both sides reduce to the same expression. Establish `hcoef` using `Multiset.prod_X_sub_C_coeff m (k := p - j) (by omega)`. Rewrite `hcoef` using `[hcard, Nat.sub_sub_self hj, hprod]`. Establish `heval : intSeriesEval (e : PowerSeries ℤ) (t ^ p) = (-1) ^ j * A.charpoly.coeff (p - j)`. Rewrite using `[← hφ]`.

Use `show φ ((-1) ^ j * M.charpoly.coeff (p - j)) = _`. Rewrite using `[map_mul, map_pow, map_neg, map_one, ← Polynomial.coeff_map, ← Matrix.charpoly_map]`. Rewrite using `[heval, hcoef, ← mul_assoc, ← mul_pow]`. Simplify using the standard rewrite rules.
-/
theorem proof (hR : IntSeriesRing.Statement) : IntSeriesNorm.Statement := by
  intro F r hr hF p hp j
  have : NeZero p := ⟨hp.ne'⟩
  obtain ⟨⟨S, hS⟩, hmul, hhas, -, -⟩ := hR (r ^ p) (pow_nonneg hr.le p)
  by_cases hj : p < j
  · refine ⟨0, ?_, fun t _ _ ↦ ?_⟩
    · simp [IntSeriesConv]
    · rw [Multiset.esymm, Multiset.powersetCard_eq_empty _ (by simpa using hj)]
      simp [intSeriesEval]
  push Not at hj
  have hmem : ∀ i k, normMatrix F p i k ∈ S := by
    intro i k
    simp only [normMatrix, Matrix.of_apply]
    split_ifs
    · rw [one_mul, hS]; exact residuePart_conv hr hF hp _
    · exact S.mul_mem ((hS _).2 (intSeriesConv_X _)) ((hS _).2 (residuePart_conv hr hF hp _))
  let M : Matrix (Fin p) (Fin p) S := Matrix.of fun i k ↦ ⟨normMatrix F p i k, hmem i k⟩
  let e : S := (-1) ^ j * M.charpoly.coeff (p - j)
  refine ⟨e, (hS _).1 e.2, fun t ht htr ↦ ?_⟩
  have hq : ‖t ^ p‖ ≤ r ^ p := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) htr p
  let φ : S →+* ℂ := evalHom S (t ^ p)
    (fun F G ↦ hmul F G ((hS _).1 F.2) ((hS _).1 G.2) _ hq) (fun F ↦ hhas F ((hS _).1 F.2) _ hq)
  have hφ : ∀ f : S, φ f = intSeriesEval f (t ^ p) := fun _ ↦ rfl
  set ζ := Complex.exp (2 * π * Complex.I / p) with hζdef
  have hζ : IsPrimitiveRoot ζ p := Complex.isPrimitiveRoot_exp p hp.ne'
  have hexp : ∀ a : ℕ, Complex.exp (2 * π * Complex.I * a / p) = ζ ^ a := by
    intro a; rw [hζdef, ← Complex.exp_nat_mul]; congr 1; ring
  let v : Fin p → ℂ := fun a ↦ ζ ^ (a : ℕ) * t
  have hvnorm : ∀ a, ‖v a‖ ≤ r := by
    intro a; simpa [v, norm_pow, hζ.norm'_eq_one hp.ne'] using htr
  have hvpow : ∀ a, v a ^ p = t ^ p := by
    intro a
    simp only [v]
    rw [mul_pow, ← pow_mul, mul_comm (a : ℕ) p, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  have hvinj : Function.Injective v := by
    intro a b hab
    exact Fin.ext (hζ.pow_inj a.is_lt b.is_lt (mul_right_cancel₀ ht hab))
  let d : Fin p → ℂ := fun a ↦ intSeriesEval F (v a)
  let A := M.map φ
  have hA : ∀ i k, A i k = intSeriesEval (normMatrix F p i k) (t ^ p) := fun _ _ ↦ rfl
  let V := (Matrix.vandermonde v).transpose
  have hAV : A * V = V * Matrix.diagonal d := by
    ext i a
    rw [Matrix.mul_apply, Matrix.mul_diagonal]
    simp only [V, Matrix.transpose_apply, Matrix.vandermonde_apply, hA]
    rw [← hvpow a]
    exact normMatrix_row hR hr hF (v a) (hvnorm a) i
  have hdet : IsUnit V.det := by
    rw [Matrix.det_transpose, isUnit_iff_ne_zero]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hvinj
  have hchar : A.charpoly = (Matrix.diagonal d).charpoly := by
    have hconj : A = V * Matrix.diagonal d * V⁻¹ := by
      rw [← hAV, mul_assoc, Matrix.mul_nonsing_inv _ hdet, mul_one]
    rw [hconj, Matrix.charpoly_mul_comm, ← mul_assoc, Matrix.nonsing_inv_mul _ hdet, one_mul]
  have hmset : (Multiset.range p).map (fun a : ℕ ↦
      intSeriesEval F (Complex.exp (2 * π * Complex.I * a / p) * t)) =
      (Multiset.range p).map (fun a : ℕ ↦ intSeriesEval F (ζ ^ a * t)) :=
    Multiset.map_congr rfl fun a _ ↦ by rw [hexp]
  rw [hmset]
  set m := (Multiset.range p).map (fun a : ℕ ↦ intSeriesEval F (ζ ^ a * t)) with hm
  have hcard : Multiset.card m = p := by simp [hm]
  have hprod : (m.map fun x ↦ Polynomial.X - Polynomial.C x).prod = A.charpoly := by
    rw [hchar, Matrix.charpoly_diagonal]
    refine (((Fin.prod_univ_eq_prod_range
      (fun a : ℕ ↦ Polynomial.X - Polynomial.C (intSeriesEval F (ζ ^ a * t))) p)).trans ?_).symm
    rw [hm, Multiset.map_map]
    rfl
  have hcoef := Multiset.prod_X_sub_C_coeff m (k := p - j) (by omega)
  rw [hcard, Nat.sub_sub_self hj, hprod] at hcoef
  have heval : intSeriesEval (e : PowerSeries ℤ) (t ^ p) = (-1) ^ j * A.charpoly.coeff (p - j) := by
    rw [← hφ]
    show φ ((-1) ^ j * M.charpoly.coeff (p - j)) = _
    rw [map_mul, map_pow, map_neg, map_one, ← Polynomial.coeff_map, ← Matrix.charpoly_map]
  rw [heval, hcoef, ← mul_assoc, ← mul_pow]
  simp

end IntSeriesNorm

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
