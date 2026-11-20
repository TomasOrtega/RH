import Mathlib
import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuation
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.WtAddSingle
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LegendreBoundsFactorialMultiIndexCapelli

open ReciprocityTheory.PGsh

namespace GlobalTheory.DetPairingBound

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps

/- English proof (translation)
Use `show (Matrix.mvPolynomialX (Fin n) (Fin n) C).det.IsHomogeneous n`. Rewrite using `[Matrix.det_apply']`. Use `IsHomogeneous.sum _ _ _ fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[← map_intCast (MvPolynomial.C : C →+* MvPolynomial (Fin n × Fin n) C)]`. Use `IsHomogeneous.C_mul ?_ _` and prove the remaining obligations.

Establish `h` using `IsHomogeneous.prod (Finset.univ : Finset (Fin n)) (fun i => Matrix.mvPolynomialX (Fin n) (Fin n) C (σ i) i) (fun _ => 1) (fun i _ => by simpa [Matrix.mvPolynomialX_apply] using isHomogeneous_X (R := C) ((σ i, i) : Fin n × Fin n))`. Simplify using `using h`.
-/
theorem cayDet_isHomogeneous (n : ℕ) (C : Type) [CommRing C] :
    (cayDet n C).IsHomogeneous n := by
  show (Matrix.mvPolynomialX (Fin n) (Fin n) C).det.IsHomogeneous n
  rw [Matrix.det_apply']
  refine IsHomogeneous.sum _ _ _ fun σ _ => ?_
  rw [← map_intCast (MvPolynomial.C : C →+* MvPolynomial (Fin n × Fin n) C)]
  refine IsHomogeneous.C_mul ?_ _
  have h := IsHomogeneous.prod (Finset.univ : Finset (Fin n))
    (fun i => Matrix.mvPolynomialX (Fin n) (Fin n) C (σ i) i) (fun _ => 1)
    (fun i _ => by simpa [Matrix.mvPolynomialX_apply] using isHomogeneous_X (R := C) ((σ i, i) : Fin n × Fin n))
  simpa using h

/- English proof (translation)
Rewrite using `[← cayDet_map (R := C), ← map_pow, coeff_map, eq_intCast]`. Conclude with `intCast_nonneg v _`.
-/
theorem coeff_cayDet_pow_nonneg (C : Type) [Field C] (v : AddValuation C (WithTop ℝ))
    (n x : ℕ) (A : Fin n × Fin n →₀ ℕ) : 0 ≤ v (coeff A (cayDet n C ^ x)) := by
  rw [← cayDet_map (R := C), ← map_pow, coeff_map, eq_intCast]
  exact intCast_nonneg v _

/- English proof (translation)
Establish `h` using `(cayDet_isHomogeneous n C).pow x`. Rewrite using `[← Finsupp.degree_eq_sum]`. Assume the negation of the conclusion as `hne`. Conclude with `(mem_support_iff.mp hA) (h.coeff_eq_zero hne)`.
-/
theorem sum_eq_of_mem_support (C : Type) [CommRing C] (n x : ℕ) (A : Fin n × Fin n →₀ ℕ)
    (hA : A ∈ (cayDet n C ^ x).support) : ∑ j, A j = n * x := by
  have h := (cayDet_isHomogeneous n C).pow x
  rw [← Finsupp.degree_eq_sum]
  by_contra hne
  exact (mem_support_iff.mp hA) (h.coeff_eq_zero hne)

/- English proof (translation)
Establish `hD0 : D ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hD`. Break down `eq_or_ne N 0 with rfl | hN0` into its components or cases. Simplify using the standard rewrite rules.

Take `⟨b, hb⟩` from `exists_real v hN0`. Rewrite using `[div_eq_coe v hD0 hb hD]`. Rewrite `hN` using `[hb, WithTop.coe_le_coe]`. Conclude with `WithTop.coe_le_coe.mpr (by linarith)`.
-/
theorem le_val_div {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {N D : C} {a d r : ℝ}
    (hN : (a : WithTop ℝ) ≤ v N) (hD : v D = d) (h : r ≤ a - d) : (r : WithTop ℝ) ≤ v (N / D) := by
  have hD0 : D ≠ 0 := by
    rintro rfl
    simp at hD
  rcases eq_or_ne N 0 with rfl | hN0
  · simp
  · obtain ⟨b, hb⟩ := exists_real v hN0
    rw [div_eq_coe v hD0 hb hD]
    rw [hb, WithTop.coe_le_coe] at hN
    exact WithTop.coe_le_coe.mpr (by linarith)

/- English proof (translation)
Introduce `C _ _ v l hl hvl i n₀ s Q hs hn₀ hQ`. Establish `hvnat : ∀ m : ℕ, m ≠ 0 → v (m : C) = ((padicValNat l m : ℝ) : WithTop ℝ)`. Introduce `m hm`. Rewrite using `[natCast_eq_factorization v hl hvl hm, Nat.factorization_def m hl]`. Take `⟨-, hL2, hL3⟩` from `GlobalTheory.LegendreBounds.legendre_bounds l hl`.

Establish `hk0 : l ^ i * s ≠ 0` using `Nat.mul_ne_zero (pow_ne_zero _ hl.ne_zero) (by omega)`. Establish `hP` using `GlobalTheory.DetPowPairing.main C n₀ (l ^ i * s)`. Rewrite `hP` using `[← Nat.cast_prod, ← Nat.cast_prod]`. Establish `hF0 : (∏ c ∈ Finset.range n₀, c.factorial) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun c _ => Nat.factorial_ne_zero c`. Establish `hF1 : (∏ c ∈ Finset.range n₀, (l ^ i * s + c).factorial) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun c _ => Nat.factorial_ne_zero _`.

Establish `hF0' : ((∏ c ∈ Finset.range n₀, c.factorial : ℕ) : C) ≠ 0` using `Nat.cast_ne_zero.mpr hF0`. Establish `hDen` using `(eq_div_iff hF0').mpr ((mul_comm _ _).trans hP)`. Establish `hvD` using `div_eq_coe v hF0' (hvnat _ hF1) (hvnat _ hF0)`. Rewrite `hvD` using `[← hDen]`. Take `⟨wb, hwb⟩ : ∃ wb : ℝ, wb = (n₀ : ℝ) * ((l : ℝ) ^ i * s) / ((l : ℝ) - 1) - (n₀ : ℝ) ^ 2 * (Real.logb l ((n₀ : ℝ) * ((l : ℝ) ^ i * s)) + 1)` from `⟨_, rfl⟩`.

Take `⟨qb, hqb⟩ : ∃ qb : ℝ, qb = (s : ℝ) / 8 - (n₀ : ℝ) ^ 2 * (Real.logb l (n₀ * s) + 1)` from `⟨_, rfl⟩`. Establish `hnum : ∀ A ∈ (cayDet n₀ C ^ (l ^ i * s)).support, ((wb + qb : ℝ) : WithTop ℝ) ≤ v (MvPolynomial.coeff A (cayDet n₀ C ^ (l ^ i * s)) * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A Q)`. Introduce `A hA`. Establish `hsum` using `sum_eq_of_mem_support C n₀ (l ^ i * s) A hA`. Establish `hW` using `hL2 (Fin n₀ × Fin n₀) A (by rw [hsum]; exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) hk0))`.

Rewrite `hW` using `[hsum]`. Simplify using `only [Fintype.card_prod, Fintype.card_fin] at hW`. Move the coercions through the operations in `at hW`. Establish `hwt : (A.prod fun _ e => (e.factorial : C)) = ((∏ j, (A j).factorial : ℕ) : C)`. Rewrite using `[Finsupp.prod_fintype _ _ (fun _ => by simp), Nat.cast_prod]`.

Establish `hne : (∏ j, (A j).factorial) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun j _ => Nat.factorial_ne_zero _`. Establish `h2 : (wb : WithTop ℝ) ≤ ((padicValNat l (∏ j, (A j).factorial) : ℝ) : WithTop ℝ)` using `WithTop.coe_le_coe.mpr (by rw [hwb, sq]; linarith)`. Establish `h3 : (qb : WithTop ℝ) ≤ v (MvPolynomial.coeff A Q)`. Rewrite using `[hqb]`. Conclude with `hQ A`.

Rewrite using `[AddValuation.map_mul, AddValuation.map_mul, hwt, hvnat _ hne]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[zero_add, WithTop.coe_add]`. Use `_ ≤ _ := add_le_add (add_le_add (coeff_cayDet_pow_nonneg C v n₀ _ A) h2) h3`. Use `le_val_div v (a := wb + qb) (AddValuation.map_le_sum v hnum) hvD ?_` and prove the remaining obligations.

Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast hl.one_lt`. Establish `hn1 : (1 : ℝ) ≤ n₀` using `by exact_mod_cast hn₀`. Establish `hs1 : (1 : ℝ) ≤ s` using `by exact_mod_cast hs`. Establish `hn0 : (n₀ : ℝ) ≠ 0` using `(by linarith : (0 : ℝ) < n₀).ne'`. Establish `hs0 : (s : ℝ) ≠ 0` using `(by linarith : (0 : ℝ) < s).ne'`.

Establish `hli : (l : ℝ) ^ i ≠ 0` using `pow_ne_zero _ (by linarith : (0 : ℝ) < l).ne'`. Establish `hLn` using `Real.logb_nonneg hl1 hn1`. Establish `hLs` using `Real.logb_nonneg hl1 hs1`. Establish `hlK : Real.logb l ((n₀ : ℝ) * ((l : ℝ) ^ i * s)) = Real.logb l n₀ + i + Real.logb l s`. Rewrite using `[Real.logb_mul hn0 (mul_ne_zero hli hs0), Real.logb_mul hli hs0, Real.logb_pow, Real.logb_self_eq_one hl1]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hlQ : Real.logb l ((n₀ : ℝ) * s) = Real.logb l n₀ + Real.logb l s` using `Real.logb_mul hn0 hs0`. Establish `h3` using `hL3 n₀ (l ^ i * s)`. Move the coercions through the operations in `at h3`. Establish `hsq : (n₀ : ℝ) * (Real.logb l n₀ + 1) ≤ (n₀ : ℝ) ^ 2 * (Real.logb l n₀ + 1)` using `mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)`.

Rewrite using `[hwb, hqb, hlK, hlQ]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem main : (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → ∀ (i n₀ s : ℕ) (Q : MvPolynomial (Fin n₀ × Fin n₀) C), 1 ≤ s → 1 ≤ n₀ →
    (∀ A, (((s : ℝ) / 8 - (n₀ : ℝ) ^ 2 * (Real.logb l (n₀ * s) + 1) : ℝ) : WithTop ℝ) ≤ v (MvPolynomial.coeff A Q)) →
    (((s : ℝ) / 8 - (n₀ : ℝ) ^ 2 * (3 * Real.logb l n₀ + 2 * Real.logb l s + i + 3) : ℝ) : WithTop ℝ) ≤
      v ((∑ A ∈ (cayDet n₀ C ^ (l ^ i * s)).support, MvPolynomial.coeff A (cayDet n₀ C ^ (l ^ i * s)) * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (Q)) / (∑ A ∈ (cayDet n₀ C ^ (l ^ i * s)).support, MvPolynomial.coeff A (cayDet n₀ C ^ (l ^ i * s)) * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (cayDet n₀ C ^ (l ^ i * s))))) := by
  intro C _ _ v l hl hvl i n₀ s Q hs hn₀ hQ
  have hvnat : ∀ m : ℕ, m ≠ 0 → v (m : C) = ((padicValNat l m : ℝ) : WithTop ℝ) := by
    intro m hm
    rw [natCast_eq_factorization v hl hvl hm, Nat.factorization_def m hl]
  obtain ⟨-, hL2, hL3⟩ := GlobalTheory.LegendreBounds.legendre_bounds l hl
  have hk0 : l ^ i * s ≠ 0 := Nat.mul_ne_zero (pow_ne_zero _ hl.ne_zero) (by omega)

  have hP := GlobalTheory.DetPowPairing.main C n₀ (l ^ i * s)
  rw [← Nat.cast_prod, ← Nat.cast_prod] at hP
  have hF0 : (∏ c ∈ Finset.range n₀, c.factorial) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun c _ => Nat.factorial_ne_zero c
  have hF1 : (∏ c ∈ Finset.range n₀, (l ^ i * s + c).factorial) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun c _ => Nat.factorial_ne_zero _
  have hF0' : ((∏ c ∈ Finset.range n₀, c.factorial : ℕ) : C) ≠ 0 := Nat.cast_ne_zero.mpr hF0
  have hDen := (eq_div_iff hF0').mpr ((mul_comm _ _).trans hP)
  have hvD := div_eq_coe v hF0' (hvnat _ hF1) (hvnat _ hF0)
  rw [← hDen] at hvD

  obtain ⟨wb, hwb⟩ : ∃ wb : ℝ, wb = (n₀ : ℝ) * ((l : ℝ) ^ i * s) / ((l : ℝ) - 1) -
      (n₀ : ℝ) ^ 2 * (Real.logb l ((n₀ : ℝ) * ((l : ℝ) ^ i * s)) + 1) := ⟨_, rfl⟩
  obtain ⟨qb, hqb⟩ : ∃ qb : ℝ, qb = (s : ℝ) / 8 - (n₀ : ℝ) ^ 2 * (Real.logb l (n₀ * s) + 1) :=
    ⟨_, rfl⟩
  have hnum : ∀ A ∈ (cayDet n₀ C ^ (l ^ i * s)).support, ((wb + qb : ℝ) : WithTop ℝ) ≤
      v (MvPolynomial.coeff A (cayDet n₀ C ^ (l ^ i * s)) * (A.prod fun _ e => (e.factorial : C)) *
        MvPolynomial.coeff A Q) := by
    intro A hA
    have hsum := sum_eq_of_mem_support C n₀ (l ^ i * s) A hA
    have hW := hL2 (Fin n₀ × Fin n₀) A
      (by rw [hsum]; exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) hk0))
    rw [hsum] at hW
    simp only [Fintype.card_prod, Fintype.card_fin] at hW
    push_cast at hW
    have hwt : (A.prod fun _ e => (e.factorial : C)) = ((∏ j, (A j).factorial : ℕ) : C) := by
      rw [Finsupp.prod_fintype _ _ (fun _ => by simp), Nat.cast_prod]
    have hne : (∏ j, (A j).factorial) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ => Nat.factorial_ne_zero _
    have h2 : (wb : WithTop ℝ) ≤ ((padicValNat l (∏ j, (A j).factorial) : ℝ) : WithTop ℝ) :=
      WithTop.coe_le_coe.mpr (by rw [hwb, sq]; linarith)
    have h3 : (qb : WithTop ℝ) ≤ v (MvPolynomial.coeff A Q) := by
      rw [hqb]; exact hQ A
    rw [AddValuation.map_mul, AddValuation.map_mul, hwt, hvnat _ hne]
    calc ((wb + qb : ℝ) : WithTop ℝ) = 0 + (wb : WithTop ℝ) + (qb : WithTop ℝ) := by
          rw [zero_add, WithTop.coe_add]
      _ ≤ _ := add_le_add (add_le_add (coeff_cayDet_pow_nonneg C v n₀ _ A) h2) h3
  refine le_val_div v (a := wb + qb) (AddValuation.map_le_sum v hnum) hvD ?_

  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hn1 : (1 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hn0 : (n₀ : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < n₀).ne'
  have hs0 : (s : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < s).ne'
  have hli : (l : ℝ) ^ i ≠ 0 := pow_ne_zero _ (by linarith : (0 : ℝ) < l).ne'
  have hLn := Real.logb_nonneg hl1 hn1
  have hLs := Real.logb_nonneg hl1 hs1
  have hlK : Real.logb l ((n₀ : ℝ) * ((l : ℝ) ^ i * s)) =
      Real.logb l n₀ + i + Real.logb l s := by
    rw [Real.logb_mul hn0 (mul_ne_zero hli hs0), Real.logb_mul hli hs0, Real.logb_pow,
      Real.logb_self_eq_one hl1]
    ring
  have hlQ : Real.logb l ((n₀ : ℝ) * s) = Real.logb l n₀ + Real.logb l s :=
    Real.logb_mul hn0 hs0
  have h3 := hL3 n₀ (l ^ i * s)
  push_cast at h3
  have hsq : (n₀ : ℝ) * (Real.logb l n₀ + 1) ≤ (n₀ : ℝ) ^ 2 * (Real.logb l n₀ + 1) :=
    mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
  rw [hwb, hqb, hlK, hlQ]
  linarith

end GlobalTheory.DetPairingBound
