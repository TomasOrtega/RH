import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar BottChern ArRing ArChow HolAtlas Alt IsType IsReal dens chPart tdPart hermMat eval₂ bas relCot dRel IsRelAcyclic IsGenSmooth)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder

namespace GlobalTheory.ToddLow

open MvPolynomial

variable {σ : Type}

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on' with`. Consider the case `monomial u a`. Establish `h1 : (monomial u a : MvPolynomial σ ℚ).IsHomogeneous u.degree` using `isHomogeneous_monomial a rfl`. Establish `h2 : (monomial u a * MvPolynomial.X i : MvPolynomial σ ℚ).IsHomogeneous (u.degree + 1)` using `h1.mul (isHomogeneous_X ℚ i)`. Rewrite using `[homogeneousComponent_of_mem h1, homogeneousComponent_of_mem h2]`.

Apply the tactic sequence `by_cases h : n = u.degree <;> simp [h]`. Consider the case `add p q hp hq => simp [add_mul, hp, hq]`.
-/
theorem hc_mul_X_succ (f : MvPolynomial σ ℚ) (i : σ) (n : ℕ) :
    homogeneousComponent (n + 1) (f * MvPolynomial.X i) = homogeneousComponent n f * MvPolynomial.X i := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial u a =>
    have h1 : (monomial u a : MvPolynomial σ ℚ).IsHomogeneous u.degree := isHomogeneous_monomial a rfl
    have h2 : (monomial u a * MvPolynomial.X i : MvPolynomial σ ℚ).IsHomogeneous (u.degree + 1) :=
      h1.mul (isHomogeneous_X ℚ i)
    rw [homogeneousComponent_of_mem h1, homogeneousComponent_of_mem h2]
    by_cases h : n = u.degree <;> simp [h]
  | add p q hp hq => simp [add_mul, hp, hq]

/- English proof (translation)
Simplify using `[homogeneousComponent_zero, coeff_mul_X']`.
-/
theorem hc_mul_X_zero (f : MvPolynomial σ ℚ) (i : σ) :
    homogeneousComponent 0 (f * MvPolynomial.X i) = 0 := by
  classical
  simp [homogeneousComponent_zero, coeff_mul_X']

/- English proof (translation)
Establish `h1 : (1 : MvPolynomial σ ℚ).IsHomogeneous 0` using `isHomogeneous_one σ ℚ`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [homogeneousComponent_of_mem h1]`. Consider the case `insert j s hj ih`. Take `⟨i0, i1, i2⟩` from `ih`.

Rewrite using `[Finset.prod_insert hj, Finset.sum_insert hj, Finset.sum_insert hj]`. Use `set P := ∏ i ∈ s, (1 + C a * MvPolynomial.X i + C b * MvPolynomial.X i ^ 2 : MvPolynomial σ ℚ)`. Establish `e : (1 + C a * MvPolynomial.X j + C b * MvPolynomial.X j ^ 2) * P = P + C a * (P * MvPolynomial.X j) + C b * (P * MvPolynomial.X j * MvPolynomial.X j)` using `by ring`. Establish `ea : (C (a ^ 2 / 2) : MvPolynomial σ ℚ) * 2 = C a ^ 2`. Rewrite using `[← map_pow, ← map_ofNat C 2, ← map_mul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, homogeneousComponent_C_mul, hc_mul_X_zero, i0]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [map_add, homogeneousComponent_C_mul]`. Rewrite using `[hc_mul_X_succ _ _ 0, hc_mul_X_succ _ _ 0, hc_mul_X_zero, i0, i1]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [map_add, homogeneousComponent_C_mul]`.

Rewrite using `[hc_mul_X_succ _ _ 1, hc_mul_X_succ _ _ 1, hc_mul_X_succ _ _ 0, i0, i1, i2, map_sub]`. Take the linear combination `(-(MvPolynomial.X j * ∑ i ∈ s, MvPolynomial.X i)) * ea`.
-/
theorem hc_prod (a b : ℚ) (s : Finset σ) :
    homogeneousComponent 0 (∏ i ∈ s, (1 + C a * MvPolynomial.X i + C b * MvPolynomial.X i ^ 2 : MvPolynomial σ ℚ)) = 1 ∧
    homogeneousComponent 1 (∏ i ∈ s, (1 + C a * MvPolynomial.X i + C b * MvPolynomial.X i ^ 2 : MvPolynomial σ ℚ)) =
      C a * ∑ i ∈ s, MvPolynomial.X i ∧
    homogeneousComponent 2 (∏ i ∈ s, (1 + C a * MvPolynomial.X i + C b * MvPolynomial.X i ^ 2 : MvPolynomial σ ℚ)) =
      C (a ^ 2 / 2) * (∑ i ∈ s, MvPolynomial.X i) ^ 2 + C (b - a ^ 2 / 2) * ∑ i ∈ s, MvPolynomial.X i ^ 2 := by
  classical
  have h1 : (1 : MvPolynomial σ ℚ).IsHomogeneous 0 := isHomogeneous_one σ ℚ
  induction s using Finset.induction_on with
  | empty => simp [homogeneousComponent_of_mem h1]
  | insert j s hj ih =>
    obtain ⟨i0, i1, i2⟩ := ih
    rw [Finset.prod_insert hj, Finset.sum_insert hj, Finset.sum_insert hj]
    set P := ∏ i ∈ s, (1 + C a * MvPolynomial.X i + C b * MvPolynomial.X i ^ 2 : MvPolynomial σ ℚ)
    have e : (1 + C a * MvPolynomial.X j + C b * MvPolynomial.X j ^ 2) * P =
        P + C a * (P * MvPolynomial.X j) + C b * (P * MvPolynomial.X j * MvPolynomial.X j) := by ring
    have ea : (C (a ^ 2 / 2) : MvPolynomial σ ℚ) * 2 = C a ^ 2 := by
      rw [← map_pow, ← map_ofNat C 2, ← map_mul]; congr 1; ring
    rw [e]
    refine ⟨?_, ?_, ?_⟩
    · simp only [map_add, homogeneousComponent_C_mul, hc_mul_X_zero, i0]; ring
    · simp only [map_add, homogeneousComponent_C_mul]
      rw [hc_mul_X_succ _ _ 0, hc_mul_X_succ _ _ 0, hc_mul_X_zero, i0, i1]; ring
    · simp only [map_add, homogeneousComponent_C_mul]
      rw [hc_mul_X_succ _ _ 1, hc_mul_X_succ _ _ 1, hc_mul_X_succ _ _ 0, i0, i1, i2, map_sub]
      linear_combination (-(MvPolynomial.X j * ∑ i ∈ s, MvPolynomial.X i)) * ea

/- English proof (translation)
Introduce `r`. Use `⟨Subtype.ext ?_, Subtype.ext ?_⟩` and prove the remaining obligations. Establish `h` using `(hc_prod (σ := Fin r) (1 / 2) 0 Finset.univ).2.1`. Simplify using `only [map_zero, zero_mul, add_zero] at h`. Simplify using `only [tdPart, chPart, Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one, SetLike.val_smul, MvPolynomial.psum, smul_eq_C_mul]`.

Simplify using `using h`. Establish `h` using `(hc_prod (σ := Fin r) (1 / 2) (1 / 12) Finset.univ).2.2`. Establish `e1 : ∀ i : Fin r, (∑ m ∈ Finset.range (2 + 1), C (bernoulli' m / m.factorial) * MvPolynomial.X i ^ m : MvPolynomial (Fin r) ℚ) = 1 + C (1 / 2) * MvPolynomial.X i + C (1 / 12) * MvPolynomial.X i ^ 2`. Introduce `i`. Simplify using `only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two]`.

Evaluate the numerical expressions using `[Nat.factorial]`. Simplify using `only [tdPart, e1, h]`. Simplify using `only [chPart, AddSubgroupClass.coe_sub, SetLike.val_smul, SubmonoidClass.coe_pow, MvPolynomial.psum, smul_smul]`. Simplify using `only [smul_eq_C_mul, sub_eq_add_neg, ← neg_mul, ← map_neg]`. Evaluate the numerical expressions using `[Nat.factorial]`.
-/
theorem tdPart_low : ∀ r : ℕ, tdPart r 1 = (1 / 2 : ℚ) • chPart r 1 ∧
    tdPart r 2 = (1 / 8 : ℚ) • chPart r 1 ^ 2 - (1 / 12 : ℚ) • chPart r 2 := by
  intro r
  refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
  · have h := (hc_prod (σ := Fin r) (1 / 2) 0 Finset.univ).2.1
    simp only [map_zero, zero_mul, add_zero] at h
    simp only [tdPart, chPart, Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one,
      SetLike.val_smul, MvPolynomial.psum, smul_eq_C_mul]
    simpa using h
  · have h := (hc_prod (σ := Fin r) (1 / 2) (1 / 12) Finset.univ).2.2
    have e1 : ∀ i : Fin r, (∑ m ∈ Finset.range (2 + 1), C (bernoulli' m / m.factorial) * MvPolynomial.X i ^ m : MvPolynomial (Fin r) ℚ) =
        1 + C (1 / 2) * MvPolynomial.X i + C (1 / 12) * MvPolynomial.X i ^ 2 := by
      intro i
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two]
      norm_num [Nat.factorial]
    simp only [tdPart, e1, h]
    simp only [chPart, AddSubgroupClass.coe_sub, SetLike.val_smul, SubmonoidClass.coe_pow, MvPolynomial.psum, smul_smul]
    simp only [smul_eq_C_mul, sub_eq_add_neg, ← neg_mul, ← map_neg]
    norm_num [Nat.factorial]

end GlobalTheory.ToddLow
