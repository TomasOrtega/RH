import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityComplexFormAevalDzWedgeDzbarStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernTopDens

variable {n : ℕ}

/- English proof (translation)
Proceed by induction. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Treat this case separately. A detailed English derivation is pending.
-/
theorem coeff_aeval_C_mul_X (c : ℂ) (Q : MvPolynomial (Fin n × Fin n) ℂ) (d : Fin n × Fin n →₀ ℕ) :
    coeff d (aeval (fun y => C c * X y) Q) = c ^ (d.sum fun _ e => e) * coeff d Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial u a =>
    have : aeval (fun y => C c * X y) (monomial u a) = monomial u (c ^ (u.sum fun _ e => e) * a) := by
      rw [aeval_monomial, monomial_eq]
      simp only [mul_pow, Finsupp.prod_mul, algebraMap_eq]
      rw [Finsupp.prod, Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum, C_mul, map_prod]
      simp only [map_pow]
      ring
    rw [this, coeff_monomial, coeff_monomial]
    split_ifs with h
    · rw [h]
    · simp
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

section Rev

variable {r : Type} [Fintype r] [DecidableEq r]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem charpolyRev_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (M : Matrix r r A) :
    (M.map f).charpolyRev = M.charpolyRev.map f := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j : 1
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem charpolyRev_smul {A : Type} [CommRing A] (c : A) (M : Matrix r r A) :
    (c • M).charpolyRev = M.charpolyRev.comp (Polynomial.C c * Polynomial.X) := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_compRingHom_apply, RingHom.map_det]
  congr 1
  ext i j : 1
  by_cases h : i = j <;> simp [Matrix.one_apply, h] <;> ring

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem aeval_chernPoly (c : ℂ) (G : V n → Matrix r r ℂ) (v : V n) (k : ℕ) :
    aeval (fun y => C c * X y) (chernPoly G v k) = c ^ k • chernPoly G v k := by
  let ψ : MvPolynomial (Fin n × Fin n) ℂ →+* MvPolynomial (Fin n × Fin n) ℂ :=
    (aeval fun y => C c * X y : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ).toRingHom
  have e : ∀ p, aeval (fun y => C c * X y) p = ψ p := fun _ => rfl
  have hM : (-curvPoly G v).map ψ = (C c : MvPolynomial (Fin n × Fin n) ℂ) • (-curvPoly G v) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.smul_apply, curvPoly, Matrix.of_apply, map_neg, map_sum,
      map_mul, smul_eq_mul, Finset.mul_sum, mul_neg, ← e, aeval_X, aeval_C, algebraMap_eq]
    refine congrArg _ (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_)
    ring
  unfold chernPoly
  rw [e, ← Polynomial.coeff_map, ← charpolyRev_map, hM, charpolyRev_smul, Polynomial.comp_C_mul_X_coeff, smul_eq_C_mul,
    map_pow, mul_comm]

end Rev

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem topCoeff_aeval_C_mul_X (c : ℂ) (Q : MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (aeval (fun y => C c * X y) Q) = c ^ n * topCoeff Q := by
  unfold topCoeff
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hdeg : (∑ a, Finsupp.single (a, w a) 1 : Fin n × Fin n →₀ ℕ).sum (fun _ e => e) = n := by
    change Finsupp.degree (∑ a, Finsupp.single (a, w a) 1 : Fin n × Fin n →₀ ℕ) = n
    simp [map_sum]
  rw [coeff_aeval_C_mul_X, hdeg]
  ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts.
-/
theorem kappa_div : kappa ^ n / (Complex.I / 2) ^ n = (((Real.pi ^ n)⁻¹ : ℝ) : ℂ) := by
  rw [← div_pow, Complex.ofReal_inv, Complex.ofReal_pow, ← inv_pow]
  congr 1
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  rw [kappa]
  field_simp

end GlobalTheory.ChernTopDens

open GlobalTheory.ChernTopDens in

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem GlobalTheory.ChernCalc.dens_chernAt_re (n : ℕ) (ι : Type) (m : ι → ℕ) (R : MvPolynomial (ι × ℕ) ℝ) (G : V n → Mat m ℂ)
    (v : V n) :
    (dens ((aeval (fun x : ι × ℕ => chernAt (fun u => G u x.1) v x.2) (R.map (algebraMap ℝ ℂ)) : Ev n) : Alt n)).re =
      chernTop R G v := by
  let Φ : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] Ev n := (aeval sym).comp (aeval fun y => C kappa * X y)
  have h1 : (fun x : ι × ℕ => chernAt (fun u => G u x.1) v x.2) =
      fun x => Φ (chernPoly (fun u => G u x.1) v x.2) := by
    funext x
    simp only [Φ, AlgHom.comp_apply, aeval_chernPoly, map_smul, chernAt]
  have h2 : aeval (fun x : ι × ℕ => chernAt (fun u => G u x.1) v x.2) (R.map (algebraMap ℝ ℂ)) =
      aeval sym (aeval (fun y => C kappa * X y)
        (aeval (fun x : ι × ℕ => chernPoly (fun u => G u x.1) v x.2) R)) := by
    rw [h1, ← comp_aeval, AlgHom.comp_apply, aeval_map_algebraMap]
    rfl
  rw [h2, GlobalTheory.T.topDegreeDensityComplexForm_aeval_dzWedgeDzbar, topCoeff_aeval_C_mul_X, mul_div_right_comm, kappa_div, Complex.re_ofReal_mul]
  rfl
