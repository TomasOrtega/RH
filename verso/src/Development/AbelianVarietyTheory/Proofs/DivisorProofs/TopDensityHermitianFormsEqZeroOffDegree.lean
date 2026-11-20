import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityComplexFormAevalDzWedgeDzbarStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
namespace GlobalTheory.ChernCalc

noncomputable def linPoly {n : ℕ} (α : V n → V n → ℂ) : MvPolynomial (Fin n × Fin n) ℂ :=
  ∑ a, ∑ b, C (α (coordVec a) (coordVec b)) * X (a, b)

/- English proof (translation)
Unfold `linPoly`. Use `IsHomogeneous.sum _ _ _ fun a _ => IsHomogeneous.sum _ _ _ fun b _ => ?_` and prove the remaining obligations. Simplify using `using (isHomogeneous_C (Fin n × Fin n) (α (coordVec a) (coordVec b))).mul (isHomogeneous_X ℂ (a, b))`.
-/
theorem linPoly_isHomogeneous {n : ℕ} (α : V n → V n → ℂ) : (linPoly α).IsHomogeneous 1 := by
  unfold linPoly
  refine IsHomogeneous.sum _ _ _ fun a _ => IsHomogeneous.sum _ _ _ fun b _ => ?_
  simpa using (isHomogeneous_C (Fin n × Fin n) (α (coordVec a) (coordVec b))).mul (isHomogeneous_X ℂ (a, b))

/- English proof (translation)
Simplify using `[linPoly, ofValues, map_sum, Algebra.smul_def]`.
-/
theorem aeval_sym_linPoly {n : ℕ} (α : V n → V n → ℂ) : aeval sym (linPoly α) = ofValues α := by
  simp [linPoly, ofValues, map_sum, Algebra.smul_def]

/- English proof (translation)
Rewrite using `[map_sum]`. Simplify using `[Finsupp.degree_single]`.
-/
theorem degree_permMono {n : ℕ} (w : Equiv.Perm (Fin n)) :
    Finsupp.degree (∑ a, Finsupp.single (a, w a) 1 : Fin n × Fin n →₀ ℕ) = n := by
  rw [map_sum]; simp [Finsupp.degree_single]

/- English proof (translation)
Unfold `topCoeff`. Use `Finset.sum_eq_zero fun w _ => ?_` and prove the remaining obligations. Rewrite using `[hQ.coeff_eq_zero (by rw [degree_permMono]; exact fun h => hd h.symm), mul_zero]`.
-/
theorem topCoeff_eq_zero_of_isHomogeneous {n d : ℕ} {Q : MvPolynomial (Fin n × Fin n) ℂ} (hQ : Q.IsHomogeneous d)
    (hd : d ≠ n) : topCoeff Q = 0 := by
  unfold topCoeff
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [hQ.coeff_eq_zero (by rw [degree_permMono]; exact fun h => hd h.symm), mul_zero]

/- English proof (translation)
Introduce `n κ α d P hP hd`. Establish `h1 : (aeval (fun i => ofValues (α i)) (P.map (algebraMap ℝ ℂ)) : Ev n) = aeval sym (bind₁ (fun i => linPoly (α i)) (P.map (algebraMap ℝ ℂ)))`. Rewrite using `[aeval_bind₁]`. Simplify using `only [aeval_sym_linPoly]`. Establish `hQ : (bind₁ (fun i => linPoly (α i)) (P.map (algebraMap ℝ ℂ))).IsHomogeneous d`.

Simplify using `using (hP.map (algebraMap ℝ ℂ)).aeval (fun i => linPoly (α i)) fun i => linPoly_isHomogeneous (α i)`. Rewrite using `[h1, GlobalTheory.T.topDegreeDensityComplexForm_aeval_dzWedgeDzbar, topCoeff_eq_zero_of_isHomogeneous hQ hd, zero_div]`.
-/
theorem dens_aeval_ofValues_offDeg : ∀ (n : ℕ) (κ : Type) (α : κ → V n → V n → ℂ) (d : ℕ) (P : MvPolynomial κ ℝ),
    P.IsHomogeneous d → d ≠ n →
      dens ((aeval (fun i => ofValues (α i)) (P.map (algebraMap ℝ ℂ)) : Ev n) : Alt n) = 0 := by
  intro n κ α d P hP hd
  have h1 : (aeval (fun i => ofValues (α i)) (P.map (algebraMap ℝ ℂ)) : Ev n) =
      aeval sym (bind₁ (fun i => linPoly (α i)) (P.map (algebraMap ℝ ℂ))) := by
    rw [aeval_bind₁]; simp only [aeval_sym_linPoly]
  have hQ : (bind₁ (fun i => linPoly (α i)) (P.map (algebraMap ℝ ℂ))).IsHomogeneous d := by
    simpa using (hP.map (algebraMap ℝ ℂ)).aeval (fun i => linPoly (α i)) fun i => linPoly_isHomogeneous (α i)
  rw [h1, GlobalTheory.T.topDegreeDensityComplexForm_aeval_dzWedgeDzbar, topCoeff_eq_zero_of_isHomogeneous hQ hd, zero_div]

end GlobalTheory.ChernCalc
