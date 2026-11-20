import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LineBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.

Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Apply the first step, then apply the next step to every resulting obligation.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Introduce a local definition for the expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.W2.hermOfJ_of :
    UpperTheory.Gal.W2.HermOfJ := by
  intro g E halt hI hpos
  have hskew : ∀ x y, E x y = - E y x := by
    intro x y
    have h := halt (x + y)
    simp only [map_add, LinearMap.add_apply, halt, zero_add, add_zero] at h
    linarith
  have hII : ∀ x : Fin g → ℂ, Complex.I • Complex.I • x = -x := by
    intro x
    rw [smul_smul, Complex.I_mul_I]
    simp
  have hcomm : ∀ x y : Fin g → ℂ, E (Complex.I • x) y = E (Complex.I • y) x := by
    intro x y
    have h := hI (Complex.I • x) y
    rw [hII, map_neg, LinearMap.neg_apply] at h
    rw [← h, hskew x]
    ring
  let H : (Fin g → ℂ) → (Fin g → ℂ) → ℂ := fun x y => ⟨E (Complex.I • x) y, E x y⟩
  have hsym : ∀ x y, H y x = star (H x y) := by
    intro x y
    apply Complex.ext
    · simpa [H] using hcomm y x
    · simpa [H] using hskew y x
  have hadd : ∀ a b y, H (a + b) y = H a y + H b y := by
    intro a b y
    apply Complex.ext <;> simp [H, smul_add]
  have hsmulI : ∀ x y, H (Complex.I • x) y = Complex.I * H x y := by
    intro x y
    apply Complex.ext
    · simp [H, hII]
    · simp [H]
  have hsmulR : ∀ (r : ℝ) x y, H (r • x) y = (r : ℂ) * H x y := by
    intro r x y
    apply Complex.ext
    · simp [H, smul_comm Complex.I r x]
    · simp [H]
  have hsmul : ∀ (c : ℂ) x y, H (c • x) y = c * H x y := by
    intro c x y
    have hc : c • x = c.re • x + c.im • (Complex.I • x) := by
      ext i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
      conv_lhs => rw [← Complex.re_add_im c]
      ring
    rw [hc, hadd, hsmulR, hsmulR, hsmulI]
    conv_rhs => rw [← Complex.re_add_im c]
    ring
  let e : Fin g → Fin g → ℂ := fun i j => if i = j then 1 else 0
  have hexp : ∀ x y, H x y = ∑ i, x i * H (e i) y := by
    intro x y
    let f : (Fin g → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun x => H x y
        map_add' := fun a b => hadd a b y
        map_smul' := fun c a => by simpa using hsmul c a y }
    simpa [f, e] using LinearMap.pi_apply_eq_sum_univ f x
  have hform : ∀ x y, hermForm (Matrix.of fun i j => H (e i) (e j)) x y = H x y := by
    intro x y
    rw [hexp x y]
    simp only [hermForm, dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [hsym y (e i), hexp y (e i), star_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul', ← hsym (e j) (e i), mul_comm]
  refine ⟨Matrix.of fun i j => H (e i) (e j), ?_, ?_, ?_⟩
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [Matrix.of_apply]
    rw [← hsym]
  · intro z hz
    rw [hform]
    exact hpos z hz
  · intro x y
    rw [hform]
