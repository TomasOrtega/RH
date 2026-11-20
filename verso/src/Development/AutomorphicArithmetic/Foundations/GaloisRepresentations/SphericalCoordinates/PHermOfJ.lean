import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LineBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

/- English proof (translation)
Introduce `g E halt hI hpos`. Establish `hskew : ∀ x y, E x y = - E y x`. Introduce `x y`. Establish `h` using `halt (x + y)`. Simplify using `only [map_add, LinearMap.add_apply, halt, zero_add, add_zero] at h`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hII : ∀ x : Fin g → ℂ, Complex.I • Complex.I • x = -x`. Introduce `x`. Rewrite using `[smul_smul, Complex.I_mul_I]`. Simplify using the standard rewrite rules.

Establish `hcomm : ∀ x y : Fin g → ℂ, E (Complex.I • x) y = E (Complex.I • y) x`. Introduce `x y`. Establish `h` using `hI (Complex.I • x) y`. Rewrite `h` using `[hII, map_neg, LinearMap.neg_apply]`. Rewrite using `[← h, hskew x]`.

Expand and normalize the polynomial expressions, which then agree. Set `H : (Fin g → ℂ) → (Fin g → ℂ) → ℂ` to `fun x y => ⟨E (Complex.I • x) y, E x y⟩`. Establish `hsym : ∀ x y, H y x = star (H x y)`. Introduce `x y`. Apply `Complex.ext` to reduce the goal to its premises.

Simplify `hcomm y x` using `[H]`. Simplify `hskew y x` using `[H]`. Establish `hadd : ∀ a b y, H (a + b) y = H a y + H b y`. Introduce `a b y`. Apply the tactic sequence `apply Complex.ext <;> simp [H, smul_add]`.

Establish `hsmulI : ∀ x y, H (Complex.I • x) y = Complex.I * H x y`. Introduce `x y`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[H, hII]`. Simplify using `[H]`.

Establish `hsmulR : ∀ (r : ℝ) x y, H (r • x) y = (r : ℂ) * H x y`. Introduce `r x y`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[H, smul_comm Complex.I r x]`. Simplify using `[H]`.

Establish `hsmul : ∀ (c : ℂ) x y, H (c • x) y = c * H x y`. Introduce `c x y`. Establish `hc : c • x = c.re • x + c.im • (Complex.I • x)`. Use extensionality with `i`. Simplify using `only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]`.

Use `conv_lhs => rw [← Complex.re_add_im c]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc, hadd, hsmulR, hsmulR, hsmulI]`. Use `conv_rhs => rw [← Complex.re_add_im c]`. Expand and normalize the polynomial expressions, which then agree.

Set `e : Fin g → Fin g → ℂ` to `fun i j => if i = j then 1 else 0`. Establish `hexp : ∀ x y, H x y = ∑ i, x i * H (e i) y`. Introduce `x y`. Set `f : (Fin g → ℂ) →ₗ[ℂ] ℂ` to `{ toFun := fun x => H x y map_add' := fun a b => hadd a b y map_smul' := fun c a => by simpa using hsmul c a y }`. Simplify `LinearMap.pi_apply_eq_sum_univ f x` using `[f, e]`.

Establish `hform : ∀ x y, hermForm (Matrix.of fun i j => H (e i) (e j)) x y = H x y`. Introduce `x y`. Rewrite using `[hexp x y]`. Simplify using `only [hermForm, dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Use `congr 1`. Rewrite using `[hsym y (e i), hexp y (e i), star_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[star_mul', ← hsym (e j) (e i), mul_comm]`. Use `⟨Matrix.of fun i j => H (e i) (e j), ?_, ?_, ?_⟩` and prove the remaining obligations.

Apply `Matrix.IsHermitian.ext` to reduce the goal to its premises. Introduce `i j`. Simplify using `only [Matrix.of_apply]`. Rewrite using `[← hsym]`. Introduce `z hz`.

Rewrite using `[hform]`. Conclude with `hpos z hz`. Introduce `x y`. Rewrite using `[hform]`.
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
