import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core.SL2BruhatDecomposition

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem coe_n {R : Type} [CommRing R] (b : R) :
    ((nMat b : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = !![1, b; 0, 1] := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem coe_m {R : Type} [CommRing R] (a : Rˣ) :
    ((mMat a : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = !![(a : R), 0; 0, ((a⁻¹ : Rˣ) : R)] := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem coe_w {R : Type} [CommRing R] :
    ((wMat : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = !![0, 1; -1, 0] := rfl

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(g : Matrix (Fin 2) (Fin 2) R) = (h : Matrix (Fin 2) (Fin 2) R)`. Rewrite using `[hh, Matrix.eta_fin_two (g : Matrix (Fin 2) (Fin 2) R), h0, h1, h2, h3]`.
-/
private theorem SL2_eq_of_entries_eq_matrix {R : Type} [CommRing R] {g : SL(2, R)} {p q r s : R}
    {h : SL(2, R)} (hh : (h : Matrix (Fin 2) (Fin 2) R) = !![p, q; r, s])
    (h0 : g 0 0 = p) (h1 : g 0 1 = q) (h2 : g 1 0 = r) (h3 : g 1 1 = s) : g = h := by
  apply Subtype.ext
  change (g : Matrix (Fin 2) (Fin 2) R) = (h : Matrix (Fin 2) (Fin 2) R)
  rw [hh, Matrix.eta_fin_two (g : Matrix (Fin 2) (Fin 2) R), h0, h1, h2, h3]

/- English proof (translation)
Introduce `R _ g`. Establish `hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1`. Establish `h` using `g.det_coe`. Rewrite `h` using `[Matrix.det_fin_two]`. Then use the resulting hypothesis. Establish `hw : (wMat : SL(2, R))⁻¹ = wMat * wMat * wMat`.

Apply `inv_eq_of_mul_eq_one_right` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(((wMat * (wMat * wMat * wMat) : SL(2, R))) : Matrix (Fin 2) (Fin 2) R) = ((1 : SL(2, R)) : Matrix (Fin 2) (Fin 2) R)`. Simplify using `only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, coe_w, Matrix.mul_fin_two, Matrix.one_fin_two]`. Simplify using the standard rewrite rules.

Use `⟨?_, ?_, ?_, hw⟩` and prove the remaining obligations. Introduce `c hc`. Establish `hu : (c : R) * ((c⁻¹ : Rˣ) : R) = 1` using `by simp`. Establish `hinv : ((-c⁻¹ : Rˣ) : R) = -((c⁻¹ : Rˣ) : R)` using `by simp`. Establish `hinv2 : (((-c⁻¹ : Rˣ)⁻¹ : Rˣ) : R) = -(c : R)` using `by simp`.

Use `SL2_eq_of_entries_eq_matrix (p := g 0 0) (q := g 0 1) (r := g 1 0) (s := g 1 1) ?_ rfl rfl rfl rfl` and prove the remaining obligations. Simplify using `only [Matrix.SpecialLinearGroup.coe_mul, coe_n, coe_m, coe_w, Matrix.mul_fin_two, hinv, hinv2]`. Generalize the expression as in `((c⁻¹ : Rˣ) : R) = u at hu`. Rewrite `hdet`, the goal using `[hc]`. Reduce the equality to equality of the corresponding arguments.

Take the linear combination `(g 0 0) * hu`. Take the linear combination `(g 0 0 * g 1 1 * u + g 0 1) * hu + u * hdet`. Expand and normalize the polynomial expressions, which then agree. Take the linear combination `(g 1 1) * hu`. Introduce `a ha`.

Establish `hu : (a : R) * ((a⁻¹ : Rˣ) : R) = 1` using `by simp`. Rewrite using `[hw]`. Use `SL2_eq_of_entries_eq_matrix (p := g 0 0) (q := g 0 1) (r := g 1 0) (s := g 1 1) ?_ rfl rfl rfl rfl` and prove the remaining obligations. Simplify using `only [Matrix.SpecialLinearGroup.coe_mul, coe_n, coe_m, coe_w, Matrix.mul_fin_two]`. Generalize the expression as in `((a⁻¹ : Rˣ) : R) = u at hu`.

Rewrite `hdet`, the goal using `[ha]`. Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree. Take the linear combination `(g 0 1) * hu`. Take the linear combination `(g 1 0) * hu`.

Take the linear combination `(g 1 0 * g 0 1 * u + g 1 1) * hu - u * hdet`. Introduce `a ha hc`. Establish `hu : (a : R) * ((a⁻¹ : Rˣ) : R) = 1` using `by simp`. Use `SL2_eq_of_entries_eq_matrix (p := g 0 0) (q := g 0 1) (r := g 1 0) (s := g 1 1) ?_ rfl rfl rfl rfl` and prove the remaining obligations. Simplify using `only [Matrix.SpecialLinearGroup.coe_mul, coe_n, coe_m, Matrix.mul_fin_two]`.

Generalize the expression as in `((a⁻¹ : Rˣ) : R) = u at hu`. Rewrite `hdet`, the goal using `[ha, hc]`. Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree. Take the linear combination `(g 0 1) * hu`.

Expand and normalize the polynomial expressions, which then agree. Take the linear combination `(g 1 1) * hu - u * hdet`.
-/
theorem decompositions : ∀ (R : Type) [CommRing R] (g : SL(2, R)), (∀ c : Rˣ, g 1 0 = (c : R) → g = nMat (g 0 0 * ((c⁻¹ : Rˣ) : R)) * mMat (-c⁻¹) * wMat * nMat (g 1 1 * ((c⁻¹ : Rˣ) : R))) ∧ (∀ a : Rˣ, g 0 0 = (a : R) → g = wMat⁻¹ * nMat (-(g 1 0 * ((a⁻¹ : Rˣ) : R))) * wMat * mMat a * nMat (g 0 1 * ((a⁻¹ : Rˣ) : R))) ∧ (∀ a : Rˣ, g 0 0 = (a : R) → g 1 0 = 0 → g = nMat (g 0 1 * (a : R)) * mMat a) ∧ (wMat : SL(2, R))⁻¹ = wMat * wMat * wMat := by
  intro R _ g
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := g.det_coe
    rwa [Matrix.det_fin_two] at h
  have hw : (wMat : SL(2, R))⁻¹ = wMat * wMat * wMat := by
    apply inv_eq_of_mul_eq_one_right
    apply Subtype.ext
    change (((wMat * (wMat * wMat * wMat) : SL(2, R))) : Matrix (Fin 2) (Fin 2) R) = ((1 : SL(2, R)) : Matrix (Fin 2) (Fin 2) R)
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, coe_w,
      Matrix.mul_fin_two, Matrix.one_fin_two]
    simp
  refine ⟨?_, ?_, ?_, hw⟩
  · intro c hc
    have hu : (c : R) * ((c⁻¹ : Rˣ) : R) = 1 := by simp
    have hinv : ((-c⁻¹ : Rˣ) : R) = -((c⁻¹ : Rˣ) : R) := by simp
    have hinv2 : (((-c⁻¹ : Rˣ)⁻¹ : Rˣ) : R) = -(c : R) := by simp
    refine SL2_eq_of_entries_eq_matrix (p := g 0 0) (q := g 0 1) (r := g 1 0) (s := g 1 1) ?_ rfl rfl rfl rfl
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_n, coe_m, coe_w, Matrix.mul_fin_two, hinv, hinv2]
    generalize ((c⁻¹ : Rˣ) : R) = u at hu
    rw [hc] at hdet ⊢
    congr
    · linear_combination (g 0 0) * hu
    · linear_combination (g 0 0 * g 1 1 * u + g 0 1) * hu + u * hdet
    · ring
    · linear_combination (g 1 1) * hu
  · intro a ha
    have hu : (a : R) * ((a⁻¹ : Rˣ) : R) = 1 := by simp
    rw [hw]
    refine SL2_eq_of_entries_eq_matrix (p := g 0 0) (q := g 0 1) (r := g 1 0) (s := g 1 1) ?_ rfl rfl rfl rfl
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_n, coe_m, coe_w, Matrix.mul_fin_two]
    generalize ((a⁻¹ : Rˣ) : R) = u at hu
    rw [ha] at hdet ⊢
    congr
    · ring
    · linear_combination (g 0 1) * hu
    · linear_combination (g 1 0) * hu
    · linear_combination (g 1 0 * g 0 1 * u + g 1 1) * hu - u * hdet
  · intro a ha hc
    have hu : (a : R) * ((a⁻¹ : Rˣ) : R) = 1 := by simp
    refine SL2_eq_of_entries_eq_matrix (p := g 0 0) (q := g 0 1) (r := g 1 0) (s := g 1 1) ?_ rfl rfl rfl rfl
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_n, coe_m, Matrix.mul_fin_two]
    generalize ((a⁻¹ : Rˣ) : R) = u at hu
    rw [ha, hc] at hdet ⊢
    congr
    · ring
    · linear_combination (g 0 1) * hu
    · ring
    · linear_combination (g 1 1) * hu - u * hdet

end GlobalTheory.CompanionTheory.SW.Core.SL2BruhatDecomposition
