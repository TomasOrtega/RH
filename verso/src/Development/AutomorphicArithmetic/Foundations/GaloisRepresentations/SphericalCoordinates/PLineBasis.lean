import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LineBasis

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

/- English proof (translation)
Rewrite using `[Matrix.add_mulVec, Matrix.one_mulVec]`. Use `congr 1`. Use extensionality with `a`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply, Finset.univ_unique, Finset.sum_singleton, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem one_add_col_mul_rank_one_mulVec {n : ℕ} (u w v : Fin n → ℂ) :
    (1 + Matrix.replicateCol Unit u * Matrix.replicateRow Unit w) *ᵥ v = v + (w ⬝ᵥ v) • u := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec]
  congr 1
  ext a
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.replicateCol_apply,
    Matrix.replicateRow_apply, Finset.univ_unique, Finset.sum_singleton, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/- English proof (translation)
Simplify using `[hv, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, dotProduct_smul]`.
-/
private theorem hv_sub_smul_left {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (x y z : Fin n → ℂ) (a : ℂ) :
    hv M (x - a • y) z = hv M x z - a * hv M y z := by
  simp [hv, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, dotProduct_smul]

/- English proof (translation)
Introduce `n M z _ hpos`. Establish `hz : ∃ i, z i ≠ 0`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `: z = 0` using `funext h`.

Substitute `this` using the available equality. Simplify using `[hv] at hpos`. Take `⟨i₀, hi₀⟩` from `hz`. Establish `hφ : hv M z z ≠ 0`. Introduce `h`.

Rewrite `hpos` using `[h]`. Simplify using `at hpos`. Use `set e : Fin n → ℂ := Pi.single i₀ 1 with he`. Use `set c : Fin n → ℂ := fun j => if j = i₀ then 0 else hv M (Pi.single j 1) z / hv M z z with hc`. Use `⟨i₀, (1 + Matrix.replicateCol Unit (z - e) * Matrix.replicateRow Unit e) * (1 + Matrix.replicateCol Unit (-e) * Matrix.replicateRow Unit c), ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.det_mul, Matrix.det_one_add_replicateCol_mul_replicateRow, Matrix.det_one_add_replicateCol_mul_replicateRow]`. Establish `h1 : e ⬝ᵥ (z - e) = z i₀ - 1`. Simplify using `[he, dotProduct_sub]`. Establish `h2 : c ⬝ᵥ (-e) = 0`. Simplify using `[he, hc]`.

Rewrite using `[h1, h2]`. Simplify using `using hi₀`. Rewrite using `[← Matrix.mulVec_mulVec, one_add_col_mul_rank_one_mulVec, one_add_col_mul_rank_one_mulVec]`. Establish `h2 : c ⬝ᵥ e = 0` using `by simp [he, hc]`. Establish `h3 : e ⬝ᵥ e = 1` using `by simp [he]`.

Rewrite using `[h2]`. Simplify using `[h3, he]`. Introduce `i hi`. Rewrite using `[← Matrix.mulVec_mulVec, one_add_col_mul_rank_one_mulVec, one_add_col_mul_rank_one_mulVec]`. Establish `h2 : c ⬝ᵥ (Pi.single i 1 : Fin n → ℂ) = hv M (Pi.single i 1) z / hv M z z`.

Simplify using `[hc, hi]`. Establish `h3 : e ⬝ᵥ ((Pi.single i 1 : Fin n → ℂ) + (hv M (Pi.single i 1) z / hv M z z) • (-e)) = - (hv M (Pi.single i 1) z / hv M z z)`. Simplify using `[he, dotProduct_add, Pi.single_apply, hi]`. Rewrite using `[h2, h3]`. Establish `h4 : (Pi.single i 1 : Fin n → ℂ) + (hv M (Pi.single i 1) z / hv M z z) • (-e) + (-(hv M (Pi.single i 1) z / hv M z z)) • (z - e) = (Pi.single i 1 : Fin n → ℂ) - (hv M (Pi.single i 1) z / hv M z z) • z`.

Use extensionality with `a`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h4, hv_sub_smul_left]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.Gal.W2.lineBasis_of :
    UpperTheory.Gal.W2.LineBasis := by
  intro n M z _ hpos
  have hz : ∃ i, z i ≠ 0 := by
    by_contra h
    push_neg at h
    have : z = 0 := funext h
    subst this
    simp [hv] at hpos
  obtain ⟨i₀, hi₀⟩ := hz
  have hφ : hv M z z ≠ 0 := by
    intro h
    rw [h] at hpos
    simp at hpos
  set e : Fin n → ℂ := Pi.single i₀ 1 with he
  set c : Fin n → ℂ := fun j => if j = i₀ then 0 else hv M (Pi.single j 1) z / hv M z z with hc
  refine ⟨i₀, (1 + Matrix.replicateCol Unit (z - e) * Matrix.replicateRow Unit e) *
    (1 + Matrix.replicateCol Unit (-e) * Matrix.replicateRow Unit c), ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_one_add_replicateCol_mul_replicateRow,
      Matrix.det_one_add_replicateCol_mul_replicateRow]
    have h1 : e ⬝ᵥ (z - e) = z i₀ - 1 := by
      simp [he, dotProduct_sub]
    have h2 : c ⬝ᵥ (-e) = 0 := by
      simp [he, hc]
    rw [h1, h2]
    simpa using hi₀
  · rw [← Matrix.mulVec_mulVec, one_add_col_mul_rank_one_mulVec, one_add_col_mul_rank_one_mulVec]
    have h2 : c ⬝ᵥ e = 0 := by simp [he, hc]
    have h3 : e ⬝ᵥ e = 1 := by simp [he]
    rw [h2]
    simp [h3, he]
  · intro i hi
    rw [← Matrix.mulVec_mulVec, one_add_col_mul_rank_one_mulVec, one_add_col_mul_rank_one_mulVec]
    have h2 : c ⬝ᵥ (Pi.single i 1 : Fin n → ℂ) = hv M (Pi.single i 1) z / hv M z z := by
      simp [hc, hi]
    have h3 : e ⬝ᵥ ((Pi.single i 1 : Fin n → ℂ) + (hv M (Pi.single i 1) z / hv M z z) • (-e)) =
        - (hv M (Pi.single i 1) z / hv M z z) := by
      simp [he, dotProduct_add, Pi.single_apply, hi]
    rw [h2, h3]
    have h4 : (Pi.single i 1 : Fin n → ℂ) + (hv M (Pi.single i 1) z / hv M z z) • (-e) +
        (-(hv M (Pi.single i 1) z / hv M z z)) • (z - e) =
        (Pi.single i 1 : Fin n → ℂ) - (hv M (Pi.single i 1) z / hv M z z) • z := by
      ext a
      simp
      ring
    rw [h4, hv_sub_smul_left]
    field_simp
    ring
