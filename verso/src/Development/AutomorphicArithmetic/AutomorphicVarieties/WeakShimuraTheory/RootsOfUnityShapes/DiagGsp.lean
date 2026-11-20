import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.LowAdj

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Use `show adj _ * _ = e • 1`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `[adj_apply, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply, sgn, Fin.rev]`.
-/
private theorem diag_gsp {R : Type} [CommRing R] (e : R) :
    IsGSp e (Matrix.diagonal ![1, 1, e, e] : M4 R) := by
  show adj _ * _ = e • 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adj_apply, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply, sgn, Fin.rev]

/- English proof (translation)
Introduce `R _ ν X n₀ hν hX hn₀ h0 h1`. Take `⟨v, rfl⟩` from `hν`. Use `set D : M4 R := Matrix.diagonal ![1, 1, ((v⁻¹ : Rˣ) : R), ((v⁻¹ : Rˣ) : R)] with hD`. Use `set D' : M4 R := Matrix.diagonal ![1, 1, (v : R), (v : R)] with hD'`. Establish `hDD : D * D' = 1`.

Rewrite using `[hD, hD', Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp`. Establish `hu : IsGSp 1 (X * n₀ * D)`.

Establish `h` using `(grp R).2.2.2.2.2.2.2.1 _ _ _ _ ((grp R).2.2.2.2.2.2.2.1 _ _ _ _ hX hn₀.1) (diag_gsp ((v⁻¹ : Rˣ) : R))`. Simplify using `using h`. Establish `hcol : ∀ i, (X * n₀ * D) i 0 = (X * n₀) i 0 ∧ (X * n₀ * D) i 1 = (X * n₀) i 1`. Introduce `i`. Simplify using `[hD, Matrix.mul_diagonal]`.

Take `⟨n, b, hn, -, hb, hfac⟩` from `Lab.luSp R _ hu (by rw [(hcol 0).1]; exact h0) (by rw [(hcol 0).1, (hcol 1).2, (hcol 0).2, (hcol 1).1]; exact h1)`. Use `⟨n, hn, ?_⟩` and prove the remaining obligations. Establish `hnn : adj n * n = 1`. Establish `h` using `hn.1`. Unfold `IsGSp at h`.

Rewrite using `[h, one_smul]`. Establish `key : adj n * X * n₀ = b * D'`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc, hDD, Matrix.mul_one]`. Use `_ = adj n * (n * b) * D' := by rw [hfac]`.

Use `_ = b * D' := by rw [← Matrix.mul_assoc (adj n), hnn, Matrix.one_mul]`. Rewrite using `[key]`. Introduce `i j hij`. Simplify using `[hD', Matrix.mul_diagonal, hb i j hij]`.
-/
theorem UpperTheory.V.Ws.Rq.luG :
    ∀ (R : Type) [CommRing R] (ν : R) (X n₀ : M4 R), IsUnit ν → IsGSp ν X → IsLow n₀ → IsUnit ((X * n₀) 0 0) →
      IsUnit ((X * n₀) 0 0 * (X * n₀) 1 1 - (X * n₀) 0 1 * (X * n₀) 1 0) → ∃ n : M4 R, IsLow n ∧ IsUp (adj n * X * n₀) := by
  intro R _ ν X n₀ hν hX hn₀ h0 h1
  obtain ⟨v, rfl⟩ := hν
  set D : M4 R := Matrix.diagonal ![1, 1, ((v⁻¹ : Rˣ) : R), ((v⁻¹ : Rˣ) : R)] with hD
  set D' : M4 R := Matrix.diagonal ![1, 1, (v : R), (v : R)] with hD'
  have hDD : D * D' = 1 := by
    rw [hD, hD', Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  have hu : IsGSp 1 (X * n₀ * D) := by
    have h := (grp R).2.2.2.2.2.2.2.1 _ _ _ _ ((grp R).2.2.2.2.2.2.2.1 _ _ _ _ hX hn₀.1)
      (diag_gsp ((v⁻¹ : Rˣ) : R))
    simpa using h
  have hcol : ∀ i, (X * n₀ * D) i 0 = (X * n₀) i 0 ∧ (X * n₀ * D) i 1 = (X * n₀) i 1 := by
    intro i
    simp [hD, Matrix.mul_diagonal]
  obtain ⟨n, b, hn, -, hb, hfac⟩ := Lab.luSp R _ hu (by rw [(hcol 0).1]; exact h0)
    (by rw [(hcol 0).1, (hcol 1).2, (hcol 0).2, (hcol 1).1]; exact h1)
  refine ⟨n, hn, ?_⟩
  have hnn : adj n * n = 1 := by
    have h := hn.1
    unfold IsGSp at h
    rw [h, one_smul]
  have key : adj n * X * n₀ = b * D' := by
    calc adj n * X * n₀ = adj n * (X * n₀ * D) * D' := by
          simp only [Matrix.mul_assoc, hDD, Matrix.mul_one]
      _ = adj n * (n * b) * D' := by rw [hfac]
      _ = b * D' := by rw [← Matrix.mul_assoc (adj n), hnn, Matrix.one_mul]
  rw [key]
  intro i j hij
  simp [hD', Matrix.mul_diagonal, hb i j hij]
