import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.SchurJT

noncomputable section

open Finset Matrix

namespace PositivityTheory.RgJS

namespace SkewJacobiTrudiStaircase

variable {m : ℕ}

def eM (α : Fin m → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i k => (-1 : ℂ) ^ (k.rev : ℕ) * eEx α i (k.rev : ℕ)

def hM (α : Fin m → ℂ) (μ : Fin m → ℕ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun k j => hZ ((μ j : ℤ) - (k.rev : ℕ)) α

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.of_apply, hE m α i (μ j), Matrix.mul_apply]`. Simplify using `only [eM, hM, Matrix.of_apply]`. Rewrite using `[← Fin.sum_univ_eq_sum_range (fun r => (-1 : ℂ) ^ r * eEx α i r * hZ ((μ j : ℤ) - (r : ℤ)) α)]`. Conclude with `(Fintype.sum_equiv Fin.revPerm _ _ (fun k => rfl)).symm`.
-/
theorem factor (hE : ERel) (α : Fin m → ℂ) (μ : Fin m → ℕ) :
    (Matrix.of fun i j => α i ^ μ j) = eM α * hM α μ := by
  ext i j
  rw [Matrix.of_apply, hE m α i (μ j), Matrix.mul_apply]
  simp only [eM, hM, Matrix.of_apply]
  rw [← Fin.sum_univ_eq_sum_range (fun r => (-1 : ℂ) ^ r * eEx α i r * hZ ((μ j : ℤ) - (r : ℤ)) α)]
  exact (Fintype.sum_equiv Fin.revPerm _ _ (fun k => rfl)).symm

/- English proof (translation)
Simplify using `[hZ, hz]`.
-/
theorem hZ_neg (α : Fin m → ℂ) {z : ℤ} (hz : z < 0) : hZ z α = 0 := by
  simp [hZ, hz]

/- English proof (translation)
Simplify using `only [hZ, hN, lt_irrefl, if_false, Int.toNat_zero]`. Rewrite using `[Nat.antidiagonalTuple_zero_right]`. Simplify using the standard rewrite rules.
-/
theorem hZ_zero (α : Fin m → ℂ) : hZ 0 α = 1 := by
  simp only [hZ, hN, lt_irrefl, if_false, Int.toNat_zero]
  rw [Nat.antidiagonalTuple_zero_right]
  simp

/- English proof (translation)
Rewrite using `[Matrix.det_of_lowerTriangular]`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `k _`. Simplify using `only [hM, Matrix.of_apply]`. Establish `hk : ((stair m k : ℕ) : ℤ) - ((k.rev : ℕ) : ℤ) = 0`.

Simplify using `only [stair, Fin.val_rev]`. Use `k.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[hk]`. Conclude with `hZ_zero α`.

Introduce `i j hij`. Simplify using `only [hM, Matrix.of_apply]`. Apply `hZ_neg` to reduce the goal to its premises. Establish `hlt : (i : ℕ) < j` using `hij`. Simplify using `only [stair, Fin.val_rev]`.

Use `j.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem det_hM_stair (α : Fin m → ℂ) : (hM α (stair m)).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · apply Finset.prod_eq_one
    intro k _
    simp only [hM, Matrix.of_apply]
    have hk : ((stair m k : ℕ) : ℤ) - ((k.rev : ℕ) : ℤ) = 0 := by
      simp only [stair, Fin.val_rev]
      have := k.isLt
      omega
    rw [hk]
    exact hZ_zero α
  · intro i j hij
    simp only [hM, Matrix.of_apply]
    apply hZ_neg
    have hlt : (i : ℕ) < j := hij
    simp only [stair, Fin.val_rev]
    have := j.isLt
    omega

/- English proof (translation)
Use extensionality with `k j`. Simplify using `only [hM, Matrix.of_apply, Pi.add_apply, stair, Fin.val_rev]`. Use `congr 1`. Establish `hj` using `j.isLt`. Establish `hk` using `k.isLt`.

Use `push_cast`. Use linear arithmetic over natural numbers and integers.
-/
theorem hM_add_stair (α : Fin m → ℂ) (l : Fin m → ℕ) :
    hM α (l + stair m) = Matrix.of fun i j : Fin m => hZ ((l j : ℤ) - j + i) α := by
  ext k j
  simp only [hM, Matrix.of_apply, Pi.add_apply, stair, Fin.val_rev]
  congr 1
  have hj := j.isLt
  have hk := k.isLt
  push_cast
  omega

end SkewJacobiTrudiStaircase

open SkewJacobiTrudiStaircase in
/- English proof (translation)
Introduce `hE m α l`. Unfold `altN jt`. Rewrite using `[factor hE α, factor hE α, det_mul, det_mul, det_hM_stair, mul_one, hM_add_stair]`.
-/
theorem alternating_jacobi_trudi_of_relation : ERel → AltJT := by
  intro hE m α l
  unfold altN jt
  rw [factor hE α, factor hE α, det_mul, det_mul, det_hM_stair, mul_one, hM_add_stair]

end PositivityTheory.RgJS
