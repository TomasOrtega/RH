import Mathlib
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore

open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu

namespace GlobalTheory.CompanionTheory.BmuDsAd

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
Establish `hd : IsUnit y.det` using `(Matrix.isUnit_iff_isUnit_det y).1 hy`. Establish `h1 : (t : ℂ) • (y⁻¹ * X * y) = y⁻¹ * ((t : ℂ) • X) * y`. Simplify using `[Matrix.mul_smul, Matrix.smul_mul]`. Unfold `ex`. Rewrite using `[h1, Matrix.exp_conj' _ _ hy, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]`.
-/
theorem ex_mul_eq {y : Mat n} (hy : IsUnit y) (X : Mat n) (t : ℝ) :
    ex X t * y = y * ex (y⁻¹ * X * y) t := by
  have hd : IsUnit y.det := (Matrix.isUnit_iff_isUnit_det y).1 hy
  have h1 : (t : ℂ) • (y⁻¹ * X * y) = y⁻¹ * ((t : ℂ) • X) * y := by
    simp [Matrix.mul_smul, Matrix.smul_mul]
  unfold ex
  rw [h1, Matrix.exp_conj' _ _ hy, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd,
    Matrix.one_mul]

/- English proof (translation)
Establish `hd : IsUnit y.det` using `(Matrix.isUnit_iff_isUnit_det y).1 hy`. Establish `h1 : y * y⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hd`. Establish `h2 : Hm * y⁻¹ = yᴴ * Hm`. Combine the equalities or inequalities in the displayed calculation. Establish `h3 : y⁻¹ᴴ * Hm = Hm * y`.

Combine the equalities or inequalities in the displayed calculation. Unfold `Lie at hX ⊢`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = yᴴ * (Xᴴ * Hm + Hm * X) * y := by`.

Rewrite using `[h2, h3]`. Simplify using `only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]`. Use `_ = 0 := by rw [hX]; simp`.
-/
theorem lie_conj {Hm y X : Mat n} (hy : IsUnit y) (hyH : yᴴ * Hm * y = Hm) (hX : Lie Hm X) :
    Lie Hm (y⁻¹ * X * y) := by
  have hd : IsUnit y.det := (Matrix.isUnit_iff_isUnit_det y).1 hy
  have h1 : y * y⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have h2 : Hm * y⁻¹ = yᴴ * Hm := by
    calc Hm * y⁻¹ = yᴴ * Hm * y * y⁻¹ := by rw [hyH]
      _ = yᴴ * Hm := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have h3 : y⁻¹ᴴ * Hm = Hm * y := by
    calc y⁻¹ᴴ * Hm = y⁻¹ᴴ * (yᴴ * Hm * y) := by rw [hyH]
      _ = (y * y⁻¹)ᴴ * (Hm * y) := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Hm * y := by rw [h1]; simp
  unfold Lie at hX ⊢
  calc (y⁻¹ * X * y)ᴴ * Hm + Hm * (y⁻¹ * X * y)
      = yᴴ * Xᴴ * (y⁻¹ᴴ * Hm) + (Hm * y⁻¹) * X * y := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = yᴴ * (Xᴴ * Hm + Hm * X) * y := by
        rw [h2, h3]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX]; simp

/- English proof (translation)
Introduce `n Hm H _ _ _ σ hσ y hy W hW`. Establish `hyu : IsUnit y`. Establish `hyH : yᴴ * Hm * y = Hm` using `hy`. Establish `h1 : (Hm * yᴴ * Hm) * y = 1`. Rewrite using `[Matrix.mul_assoc Hm, Matrix.mul_assoc Hm, hyH, hσ.sq]`.

Conclude with `(Matrix.isUnit_iff_isUnit_det y).2 (Matrix.isUnit_det_of_left_inverse h1)`. Establish `hyH : yᴴ * Hm * y = Hm` using `hy`. Establish `hL : ∀ W, LieWd Hm W → LieWd Hm (W.map fun X => y⁻¹ * X * y)`. Introduce `W hW Z hZ`. Take `⟨X, hX, rfl⟩` from `List.mem_map.1 hZ`.

Conclude with `lie_conj hyu hyH (hW X hX)`. Use `⟨hL W hW, fun u hu => ?_⟩` and prove the remaining obligations. Proceed by induction on `W with`. Consider the case `nil => rfl`. Consider the case `cons X W ih`.

Establish `hW' : LieWd Hm W` using `fun Y hY => hW Y (List.mem_cons_of_mem _ hY)`. Establish `hX : Lie Hm X` using `hW X List.mem_cons_self`. Establish `hX' : ∀ t, ex (y⁻¹ * X * y) t ∈ UH Hm` using `fun t => ex_mem_of_lie (lie_conj hyu hyH hX) t`. Establish `hs : IsSm (UH Hm) σ (dsW σ (W.map fun X => y⁻¹ * X * y) u)` using `hu.dsW hσ.rep fun Z hZ t => ex_mem_of_lie (hL W hW' Z hZ) t`. Rewrite using `[List.map_cons, dsW_cons, dsW_cons, ih hW', apply_ds hσ.rep hX' hy (hs.differentiableAt hσ.rep hX')]`.

Unfold `ds`. Use `congr 1`. Use extensionality with `t`. Rewrite using `[← hσ.rep.apply_mul (ex_mem_of_lie hX t) hy, ex_mul_eq hyu]`.
-/
theorem dsAd : DsAd := by
  intro n Hm H _ _ _ σ hσ y hy W hW
  have hyu : IsUnit y := by
    have hyH : yᴴ * Hm * y = Hm := hy
    have h1 : (Hm * yᴴ * Hm) * y = 1 := by
      rw [Matrix.mul_assoc Hm, Matrix.mul_assoc Hm, hyH, hσ.sq]
    exact (Matrix.isUnit_iff_isUnit_det y).2 (Matrix.isUnit_det_of_left_inverse h1)
  have hyH : yᴴ * Hm * y = Hm := hy
  have hL : ∀ W, LieWd Hm W → LieWd Hm (W.map fun X => y⁻¹ * X * y) := by
    intro W hW Z hZ
    obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hZ
    exact lie_conj hyu hyH (hW X hX)
  refine ⟨hL W hW, fun u hu => ?_⟩
  induction W with
  | nil => rfl
  | cons X W ih =>
    have hW' : LieWd Hm W := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
    have hX : Lie Hm X := hW X List.mem_cons_self
    have hX' : ∀ t, ex (y⁻¹ * X * y) t ∈ UH Hm := fun t => ex_mem_of_lie (lie_conj hyu hyH hX) t
    have hs : IsSm (UH Hm) σ (dsW σ (W.map fun X => y⁻¹ * X * y) u) :=
      hu.dsW hσ.rep fun Z hZ t => ex_mem_of_lie (hL W hW' Z hZ) t
    rw [List.map_cons, dsW_cons, dsW_cons, ih hW',
      apply_ds hσ.rep hX' hy (hs.differentiableAt hσ.rep hX')]
    unfold ds
    congr 1
    ext t
    rw [← hσ.rep.apply_mul (ex_mem_of_lie hX t) hy, ex_mul_eq hyu]

end GlobalTheory.CompanionTheory.BmuDsAd
