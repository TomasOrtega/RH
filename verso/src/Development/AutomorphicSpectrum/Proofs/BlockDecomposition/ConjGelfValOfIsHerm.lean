import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandSeriesShiftIdentity

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Matrix.map_apply, Formalism.REAL.Amat, Matrix.of_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem amat_map_conj {n : ℕ} (l : Fin n → ℂ) :
    (Formalism.REAL.Amat l).map (starRingEnd ℂ) = Formalism.REAL.Amat (fun a => conj (l a)) := by
  ext a b
  simp only [Matrix.map_apply, Formalism.REAL.Amat, Matrix.of_apply]
  split_ifs <;> simp

/- English proof (translation)
Establish `h : ((Formalism.REAL.Amat fun a => c a + ((n : ℂ) - 1) / 2) ^ m).map (starRingEnd ℂ) = (Formalism.REAL.Amat fun a => conj (c a) + ((n : ℂ) - 1) / 2) ^ m`. Rewrite using `[Matrix.map_pow, amat_map_conj]`. Use `congr 2`. Use function extensionality and compare the values at `a`. Simplify using `[map_ofNat]`.

Simplify using `only [GlobalTheory.Dec.gelfVal, map_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[← h]`. Both sides reduce to the same expression.
-/
theorem conj_gelfVal {n : ℕ} (c : Fin n → ℂ) (m : ℕ) :
    conj (GlobalTheory.Dec.gelfVal c m) = GlobalTheory.Dec.gelfVal (fun a => conj (c a)) m := by
  have h : ((Formalism.REAL.Amat fun a => c a + ((n : ℂ) - 1) / 2) ^ m).map (starRingEnd ℂ) =
      (Formalism.REAL.Amat fun a => conj (c a) + ((n : ℂ) - 1) / 2) ^ m := by
    rw [Matrix.map_pow, amat_map_conj]
    congr 2
    funext a
    simp [map_ofNat]
  simp only [GlobalTheory.Dec.gelfVal, map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← h]
  rfl

/- English proof (translation)
Use `Finset.prod_ne_zero_iff.2 fun a _ h => ?_` and prove the remaining obligations. Use `congrArg PowerSeries.constantCoeff h` as an intermediate fact. Simplify using `at this`.
-/
theorem prod_one_sub_ne_zero {n : ℕ} (l : Fin n → ℂ) :
    (∏ a, (1 - PowerSeries.C (l a) * PowerSeries.X) : PowerSeries ℂ) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun a _ h => ?_
  have := congrArg PowerSeries.constantCoeff h
  simp at this

/- English proof (translation)
Establish `h1` using `gser_mul_prod n (fun a => c (σ a))`. Establish `h2` using `gser_mul_prod n c`. Use `beta_reduce at h1`. Establish `e1 : (∏ a, (1 - PowerSeries.C (c (σ a) + ((n : ℂ) - 1) / 2) * PowerSeries.X) : PowerSeries ℂ) = ∏ a, (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2) * PowerSeries.X)` using `Equiv.prod_comp σ (fun a => (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2) * PowerSeries.X))`. Establish `e2 : (∏ a, (1 - PowerSeries.C (c (σ a) + ((n : ℂ) - 1) / 2 + 1) * PowerSeries.X) : PowerSeries ℂ) = ∏ a, (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2 + 1) * PowerSeries.X)` using `Equiv.prod_comp σ (fun a => (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2 + 1) * PowerSeries.X))`.

Rewrite `h1` using `[e1, e2]`. Establish `hP : (∏ a, (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2) * PowerSeries.X) : PowerSeries ℂ) ≠ 0` using `prod_one_sub_ne_zero _`. Establish `h3 : (1 - PowerSeries.X * gser (fun a => c (σ a))) = 1 - PowerSeries.X * gser c` using `mul_right_cancel₀ hP (h1.trans h2.symm)`. Establish `h4 : PowerSeries.X * gser (fun a => c (σ a)) = PowerSeries.X * gser c` using `sub_right_injective h3`. Conclude with `mul_left_cancel₀ PowerSeries.X_ne_zero h4`.
-/
theorem gser_comp_perm {n : ℕ} (c : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) :
    gser (fun a => c (σ a)) = gser c := by
  have h1 := gser_mul_prod n (fun a => c (σ a))
  have h2 := gser_mul_prod n c
  beta_reduce at h1
  have e1 : (∏ a, (1 - PowerSeries.C (c (σ a) + ((n : ℂ) - 1) / 2) * PowerSeries.X) : PowerSeries ℂ) =
      ∏ a, (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2) * PowerSeries.X) :=
    Equiv.prod_comp σ (fun a => (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2) * PowerSeries.X))
  have e2 : (∏ a, (1 - PowerSeries.C (c (σ a) + ((n : ℂ) - 1) / 2 + 1) * PowerSeries.X) : PowerSeries ℂ) =
      ∏ a, (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2 + 1) * PowerSeries.X) :=
    Equiv.prod_comp σ (fun a => (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2 + 1) * PowerSeries.X))
  rw [e1, e2] at h1
  have hP : (∏ a, (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2) * PowerSeries.X) : PowerSeries ℂ) ≠ 0 :=
    prod_one_sub_ne_zero _
  have h3 : (1 - PowerSeries.X * gser (fun a => c (σ a))) = 1 - PowerSeries.X * gser c :=
    mul_right_cancel₀ hP (h1.trans h2.symm)
  have h4 : PowerSeries.X * gser (fun a => c (σ a)) = PowerSeries.X * gser c := sub_right_injective h3
  exact mul_left_cancel₀ PowerSeries.X_ne_zero h4

/- English proof (translation)
Establish `h` using `congrArg (PowerSeries.coeff m) (gser_comp_perm c σ)`. Simplify `h` using `[gser]`.
-/
theorem gelfVal_comp_perm {n : ℕ} (c : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) (m : ℕ) :
    GlobalTheory.Dec.gelfVal (fun a => c (σ a)) m = GlobalTheory.Dec.gelfVal c m := by
  have h := congrArg (PowerSeries.coeff m) (gser_comp_perm c σ)
  simpa [gser] using h

/- English proof (translation)
Introduce `n χ hχ s m`. Take `⟨σ, hσ⟩` from `hχ`. Rewrite using `[conj_gelfVal]`. Consider the cases of `s`. Simplify using `only [Bool.not_false]`.

Rewrite using `[← gelfVal_comp_perm (fun a => conj (χ false a)) σ]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Simplify using `[hσ a]`. Simplify using `only [Bool.not_true]`.

Rewrite using `[← gelfVal_comp_perm (fun a => -χ false a) σ]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Simplify using `[hσ a]`.
-/
theorem conj_gelfVal_of_isHerm : ∀ (n : ℕ) (χ : Inf n), IsHerm χ → ∀ (s : Bool) (m : ℕ),
    conj (GlobalTheory.Dec.gelfVal (χ s) m) = GlobalTheory.Dec.gelfVal (fun a => - χ (!s) a) m := by
  intro n χ hχ s m
  obtain ⟨σ, hσ⟩ := hχ
  rw [conj_gelfVal]
  cases s
  · simp only [Bool.not_false]
    rw [← gelfVal_comp_perm (fun a => conj (χ false a)) σ]
    congr 1
    funext a
    simp [hσ a]
  · simp only [Bool.not_true]
    rw [← gelfVal_comp_perm (fun a => -χ false a) σ]
    congr 1
    funext a
    simp [hσ a]

end GlobalTheory.CompanionTheory.WaveMult
