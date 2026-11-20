import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StLocB
import GroundTheory.AutomorphicForms.MacdonaldFormula
import GroundTheory.AutomorphicForms.Cartan

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

/- English proof (translation)
Unfold `rhoPair`. Use `Fintype.sum_equiv Fin.revPerm _ _ (fun i => ?_)` and prove the remaining obligations. Simplify using `only [Fin.revPerm_apply, Fin.val_rev]`. Rewrite using `[Nat.cast_sub (by omega : (i : ℕ) + 1 ≤ n)]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem rhoPair_dual {n : ℕ} (l : Fin n → ℤ) :
    rhoPair (fun i => -l (Fin.rev i)) = rhoPair l := by
  unfold rhoPair
  refine Fintype.sum_equiv Fin.revPerm _ _ (fun i => ?_)
  simp only [Fin.revPerm_apply, Fin.val_rev]
  rw [Nat.cast_sub (by omega : (i : ℕ) + 1 ≤ n)]
  push_cast
  ring

/- English proof (translation)
Unfold `vPoly`. Simplify using `[map_prod, map_div₀]`.
-/
private theorem conj_vPoly (n : ℕ) (t : ℝ) :
    (starRingEnd ℂ) (vPoly n (t : ℂ)) = vPoly n (t : ℂ) := by
  unfold vPoly
  simp [map_prod, map_div₀]

set_option maxHeartbeats 400000 in
/- English proof (translation)
Introduce `hR F _ _ _ _ n _ _ μ _`. Use `show ∀ z, _`. Introduce `z hinj hz g`. Take `⟨l, hl, k₁, hk₁, k₂, hk₂, rfl⟩` from `Cartan.exists_eq_mul_diagPow_mul F n g`. Establish `htp : Cartan.diagPow F n l = Iwasawa.torusPow F n l`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Cartan.coe_diagPow, Iwasawa.coe_torusPow]`. Establish `hl' : Antitone (fun i : Fin n => -l (Fin.rev i))`. Introduce `i j hij`. Use `show -l (Fin.rev j) ≤ -l (Fin.rev i)`.

Conclude with `neg_le_neg (hl (Fin.rev_le_rev.mpr hij))`. Establish `hinv : (k₁ * Cartan.diagPow F n l * k₂)⁻¹ = k₂⁻¹ * Iwasawa.torusPow F n (-l) * k₁⁻¹`. Rewrite using `[Iwasawa.torusPow_neg, ← htp]`. Use `group`. Establish `hcomp : Iwasawa.torusPow F n (fun i : Fin n => -l (Fin.rev i)) = Iwasawa.torusPow F n ((-l) ∘ Fin.revPerm)` using `rfl`.

Establish `hZinv : zonalSpherical μ z (k₁ * Cartan.diagPow F n l * k₂)⁻¹ = zonalSpherical μ z (Iwasawa.torusPow F n (fun i : Fin n => -l (Fin.rev i)))`. Rewrite using `[hinv, zonalSpherical_mul_right z _ (inv_mem hk₁), zonalSpherical_mul_left z (inv_mem hk₂), hcomp, zonalSpherical_torusPow_comp]`. Establish `hZ : zonalSpherical μ z (k₁ * Cartan.diagPow F n l * k₂) = zonalSpherical μ z (Iwasawa.torusPow F n l)`. Rewrite using `[zonalSpherical_mul_right z _ hk₂, zonalSpherical_mul_left z hk₁, htp]`. Rewrite using `[hZinv, hZ]`.

Establish `hv : vPoly n ((qF F : ℂ))⁻¹ ≠ 0` using `vPoly_ne_zero injective_qInv_pow n`. Establish `hcast : (((qF F : ℝ)⁻¹ : ℝ) : ℂ) = ((qF F : ℂ))⁻¹` using `by simp`. Establish `m1` using `macdonald_formula_hlR (μ := μ) z hl'`. Establish `m2` using `macdonald_formula_hlR (μ := μ) z hl`. Establish `hc` using `hR n ((qF F : ℝ))⁻¹ l z hinj hz`.

Rewrite `hc` using `[hcast]`. Establish `hhm : halfModulus F (fun i : Fin n => -l (Fin.rev i)) = halfModulus F l`. Rewrite using `[halfModulus_eq, halfModulus_eq, rhoPair_dual]`. Establish `hhmr : (starRingEnd ℂ) (halfModulus F l) = halfModulus F l`. Rewrite using `[halfModulus_eq, map_zpow₀]`.

Simplify using `[sqrtQ]`. Establish `hvr : (starRingEnd ℂ) (vPoly n ((qF F : ℂ))⁻¹) = vPoly n ((qF F : ℂ))⁻¹`. Rewrite using `[← hcast]`. Conclude with `conj_vPoly n _`. Apply `mul_left_cancel₀ hv` to reduce the goal to its premises.

Rewrite using `[m1, hhm, hc]`. Establish `m2c` using `congrArg (starRingEnd ℂ) m2`. Rewrite `m2c` using `[map_mul, map_mul, hvr, hhmr]`. Rewrite using `[m2c]`.
-/
theorem UpperTheory.Gal.Gen.gammaConj_pf :
    UpperTheory.Gal.Gen.RConj → UpperTheory.Gal.Gen.GammaConj := by
  intro hR F _ _ _ _ n _ _ μ _
  show ∀ z, _
  intro z hinj hz g
  obtain ⟨l, hl, k₁, hk₁, k₂, hk₂, rfl⟩ := Cartan.exists_eq_mul_diagPow_mul F n g
  have htp : Cartan.diagPow F n l = Iwasawa.torusPow F n l := by
    apply Units.ext
    rw [Cartan.coe_diagPow, Iwasawa.coe_torusPow]
  have hl' : Antitone (fun i : Fin n => -l (Fin.rev i)) := by
    intro i j hij
    show -l (Fin.rev j) ≤ -l (Fin.rev i)
    exact neg_le_neg (hl (Fin.rev_le_rev.mpr hij))
  have hinv : (k₁ * Cartan.diagPow F n l * k₂)⁻¹ =
      k₂⁻¹ * Iwasawa.torusPow F n (-l) * k₁⁻¹ := by
    rw [Iwasawa.torusPow_neg, ← htp]
    group
  have hcomp : Iwasawa.torusPow F n (fun i : Fin n => -l (Fin.rev i)) =
      Iwasawa.torusPow F n ((-l) ∘ Fin.revPerm) := rfl
  have hZinv : zonalSpherical μ z (k₁ * Cartan.diagPow F n l * k₂)⁻¹ =
      zonalSpherical μ z (Iwasawa.torusPow F n (fun i : Fin n => -l (Fin.rev i))) := by
    rw [hinv, zonalSpherical_mul_right z _ (inv_mem hk₁), zonalSpherical_mul_left z (inv_mem hk₂),
      hcomp, zonalSpherical_torusPow_comp]
  have hZ : zonalSpherical μ z (k₁ * Cartan.diagPow F n l * k₂) =
      zonalSpherical μ z (Iwasawa.torusPow F n l) := by
    rw [zonalSpherical_mul_right z _ hk₂, zonalSpherical_mul_left z hk₁, htp]
  rw [hZinv, hZ]
  have hv : vPoly n ((qF F : ℂ))⁻¹ ≠ 0 := vPoly_ne_zero injective_qInv_pow n
  have hcast : (((qF F : ℝ)⁻¹ : ℝ) : ℂ) = ((qF F : ℂ))⁻¹ := by simp
  have m1 := macdonald_formula_hlR (μ := μ) z hl'
  have m2 := macdonald_formula_hlR (μ := μ) z hl
  have hc := hR n ((qF F : ℝ))⁻¹ l z hinj hz
  rw [hcast] at hc
  have hhm : halfModulus F (fun i : Fin n => -l (Fin.rev i)) = halfModulus F l := by
    rw [halfModulus_eq, halfModulus_eq, rhoPair_dual]
  have hhmr : (starRingEnd ℂ) (halfModulus F l) = halfModulus F l := by
    rw [halfModulus_eq, map_zpow₀]
    simp [sqrtQ]
  have hvr : (starRingEnd ℂ) (vPoly n ((qF F : ℂ))⁻¹) = vPoly n ((qF F : ℂ))⁻¹ := by
    rw [← hcast]
    exact conj_vPoly n _
  apply mul_left_cancel₀ hv
  rw [m1, hhm, hc]
  have m2c := congrArg (starRingEnd ℂ) m2
  rw [map_mul, map_mul, hvr, hhmr] at m2c
  rw [m2c]
