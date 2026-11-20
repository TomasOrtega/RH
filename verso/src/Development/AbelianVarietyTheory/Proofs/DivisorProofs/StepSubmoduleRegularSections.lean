import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepInclStepProj
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.FlagChi Matrix

set_option autoImplicit false

namespace GlobalTheory.FlagChi

/- English proof (translation)
The claim follows from `RingHom.mem_range.symm`.
-/
theorem regAt_iff_mem_range {Z : Scheme.{0}} [IsIntegral Z] (x : Z) (f : Z.functionField) :
    RegAt x f ↔ f ∈ (algebraMap (Z.presheaf.stalk x) Z.functionField).range :=
  RingHom.mem_range.symm

/- English proof (translation)
Use `choose m hm using hM`. Establish `e : M = (Matrix.of m).map (algebraMap (Z.presheaf.stalk x) Z.functionField)`. Use extensionality with `a b`. Conclude with `(hm a b).symm`. Establish `hadj : ∀ a b, RegAt x (M.adjugate a b)`.

Introduce `a b`. Rewrite using `[e, ← RingHom.mapMatrix_apply, ← RingHom.map_adjugate]`. Conclude with `⟨_, rfl⟩`. Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]`. Conclude with `hd.inv.regAt.mul (hadj i j)`.
-/
theorem regAt_inv_entry {Z : Scheme.{0}} [IsIntegral Z] {N : ℕ} (x : Z)
    (M : Matrix (Fin N) (Fin N) Z.functionField) (hM : ∀ a b, RegAt x (M a b))
    (hd : UnitAt x M.det) (i j : Fin N) : RegAt x (M⁻¹ i j) := by
  choose m hm using hM
  have e : M = (Matrix.of m).map (algebraMap (Z.presheaf.stalk x) Z.functionField) := by
    ext a b; exact (hm a b).symm
  have hadj : ∀ a b, RegAt x (M.adjugate a b) := by
    intro a b
    rw [e, ← RingHom.mapMatrix_apply, ← RingHom.map_adjugate]
    exact ⟨_, rfl⟩
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact hd.inv.regAt.mul (hadj i j)

/- English proof (translation)
Introduce `Z _ N A l L r _ hB x v hv hreg c hc`. Take `⟨B, hBt, hMreg, hMdet, hBl⟩` from `hB x`. Use `set M := A * B with hMdef`. Establish `hdetM : M.det ≠ 0` using `hMdet.ne_zero`. Establish `hdetA : A.det ≠ 0` using `fun h => hdetM (by rw [hMdef, Matrix.det_mul, h, zero_mul])`.

Establish `hdetB : B.det ≠ 0` using `fun h => hdetM (by rw [hMdef, Matrix.det_mul, h, mul_zero])`. Use `haveI : Invertible B := Matrix.invertibleOfIsUnitDet B (isUnit_iff_ne_zero.2 hdetB)`. Use `haveI : Invertible A := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.2 hdetA)`. Use `set w := M⁻¹ *ᵥ v with hw`. Use `set a := A⁻¹ *ᵥ v with ha`.

Establish `hMinv : M⁻¹ = B⁻¹ * A⁻¹` using `Matrix.mul_inv_rev A B`. Establish `haw : a = B *ᵥ w`. Rewrite using `[hw, hMinv, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.one_mul]`. Establish `hwa : w = B⁻¹ *ᵥ a` using `by rw [hw, hMinv, ha, Matrix.mulVec_mulVec]`. Establish `hwreg : ∀ k, RegAt x (w k)`.

Introduce `k`. Rewrite using `[hw, regAt_iff_mem_range]`. Simplify using `only [Matrix.mulVec, dotProduct]`. Use `Subring.sum_mem _ fun j _ => Subring.mul_mem _ ?_ ?_` and prove the remaining obligations. Apply the tactic sequence `exact (regAt_iff_mem_range _ _).1 (regAt_inv_entry x M hMreg hMdet k j)`.

Conclude with `(regAt_iff_mem_range _ _).1 (hreg j)`. Establish `hBinv : (B⁻¹).BlockTriangular id` using `Matrix.blockTriangular_inv_of_blockTriangular hBt`. Establish `hwz : ∀ k : Fin N, l < k → w k = 0`. Introduce `k hk`. Rewrite using `[hwa]`.

Simplify using `only [Matrix.mulVec, dotProduct]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Break down `lt_or_ge j k with hjk | hjk` into its components or cases. Rewrite using `[hBinv hjk, zero_mul]`. Establish `: (l : ℕ) + 1 ≤ (j : ℕ)`.

Use `lt_of_lt_of_le hk hjk` as an intermediate fact. Conclude with `this`. Rewrite using `[show a j = 0 from hv j this, mul_zero]`. Establish `hal : a l = B l l * w l`. Rewrite using `[haw]`.

Simplify using `only [Matrix.mulVec, dotProduct]`. Use `Finset.sum_eq_single l (fun k _ hkl => ?_) (fun h => (h (Finset.mem_univ _)).elim)` and prove the remaining obligations. Break down `lt_or_gt_of_ne hkl with hk | hk` into its components or cases. Rewrite using `[hBt hk, zero_mul]`. Rewrite using `[hwz k hk, mul_zero]`.

Use `show RegAt x (a l * r c)`. Rewrite using `[hal, mul_right_comm]`. Conclude with `(hBl c hc).regAt.mul (hwreg l)`.
-/
theorem coord_regular :
    ∀ (Z : Scheme.{0}) [IsIntegral Z] (N : ℕ) (A : Matrix (Fin N) (Fin N) Z.functionField) (l : Fin N) (L : LB Z) (r : L.ι → Z.functionFieldˣ), IsUnit A.det → (∀ z : Z, ∃ B : Matrix (Fin N) (Fin N) Z.functionField, B.BlockTriangular id ∧ (∀ a b, RegAt z ((A * B) a b)) ∧ UnitAt z (A * B).det ∧ ∀ c, z ∈ L.U c → UnitAt z (B l l * r c)) → ∀ (x : Z) (v : Fin N → Z.functionField), v ∈ stepSub A⁻¹ ((l : ℕ) + 1) → (∀ a, RegAt x (v a)) → ∀ c, x ∈ L.U c → RegAt x ((A⁻¹ *ᵥ v) l * r c) := by
  intro Z _ N A l L r _ hB x v hv hreg c hc
  obtain ⟨B, hBt, hMreg, hMdet, hBl⟩ := hB x
  set M := A * B with hMdef
  have hdetM : M.det ≠ 0 := hMdet.ne_zero
  have hdetA : A.det ≠ 0 := fun h => hdetM (by rw [hMdef, Matrix.det_mul, h, zero_mul])
  have hdetB : B.det ≠ 0 := fun h => hdetM (by rw [hMdef, Matrix.det_mul, h, mul_zero])
  haveI : Invertible B := Matrix.invertibleOfIsUnitDet B (isUnit_iff_ne_zero.2 hdetB)
  haveI : Invertible A := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.2 hdetA)
  set w := M⁻¹ *ᵥ v with hw
  set a := A⁻¹ *ᵥ v with ha
  have hMinv : M⁻¹ = B⁻¹ * A⁻¹ := Matrix.mul_inv_rev A B
  have haw : a = B *ᵥ w := by
    rw [hw, hMinv, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_inv_of_invertible,
      Matrix.one_mul]
  have hwa : w = B⁻¹ *ᵥ a := by rw [hw, hMinv, ha, Matrix.mulVec_mulVec]
  have hwreg : ∀ k, RegAt x (w k) := by
    intro k
    rw [hw, regAt_iff_mem_range]
    simp only [Matrix.mulVec, dotProduct]
    refine Subring.sum_mem _ fun j _ => Subring.mul_mem _ ?_ ?_
    · exact (regAt_iff_mem_range _ _).1 (regAt_inv_entry x M hMreg hMdet k j)
    · exact (regAt_iff_mem_range _ _).1 (hreg j)
  have hBinv : (B⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hBt
  have hwz : ∀ k : Fin N, l < k → w k = 0 := by
    intro k hk
    rw [hwa]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases lt_or_ge j k with hjk | hjk
    · rw [hBinv hjk, zero_mul]
    · have : (l : ℕ) + 1 ≤ (j : ℕ) := by
        have := lt_of_lt_of_le hk hjk; exact this
      rw [show a j = 0 from hv j this, mul_zero]
  have hal : a l = B l l * w l := by
    rw [haw]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_single l (fun k _ hkl => ?_) (fun h => (h (Finset.mem_univ _)).elim)
    rcases lt_or_gt_of_ne hkl with hk | hk
    · rw [hBt hk, zero_mul]
    · rw [hwz k hk, mul_zero]
  show RegAt x (a l * r c)
  rw [hal, mul_right_comm]
  exact (hBl c hc).regAt.mul (hwreg l)

end GlobalTheory.FlagChi
