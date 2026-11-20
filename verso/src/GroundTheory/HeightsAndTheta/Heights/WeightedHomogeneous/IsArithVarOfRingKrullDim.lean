import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

/- English proof (translation)
Assemble the required witnesses or components as `⟨inferInstance, P.isMultiProjPrime, P.isHorizontal, hdim⟩`.
-/
theorem ArithVariety.isArithVar_of_ringKrullDim {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {n : ι → ℕ} (P : ArithVariety n) {D : ℕ}
    (hdim : ringKrullDim P.CoordRing = ((D + 1 + Fintype.card ι : ℕ) : WithBot ℕ∞)) :
    Geo.IsArithVar (ι := blockIdx n) P.ideal (D + 1) :=
  ⟨inferInstance, P.isMultiProjPrime, P.isHorizontal, hdim⟩

/- English proof (translation)
Introduce `hDeg ι _ _ _ n P D hdim L hL`. Establish `hP : Geo.IsArithVar (ι` using `blockIdx n) P.ideal (D + 1) := P.isArithVar_of_ringKrullDim hdim`. Establish `hfin` using `Geo.divSupp_finite (ι := blockIdx n) P.ideal (C ((2 : ℕ) : ℤ))`. Rewrite using `[hDeg ι (blockIdx n) P.ideal D L 2 hP hL Nat.prime_two, hG ι n P D hdim (fun j ↦ (L j).a) 2]`. Establish `hcast` using `(Int.castAddHom ℝ).map_finsum_mem (fun V ↦ (Geo.multAt (ι := blockIdx n) (P.ideal ⊔ Ideal.span {C ((2 : ℕ) : ℤ)}) V : ℤ) * Geo.geoNum (ι := blockIdx n) D V (fun j ↦ (L j).a)) hfin`.

Simplify using `only [Int.coe_castAddHom, Int.cast_mul, Int.cast_natCast] at hcast`. Conclude with `hcast.symm`.
-/
theorem FibrePoints.proof (hG : GeometricArithmeticNumbers.Statement) : FibrePoints.Statement := by
  intro hDeg ι _ _ _ n P D hdim L hL
  have hP : Geo.IsArithVar (ι := blockIdx n) P.ideal (D + 1) := P.isArithVar_of_ringKrullDim hdim
  have hfin := Geo.divSupp_finite (ι := blockIdx n) P.ideal (C ((2 : ℕ) : ℤ))
  rw [hDeg ι (blockIdx n) P.ideal D L 2 hP hL Nat.prime_two,
    hG ι n P D hdim (fun j ↦ (L j).a) 2]
  have hcast := (Int.castAddHom ℝ).map_finsum_mem
    (fun V ↦ (Geo.multAt (ι := blockIdx n) (P.ideal ⊔ Ideal.span {C ((2 : ℕ) : ℤ)}) V : ℤ) *
      Geo.geoNum (ι := blockIdx n) D V (fun j ↦ (L j).a)) hfin
  simp only [Int.coe_castAddHom, Int.cast_mul, Int.cast_natCast] at hcast
  exact hcast.symm

end GroundTheory.Heights₂.Heights
