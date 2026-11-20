import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegelTor

/- English proof (translation)
Introduce `g n F U hU`. Establish `hW : IsAffineOpen (U : F.X.Opens)` using `U.2`. Establish `: SmoothOfRelativeDimension (g * (g + 1) / 2) F.s` using `F.smooth`. Apply the tactic sequence `have : Smooth F.s := by first | exact SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s | exact F.smooth.smooth | infer_instance`. Take `⟨φ, hφ⟩` from `Spec.map_surjective (hW.fromSpec ≫ F.s)`.

Establish `h₁ : φ.hom.Flat` using `by rw [← Flat.SpecMap_iff, hφ]; infer_instance`. Use `letI : Algebra (cycAway n) Γ(F.X, U) := φ.hom.toAlgebra`. Establish `: Module.Flat (cycAway n) Γ(F.X, U)` using `h₁`. Use `charZero_of_inj_zero fun k hk => by_contra fun h0 => ?_` and prove the remaining obligations. Establish `hk' : ((k : cycAway n) : ℂ) ≠ 0` using `by simpa using h0`.

Establish `hne : (k : cycAway n) ≠ 0` using `fun h => hk' (by rw [h]; rfl)`. Use `(Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(F.X, U)) (r := (k : cycAway n)) (mem_nonZeroDivisors_of_ne_zero hne)).right_eq_zero_of_smul (x := 1) (by rw [Algebra.smul_def, _root_.mul_one, map_natCast]; exact hk)` as an intermediate fact. Conclude with `one_ne_zero this`.
-/
theorem sFam_charZero_affineOpen : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (U : F.X.affineOpens),
    Nontrivial Γ(F.X, U) → CharZero Γ(F.X, U) := by
  intro g n F U hU
  have hW : IsAffineOpen (U : F.X.Opens) := U.2
  have : SmoothOfRelativeDimension (g * (g + 1) / 2) F.s := F.smooth
  have : Smooth F.s := by first | exact SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s | exact F.smooth.smooth | infer_instance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hW.fromSpec ≫ F.s)
  have h₁ : φ.hom.Flat := by rw [← Flat.SpecMap_iff, hφ]; infer_instance
  letI : Algebra (cycAway n) Γ(F.X, U) := φ.hom.toAlgebra
  have : Module.Flat (cycAway n) Γ(F.X, U) := h₁
  refine charZero_of_inj_zero fun k hk => by_contra fun h0 => ?_
  have hk' : ((k : cycAway n) : ℂ) ≠ 0 := by simpa using h0
  have hne : (k : cycAway n) ≠ 0 := fun h => hk' (by rw [h]; rfl)
  have := (Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(F.X, U)) (r := (k : cycAway n))
    (mem_nonZeroDivisors_of_ne_zero hne)).right_eq_zero_of_smul (x := 1) (by rw [Algebra.smul_def, _root_.mul_one, map_natCast]; exact hk)
  exact one_ne_zero this

end GlobalTheory.SiegelTor
