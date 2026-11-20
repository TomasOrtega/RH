import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef.InfScale

variable {F : Type} [Field F]

noncomputable def polyScale (c : F) : F[X] →ₐ[F] F[X] := Polynomial.aeval (Polynomial.C c * Polynomial.X)

/- English proof (translation)
Establish `: (polyScale d).comp (polyScale c) = polyScale (c * d)`. Apply `Polynomial.algHom_ext` to reduce the goal to its premises. Simplify using `only [polyScale, AlgHom.comp_apply, Polynomial.aeval_X, map_mul, Polynomial.aeval_C, Polynomial.algebraMap_eq, Polynomial.C_mul]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `congrArg (fun φ : F[X] →ₐ[F] F[X] => φ p) this`.
-/
theorem polyScale_polyScale (c d : F) (p : F[X]) :
    polyScale d (polyScale c p) = polyScale (c * d) p := by
  have : (polyScale d).comp (polyScale c) = polyScale (c * d) := by
    apply Polynomial.algHom_ext
    simp only [polyScale, AlgHom.comp_apply, Polynomial.aeval_X, map_mul, Polynomial.aeval_C,
      Polynomial.algebraMap_eq, Polynomial.C_mul]
    ring
  exact congrArg (fun φ : F[X] →ₐ[F] F[X] => φ p) this

/- English proof (translation)
Use `show Polynomial.aeval (Polynomial.C (1 : F) * Polynomial.X) p = p`. Rewrite using `[map_one, one_mul, Polynomial.aeval_X_left_apply]`.
-/
theorem polyScale_one (p : F[X]) : polyScale (1 : F) p = p := by
  show Polynomial.aeval (Polynomial.C (1 : F) * Polynomial.X) p = p
  rw [map_one, one_mul, Polynomial.aeval_X_left_apply]

/- English proof (translation)
Introduce `p q h`. Use `congrArg (polyScale c⁻¹) h` as an intermediate fact. Rewrite `this` using `[polyScale_polyScale, polyScale_polyScale, mul_inv_cancel₀ hc, polyScale_one, polyScale_one]`. Then use the resulting hypothesis.
-/
theorem polyScale_injective {c : F} (hc : c ≠ 0) : Function.Injective (polyScale c) := by
  intro p q h
  have := congrArg (polyScale c⁻¹) h
  rwa [polyScale_polyScale, polyScale_polyScale, mul_inv_cancel₀ hc, polyScale_one, polyScale_one] at this

/- English proof (translation)
Introduce `p q h`. Use `congrArg (PowerSeries.rescale c⁻¹) h` as an intermediate fact. Rewrite `this` using `[PowerSeries.rescale_rescale, PowerSeries.rescale_rescale, mul_inv_cancel₀ hc, PowerSeries.rescale_one, RingHom.id_apply, RingHom.id_apply]`. Then use the resulting hypothesis.
-/
theorem rescale_injective {c : F} (hc : c ≠ 0) : Function.Injective (PowerSeries.rescale c) := by
  intro p q h
  have := congrArg (PowerSeries.rescale c⁻¹) h
  rwa [PowerSeries.rescale_rescale, PowerSeries.rescale_rescale, mul_inv_cancel₀ hc,
    PowerSeries.rescale_one, RingHom.id_apply, RingHom.id_apply] at this

/- English proof (translation)
Rewrite using `[transcendental_iff_injective]`. Introduce `p q h`. Establish `e : ∀ r : F[X], Polynomial.aeval (RatFunc.X : RatFunc F) r = algebraMap F[X] (RatFunc F) r`. Introduce `r`. Rewrite using `[← RatFunc.algebraMap_X, Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]`.

Rewrite `h` using `[e, e]`. Conclude with `IsFractionRing.injective F[X] (RatFunc F) h`.
-/
theorem transcendental_X : Transcendental F (RatFunc.X : RatFunc F) := by
  rw [transcendental_iff_injective]
  intro p q h
  have e : ∀ r : F[X], Polynomial.aeval (RatFunc.X : RatFunc F) r = algebraMap F[X] (RatFunc F) r := by
    intro r
    rw [← RatFunc.algebraMap_X, Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]
  rw [e, e] at h
  exact IsFractionRing.injective F[X] (RatFunc F) h

end GlobalTheory.Nef.InfScale

namespace GlobalTheory.Nef.InfScale

variable {F : Type} [Field F]

noncomputable def ratScale (c : F) (hc : c ≠ 0) : RatFunc F →+* RatFunc F :=
  IsFractionRing.lift (g := (algebraMap F[X] (RatFunc F)).comp (polyScale c).toRingHom)
    ((IsFractionRing.injective F[X] (RatFunc F)).comp (polyScale_injective hc))

noncomputable def lsScale (c : F) (hc : c ≠ 0) : LaurentSeries F →+* LaurentSeries F :=
  IsFractionRing.lift (g := (algebraMap (PowerSeries F) (LaurentSeries F)).comp (PowerSeries.rescale c))
    ((IsFractionRing.injective (PowerSeries F) (LaurentSeries F)).comp (rescale_injective hc))

noncomputable def ratInv : RatFunc F →+* RatFunc F :=
  IsFractionRing.lift (g := (Polynomial.aeval (RatFunc.X : RatFunc F)⁻¹).toRingHom)
    (fun x y h => (transcendental_iff_injective.1 fun h => transcendental_X (IsAlgebraic.inv_iff.1 h)) h)

/- English proof (translation)
The claim follows from `IsLocalization.lift_comp _`.
-/
theorem lsScale_comp (c : F) (hc : c ≠ 0) :
    (lsScale c hc).comp (algebraMap (PowerSeries F) (LaurentSeries F)) =
      (algebraMap (PowerSeries F) (LaurentSeries F)).comp (PowerSeries.rescale c) :=
  IsLocalization.lift_comp _

/- English proof (translation)
The claim follows from `IsLocalization.lift_eq _ _`.
-/
theorem ratScale_alg (c : F) (hc : c ≠ 0) (p : F[X]) :
    ratScale c hc (algebraMap F[X] (RatFunc F) p) = algebraMap F[X] (RatFunc F) (polyScale c p) :=
  IsLocalization.lift_eq _ _

/- English proof (translation)
The claim follows from `IsLocalization.lift_eq _ _`.
-/
theorem ratInv_alg (p : F[X]) :
    ratInv (algebraMap F[X] (RatFunc F) p) = Polynomial.aeval (RatFunc.X : RatFunc F)⁻¹ p :=
  IsLocalization.lift_eq _ _

/- English proof (translation)
Apply `IsLocalization.ringHom_ext (nonZeroDivisors F[X])` to reduce the goal to its premises. Apply `Polynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify `hC a` using `[RatFunc.algebraMap_C]`. Simplify `hX` using `[RatFunc.algebraMap_X]`.
-/
theorem ext_rat {A : Type} [CommRing A] {f g : RatFunc F →+* A}
    (hC : ∀ a, f (RatFunc.C a) = g (RatFunc.C a)) (hX : f RatFunc.X = g RatFunc.X) : f = g := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors F[X])
  apply Polynomial.ringHom_ext
  · intro a; simpa [RatFunc.algebraMap_C] using hC a
  · simpa [RatFunc.algebraMap_X] using hX

/- English proof (translation)
Rewrite using `[← RatFunc.algebraMap_C, ratScale_alg]`. Simplify using `[polyScale]`.
-/
theorem ratScale_C (c : F) (hc : c ≠ 0) (a : F) : ratScale c hc (RatFunc.C a) = RatFunc.C a := by
  rw [← RatFunc.algebraMap_C, ratScale_alg]; simp [polyScale]

/- English proof (translation)
Rewrite using `[← RatFunc.algebraMap_X, ratScale_alg]`. Simplify using `[polyScale, RatFunc.algebraMap_C, RatFunc.algebraMap_X]`.
-/
theorem ratScale_X (c : F) (hc : c ≠ 0) :
    ratScale c hc RatFunc.X = RatFunc.C c * RatFunc.X := by
  rw [← RatFunc.algebraMap_X, ratScale_alg]; simp [polyScale, RatFunc.algebraMap_C, RatFunc.algebraMap_X]

/- English proof (translation)
Rewrite using `[← RatFunc.algebraMap_C, ratInv_alg]`. Simplify using the standard rewrite rules.
-/
theorem ratInv_C (a : F) : ratInv (RatFunc.C a) = RatFunc.C a := by
  rw [← RatFunc.algebraMap_C, ratInv_alg]; simp

/- English proof (translation)
Rewrite using `[← RatFunc.algebraMap_X, ratInv_alg]`. Simplify using the standard rewrite rules.
-/
theorem ratInv_X : ratInv (RatFunc.X : RatFunc F) = RatFunc.X⁻¹ := by
  rw [← RatFunc.algebraMap_X, ratInv_alg]; simp

end GlobalTheory.Nef.InfScale

namespace GlobalTheory.Nef.InfScale

variable {F : Type} [Field F]

/- English proof (translation)
Establish `h` using `(RatFunc.coe_coe (Polynomial.C a)).symm`. Rewrite `h` using `[Polynomial.coe_C]`. Conclude with `h`.
-/
theorem alg_C (a : F) : algebraMap (RatFunc F) (LaurentSeries F) (RatFunc.C a) =
    algebraMap (PowerSeries F) (LaurentSeries F) (PowerSeries.C a) := by
  have h := (RatFunc.coe_coe (Polynomial.C a)).symm
  rw [Polynomial.coe_C] at h
  exact h

/- English proof (translation)
Simplify using `[RatFunc.coe_X]`.
-/
theorem alg_X : algebraMap (RatFunc F) (LaurentSeries F) RatFunc.X =
    algebraMap (PowerSeries F) (LaurentSeries F) PowerSeries.X := by
  simp [RatFunc.coe_X]

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[PowerSeries.coeff_rescale, PowerSeries.coeff_C]`. Apply the tactic sequence `rcases n with _ | n <;> simp`.
-/
theorem rescale_C' (c a : F) : PowerSeries.rescale c (PowerSeries.C a) = PowerSeries.C a := by
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  rcases n with _ | n <;> simp

/- English proof (translation)
Establish `hl : ∀ p, lsScale c hc (algebraMap (PowerSeries F) (LaurentSeries F) p) = algebraMap (PowerSeries F) (LaurentSeries F) (PowerSeries.rescale c p)` using `fun p => RingHom.congr_fun (lsScale_comp c hc) p`. Apply `ext_rat` to reduce the goal to its premises. Introduce `a`. Simplify using `only [RingHom.comp_apply, ratScale_C, alg_C, hl, rescale_C']`. Simplify using `only [RingHom.comp_apply, ratScale_X, map_mul, alg_C, alg_X, hl, PowerSeries.rescale_X, rescale_C']`.
-/
theorem lsScale_rat (c : F) (hc : c ≠ 0) :
    (lsScale c hc).comp (algebraMap (RatFunc F) (LaurentSeries F)) =
      (algebraMap (RatFunc F) (LaurentSeries F)).comp (ratScale c hc) := by
  have hl : ∀ p, lsScale c hc (algebraMap (PowerSeries F) (LaurentSeries F) p) =
      algebraMap (PowerSeries F) (LaurentSeries F) (PowerSeries.rescale c p) :=
    fun p => RingHom.congr_fun (lsScale_comp c hc) p
  apply ext_rat
  · intro a
    simp only [RingHom.comp_apply, ratScale_C, alg_C, hl, rescale_C']
  · simp only [RingHom.comp_apply, ratScale_X, map_mul, alg_C, alg_X, hl, PowerSeries.rescale_X,
      rescale_C']

/- English proof (translation)
Apply `ext_rat` to reduce the goal to its premises. Introduce `a`. Simplify using `only [RingHom.comp_apply, ratScale_C, ratInv_C]`. Simplify using `only [RingHom.comp_apply, ratScale_X, ratInv_X, map_mul, ratInv_C, map_inv₀, mul_inv, inv_inv]`.
-/
theorem ratInv_ratScale (c : F) (hc : c ≠ 0) :
    ratInv.comp (ratScale c hc) = (ratScale c⁻¹ (inv_ne_zero hc)).comp ratInv := by
  apply ext_rat
  · intro a; simp only [RingHom.comp_apply, ratScale_C, ratInv_C]
  · simp only [RingHom.comp_apply, ratScale_X, ratInv_X, map_mul, ratInv_C, map_inv₀, mul_inv,
      inv_inv]

/- English proof (translation)
Introduce `F _ _`. Establish `h2 : (2 : F) ≠ 0` using `two_ne_zero`. Establish `h2' : (2 : F)⁻¹ ≠ 0` using `inv_ne_zero h2`. Use `⟨ratScale 2 h2, (algebraMap (RatFunc F) (LaurentSeries F)).comp ratInv, lsScale 2 h2, lsScale 2⁻¹ h2', lsScale_comp 2 h2, lsScale_rat 2 h2, lsScale_comp 2⁻¹ h2', ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← RingHom.comp_assoc, lsScale_rat, RingHom.comp_assoc, RingHom.comp_assoc, ratInv_ratScale 2 h2]`.

Use extensionality with `a`. Simplify using `only [RingHom.comp_apply, ratInv_C, alg_C]`. Use extensionality with `a`. Simplify using `only [RingHom.comp_apply, alg_C]`.
-/
theorem scaling_expansion_infinity :
    ∀ (F : Type) [Field F] [CharZero F], ∃ (σ : RatFunc F →+* RatFunc F) (j : RatFunc F →+* LaurentSeries F) (r₂ rh : LaurentSeries F →+* LaurentSeries F), r₂.comp (algebraMap (PowerSeries F) (LaurentSeries F)) = (algebraMap (PowerSeries F) (LaurentSeries F)).comp (PowerSeries.rescale 2) ∧ r₂.comp (algebraMap (RatFunc F) (LaurentSeries F)) = (algebraMap (RatFunc F) (LaurentSeries F)).comp σ ∧ rh.comp (algebraMap (PowerSeries F) (LaurentSeries F)) = (algebraMap (PowerSeries F) (LaurentSeries F)).comp (PowerSeries.rescale 2⁻¹) ∧ rh.comp j = j.comp σ ∧ j.comp RatFunc.C = (algebraMap (PowerSeries F) (LaurentSeries F)).comp PowerSeries.C ∧ (algebraMap (RatFunc F) (LaurentSeries F)).comp RatFunc.C = (algebraMap (PowerSeries F) (LaurentSeries F)).comp PowerSeries.C := by
  intro F _ _
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have h2' : (2 : F)⁻¹ ≠ 0 := inv_ne_zero h2
  refine ⟨ratScale 2 h2, (algebraMap (RatFunc F) (LaurentSeries F)).comp ratInv, lsScale 2 h2,
    lsScale 2⁻¹ h2', lsScale_comp 2 h2, lsScale_rat 2 h2, lsScale_comp 2⁻¹ h2', ?_, ?_, ?_⟩
  · rw [← RingHom.comp_assoc, lsScale_rat, RingHom.comp_assoc, RingHom.comp_assoc,
      ratInv_ratScale 2 h2]
  · ext a; simp only [RingHom.comp_apply, ratInv_C, alg_C]
  · ext a; simp only [RingHom.comp_apply, alg_C]

end GlobalTheory.Nef.InfScale
