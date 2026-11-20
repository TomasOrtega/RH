import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

namespace GlobalTheory.HasFields

/- English proof (translation)
Establish `hc : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries k)) (PowerSeries k)`. Rewrite using `[PowerSeries.maximalIdeal_eq_span_X]`. Use `infer_instance`. Establish `h0 : CharZero (PowerSeries k)` using `algebraRat.charZero _`. Conclude with `(GlobalTheory.LN.cDvr_iff _).2 ⟨inferInstance, hc, h0⟩`.
-/
theorem cdv_powerSeries (k : Type) [Field k] [CharZero k] : CDV (PowerSeries k) := by
  have hc : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries k)) (PowerSeries k) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  have h0 : CharZero (PowerSeries k) := algebraRat.charZero _
  exact (GlobalTheory.LN.cDvr_iff _).2 ⟨inferInstance, hc, h0⟩

/- English proof (translation)
Use `letI : Algebra R L := ψ.toAlgebra`. Use `haveI : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).2 hψ`. Set `e : K →ₐ[R] L` to `IsAlgClosed.lift`. Conclude with `⟨e, fun x => e.commutes x⟩`.
-/
theorem exists_lift (R K L : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [FaithfulSMul R K] [Algebra.IsAlgebraic R K] [Field L] [IsAlgClosed L] (ψ : R →+* L)
    (hψ : Function.Injective ψ) : ∃ e : K →+* L, ∀ x, e (algebraMap R K x) = ψ x := by
  letI : Algebra R L := ψ.toAlgebra
  haveI : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).2 hψ
  let e : K →ₐ[R] L := IsAlgClosed.lift
  exact ⟨e, fun x => e.commutes x⟩

/- English proof (translation)
Introduce `O' _ _ _ K _ _ _ _`. Set `F` to `FractionRing O'`. Use `haveI : CharZero F := IsFractionRing.charZero_of_isFractionRing O'`. Set `W` to `PowerSeries F`. Set `φ : PowerSeries O' →+* W` to `PowerSeries.map (algebraMap O' F)`.

Establish `hφ : Function.Injective φ` using `PowerSeries.map_injective _ (IsFractionRing.injective O' F)`. Set `K₁` to `AlgebraicClosure (FractionRing W)`. Set `ψ : PowerSeries O' →+* K₁` to `(algebraMap (FractionRing W) K₁).comp ((algebraMap W (FractionRing W)).comp φ)`. Establish `hψ : Function.Injective ψ` using `(algebraMap (FractionRing W) K₁).injective.comp ((IsFractionRing.injective W (FractionRing W)).comp hφ)`. Establish `key : ∃ e : K →+* K₁, ∀ x, e (algebraMap (PowerSeries O') K x) = ψ x` using `exists_lift _ K K₁ ψ hψ`.

Take `⟨e, he⟩` from `key`. Use `⟨W, inferInstance, inferInstance, inferInstance, φ, K₁, inferInstance, inferInstance, inferInstance, e, cdv_powerSeries F, ?_, he⟩` and prove the remaining obligations. Rewrite using `[PowerSeries.maximalIdeal_eq_span_X]`. Establish `hX : φ PowerSeries.X = PowerSeries.X` using `PowerSeries.map_X _`. Rewrite using `[hX]`.

Conclude with `Ideal.subset_span rfl`.
-/
theorem exists_cdv_over_powerSeries : ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (K : Type) [Field K] [Algebra (PowerSeries O') K] [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K], ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : PowerSeries O' →+* W) (K₁ : Type) (_ : Field K₁) (_ : Algebra (FractionRing W) K₁) (_ : Algebra.IsAlgebraic (FractionRing W) K₁) (e : K →+* K₁), CDV W ∧ φ PowerSeries.X ∈ IsLocalRing.maximalIdeal W ∧ ∀ x, e (algebraMap (PowerSeries O') K x) = algebraMap (FractionRing W) K₁ (algebraMap W _ (φ x)) := by
  intro O' _ _ _ K _ _ _ _
  let F := FractionRing O'
  haveI : CharZero F := IsFractionRing.charZero_of_isFractionRing O'
  let W := PowerSeries F
  let φ : PowerSeries O' →+* W := PowerSeries.map (algebraMap O' F)
  have hφ : Function.Injective φ :=
    PowerSeries.map_injective _ (IsFractionRing.injective O' F)
  let K₁ := AlgebraicClosure (FractionRing W)
  let ψ : PowerSeries O' →+* K₁ :=
    (algebraMap (FractionRing W) K₁).comp ((algebraMap W (FractionRing W)).comp φ)
  have hψ : Function.Injective ψ :=
    (algebraMap (FractionRing W) K₁).injective.comp
      ((IsFractionRing.injective W (FractionRing W)).comp hφ)
  have key : ∃ e : K →+* K₁, ∀ x, e (algebraMap (PowerSeries O') K x) = ψ x :=
    exists_lift _ K K₁ ψ hψ
  obtain ⟨e, he⟩ := key
  refine ⟨W, inferInstance, inferInstance, inferInstance, φ, K₁, inferInstance, inferInstance,
    inferInstance, e, cdv_powerSeries F, ?_, he⟩
  rw [PowerSeries.maximalIdeal_eq_span_X]
  have hX : φ PowerSeries.X = PowerSeries.X := PowerSeries.map_X _
  rw [hX]
  exact Ideal.subset_span rfl

end GlobalTheory.HasFields
