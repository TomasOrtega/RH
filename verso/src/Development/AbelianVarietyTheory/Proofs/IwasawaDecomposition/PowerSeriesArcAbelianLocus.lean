import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntOfIsIntegral
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.PolArc

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `v hv`. Assume the negation of the conclusion as `hne`. Establish `hvF : ((v : c.F)) ≠ 0` using `fun h => hne (Subtype.ext h)`. Take `⟨n, hn, hint⟩` from `IsAlgebraic.exists_integral_multiple (R := ℤ) (z := ((v : c.F))⁻¹) ((IsFractionRing.isAlgebraic_iff ℤ ℚ c.F).mpr (Algebra.IsAlgebraic.isAlgebraic _))`.

Establish `hint' : IsIntegral (c.V W) (n • ((v : c.F))⁻¹)` using `hint.tower_top`. Take `⟨w, hw⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hint'`. Establish `hw' : (w : c.F) = (n : c.F) * (v : c.F)⁻¹` using `by rw [← zsmul_eq_mul]; exact hw`. Establish `e : (n : c.V W) = v * w`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[MulMemClass.coe_mul, hw', mul_comm (n : c.F), ← mul_assoc, mul_inv_cancel₀ hvF, one_mul]`. Simplify using the standard rewrite rules. Establish `h0 : b' (n : c.V W) = 0` using `by rw [e, map_mul, hv, zero_mul]`. Rewrite `h0` using `[map_intCast]`. Conclude with `hn (Int.cast_eq_zero.mp h0)`.
-/
theorem injective_of_charZero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}
    (c : Coeff l) (W : ValuationSubring ℂ) {O' : Type} [CommRing O'] [IsDomain O'] [CharZero O']
    (b' : c.V W →+* O') : Function.Injective b' := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  by_contra hne
  have hvF : ((v : c.F)) ≠ 0 := fun h => hne (Subtype.ext h)
  obtain ⟨n, hn, hint⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) (z := ((v : c.F))⁻¹)
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ c.F).mpr (Algebra.IsAlgebraic.isAlgebraic _))
  have hint' : IsIntegral (c.V W) (n • ((v : c.F))⁻¹) := hint.tower_top
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint'
  have hw' : (w : c.F) = (n : c.F) * (v : c.F)⁻¹ := by rw [← zsmul_eq_mul]; exact hw
  have e : (n : c.V W) = v * w := by
    apply Subtype.ext
    rw [MulMemClass.coe_mul, hw', mul_comm (n : c.F), ← mul_assoc, mul_inv_cancel₀ hvF, one_mul]
    simp
  have h0 : b' (n : c.V W) = 0 := by rw [e, map_mul, hv, zero_mul]
  rw [map_intCast] at h0
  exact hn (Int.cast_eq_zero.mp h0)

end GlobalTheory.PolArc

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c W Y O' _ _ _ b' χ₀ hs hab`. Establish `hb'` using `GlobalTheory.PolArc.injective_of_charZero c W b'`. Establish `hC : Function.Injective (PowerSeries.C (R` using `O')) := fun a b h => by`. Simplify using `using congrArg (PowerSeries.constantCoeff (R := O')) h`. Establish `hinj : Function.Injective ((algebraMap (PowerSeries O') (FractionRing (PowerSeries O'))).comp ((PowerSeries.C (R` using `O')).comp b')) := (IsFractionRing.injective (PowerSeries O') (FractionRing (PowerSeries O'))).comp (hC.comp hb')`.

Take `⟨g, hg⟩ : ∃ g : c.F →+* FractionRing (PowerSeries O'), g.comp (c.V W).subtype = (algebraMap (PowerSeries O') (FractionRing (PowerSeries O'))).comp ((PowerSeries.C (R` from `O')).comp b') := by`. Use `⟨IsFractionRing.lift (A := c.V W) (K := c.F) hinj, RingHom.ext fun v => ?_⟩` and prove the remaining obligations. Establish `key` using `IsFractionRing.lift_algebraMap (A := c.V W) (K := c.F) hinj v`. Rewrite using `[RingHom.comp_apply]`. Conclude with `key`.

Establish `hsq : (Out.jK (PowerSeries O') ≫ χ₀) ≫ Y.s = spMap g ≫ spMap (c.V W).subtype`. Rewrite using `[Category.assoc, hs]`. Simplify using `only [Out.jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hg]`. Set `q` to `pullback.lift (Out.jK (PowerSeries O') ≫ χ₀) (spMap g) hsq`. Establish `hrange : Set.range q ⊆ Set.range Y.jQ`.

Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, hab]`. Introduce `hX`. Establish `h1 : y.asIdeal = ⊥` using `@Ideal.eq_bot_of_prime _ _ y.asIdeal y.isPrime`. Establish `h2 : algebraMap (PowerSeries O') (FractionRing (PowerSeries O')) PowerSeries.X ∈ y.asIdeal` using `hX`.

Rewrite `h2` using `[h1, Ideal.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective _ _)]`. Conclude with `PowerSeries.X_ne_zero h2`. Use `haveI := Y.jQ_open`. Use `⟨IsOpenImmersion.lift Y.jQ q hrange, ?_⟩` and prove the remaining obligations. Rewrite using `[Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]`.
-/
theorem GlobalTheory.PolArc.generic_factors_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (W : ValuationSubring ℂ) (Y : Model Xo c (c.V W).subtype) (O' : Type) [CommRing O'] [IsDomain O']
    [CharZero O'] (b' : c.V W →+* O') (χ₀ : Sp (PowerSeries O') ⟶ Y.X),
    χ₀ ≫ Y.s = spMap (PowerSeries.C (R := O')) ≫ spMap b' →
    (∀ x : Sp (PowerSeries O'), χ₀ x ∈ abLocus Y.t.G ↔ PowerSeries.X ∉ x.asIdeal) →
    ∃ x₀ : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, Out.jK (PowerSeries O') ≫ χ₀ = x₀ ≫ Y.j := by
  intro E _ _ _ H D l Xo c W Y O' _ _ _ b' χ₀ hs hab
  have hb' := GlobalTheory.PolArc.injective_of_charZero c W b'
  have hC : Function.Injective (PowerSeries.C (R := O')) := fun a b h => by
    simpa using congrArg (PowerSeries.constantCoeff (R := O')) h
  have hinj : Function.Injective ((algebraMap (PowerSeries O') (FractionRing (PowerSeries O'))).comp
      ((PowerSeries.C (R := O')).comp b')) :=
    (IsFractionRing.injective (PowerSeries O') (FractionRing (PowerSeries O'))).comp (hC.comp hb')
  obtain ⟨g, hg⟩ : ∃ g : c.F →+* FractionRing (PowerSeries O'), g.comp (c.V W).subtype =
      (algebraMap (PowerSeries O') (FractionRing (PowerSeries O'))).comp ((PowerSeries.C (R := O')).comp b') := by
    refine ⟨IsFractionRing.lift (A := c.V W) (K := c.F) hinj, RingHom.ext fun v => ?_⟩
    have key := IsFractionRing.lift_algebraMap (A := c.V W) (K := c.F) hinj v
    rw [RingHom.comp_apply]
    exact key
  have hsq : (Out.jK (PowerSeries O') ≫ χ₀) ≫ Y.s = spMap g ≫ spMap (c.V W).subtype := by
    rw [Category.assoc, hs]
    simp only [Out.jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hg]
  let q := pullback.lift (Out.jK (PowerSeries O') ≫ χ₀) (spMap g) hsq
  have hrange : Set.range q ⊆ Set.range Y.jQ := by
    rintro _ ⟨y, rfl⟩
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, hab]
    intro hX
    have h1 : y.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ y.asIdeal y.isPrime
    have h2 : algebraMap (PowerSeries O') (FractionRing (PowerSeries O')) PowerSeries.X ∈ y.asIdeal := hX
    rw [h1, Ideal.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h2
    exact PowerSeries.X_ne_zero h2
  haveI := Y.jQ_open
  refine ⟨IsOpenImmersion.lift Y.jQ q hrange, ?_⟩
  rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]
