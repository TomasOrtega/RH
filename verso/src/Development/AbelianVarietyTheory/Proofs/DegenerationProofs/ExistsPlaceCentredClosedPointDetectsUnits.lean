import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralClosureFiniteLocalOfIsAdicComplete
import ReciprocityTheory.AdicCompleteness.IsAdicCompleteComapConstantCoeff

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

namespace GlobalTheory.CentredPlace

/- English proof (translation)
Use `letI := f.toAlgebra`. Set `σ : K →ₐ[L] M` to `IsAlgClosed.lift`. Conclude with `⟨σ.toRingHom, fun x => σ.commutes x⟩`.
-/
theorem exists_extension {F K M : Type} [Field F] [Field K] [Algebra F K] [Algebra.IsAlgebraic F K] [Field M]
    [IsAlgClosed M] (L : IntermediateField F K) (f : L →+* M) : ∃ σ : K →+* M, ∀ x : L, σ x = f x := by
  letI := f.toAlgebra
  let σ : K →ₐ[L] M := IsAlgClosed.lift
  exact ⟨σ.toRingHom, fun x => σ.commutes x⟩

/- English proof (translation)
Set `V` to `AdicCompletion (maximalIdeal W) W`. Establish `hj : Function.Injective (algebraMap W V)` using `algebraMap_adicCompletion_injective_of_dvr W`. Set `j : W →+* FractionRing V` to `(algebraMap V (FractionRing V)).comp (algebraMap W V)`. Establish `hj' : Function.Injective j` using `(IsFractionRing.injective V (FractionRing V)).comp hj`. Set `f : L →+* FractionRing V` to `IsFractionRing.lift (K := L) hj'`.

Establish `hf : ∀ w : W, f (w : L) = j w` using `fun w => IsFractionRing.lift_algebraMap hj' w`. Set `φ : R₁ →+* V` to `(algebraMap W V).comp ((algebraMap R₁ L).codRestrict W hW)`. Establish `hinj : Function.Injective (algebraMap R₁ L)`. Rewrite using `[IsScalarTower.algebraMap_eq R₁ (FractionRing R₁) L]`. Conclude with `(algebraMap (FractionRing R₁) L).injective.comp (IsFractionRing.injective R₁ _)`.

Establish `hφ : Function.Injective φ` using `hj.comp fun a b hab => hinj (congrArg Subtype.val hab)`. Establish `hV : CDvr V` using `⟨inferInstance, inferInstance, charZero_of_injective_ringHom hφ⟩`. Take `⟨σ, hσ⟩` from `exists_extension L ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp f)`. Take `⟨S, hS, h⟩` from `hP V hV φ (f.comp (algebraMap (FractionRing R₁) L)) (fun r => by`. Rewrite using `[RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]`.

Conclude with `hf ⟨_, hW r⟩) σ (fun x => hσ (algebraMap (FractionRing R₁) L x))`. Use `⟨S, hS, fun x hx hxS => ?_⟩` and prove the remaining obligations. Take `⟨v, hv⟩` from `(h x (f x) (hσ x)).1 hxS`. Establish `hx0 : x ≠ 0` using `fun e => hx (e ▸ W.zero_mem)`. Establish `hi : x⁻¹ ∈ W` using `(W.mem_or_inv_mem x).resolve_left hx`.

Establish `hu : IsUnit (algebraMap W V ⟨x⁻¹, hi⟩)`. Use `IsUnit.of_mul_eq_one v (IsFractionRing.injective V (FractionRing V) ?_)` and prove the remaining obligations. Rewrite using `[map_mul, hv, map_one]`. Express the relevant statement in the definitionally equal form `j ⟨x⁻¹, hi⟩ * _ = _`. Rewrite using `[← hf, ← map_mul, inv_mul_cancel₀ hx0, map_one]`.

Take `⟨u, hu'⟩` from `isUnit_iff_exists_inv.1 (IsLocalHom.map_nonunit _ hu)`. Establish `: x⁻¹ * u = 1` using `congrArg Subtype.val hu'`. Establish `e : (u : L) = x` using `by rw [eq_inv_of_mul_eq_one_right this, inv_inv]`. Conclude with `hx (e ▸ u.2)`.
-/
theorem exists_mem_of_dvr {R₁ : Type} [CommRing R₁] [IsDomain R₁] [CharZero R₁]
    (P : Set (ValuationSubring (AlgebraicClosure (FractionRing R₁))))
    (hP : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (φ : R₁ →+* V)
      (gam : FractionRing R₁ →+* FractionRing V), (∀ r, gam (algebraMap R₁ _ r) = algebraMap V _ (φ r)) →
      ∀ σ : AlgebraicClosure (FractionRing R₁) →+* AlgebraicClosure (FractionRing V),
      (∀ x, σ (algebraMap (FractionRing R₁) _ x) = algebraMap (FractionRing V) _ (gam x)) →
      ∃ S ∈ P, ∀ x (y : FractionRing V), σ x = algebraMap (FractionRing V) _ y →
        (x ∈ S ↔ y ∈ Set.range (algebraMap V (FractionRing V))))
    (L : IntermediateField (FractionRing R₁) (AlgebraicClosure (FractionRing R₁)))
    (W : ValuationSubring L) [IsDiscreteValuationRing W] (hW : ∀ r : R₁, algebraMap R₁ L r ∈ W) :
    ∃ S ∈ P, ∀ x : L, x ∉ W → (x : AlgebraicClosure (FractionRing R₁)) ∉ S := by
  let V := AdicCompletion (maximalIdeal W) W
  have hj : Function.Injective (algebraMap W V) := algebraMap_adicCompletion_injective_of_dvr W
  let j : W →+* FractionRing V := (algebraMap V (FractionRing V)).comp (algebraMap W V)
  have hj' : Function.Injective j := (IsFractionRing.injective V (FractionRing V)).comp hj
  let f : L →+* FractionRing V := IsFractionRing.lift (K := L) hj'
  have hf : ∀ w : W, f (w : L) = j w := fun w => IsFractionRing.lift_algebraMap hj' w
  let φ : R₁ →+* V := (algebraMap W V).comp ((algebraMap R₁ L).codRestrict W hW)
  have hinj : Function.Injective (algebraMap R₁ L) := by
    rw [IsScalarTower.algebraMap_eq R₁ (FractionRing R₁) L]
    exact (algebraMap (FractionRing R₁) L).injective.comp (IsFractionRing.injective R₁ _)
  have hφ : Function.Injective φ := hj.comp fun a b hab => hinj (congrArg Subtype.val hab)
  have hV : CDvr V := ⟨inferInstance, inferInstance, charZero_of_injective_ringHom hφ⟩
  obtain ⟨σ, hσ⟩ := exists_extension L
    ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp f)
  obtain ⟨S, hS, h⟩ := hP V hV φ (f.comp (algebraMap (FractionRing R₁) L))
    (fun r => by
      rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
      exact hf ⟨_, hW r⟩) σ (fun x => hσ (algebraMap (FractionRing R₁) L x))
  refine ⟨S, hS, fun x hx hxS => ?_⟩
  obtain ⟨v, hv⟩ := (h x (f x) (hσ x)).1 hxS
  have hx0 : x ≠ 0 := fun e => hx (e ▸ W.zero_mem)
  have hi : x⁻¹ ∈ W := (W.mem_or_inv_mem x).resolve_left hx
  have hu : IsUnit (algebraMap W V ⟨x⁻¹, hi⟩) := by
    refine IsUnit.of_mul_eq_one v (IsFractionRing.injective V (FractionRing V) ?_)
    rw [map_mul, hv, map_one]
    change j ⟨x⁻¹, hi⟩ * _ = _
    rw [← hf, ← map_mul, inv_mul_cancel₀ hx0, map_one]
  obtain ⟨u, hu'⟩ := isUnit_iff_exists_inv.1 (IsLocalHom.map_nonunit _ hu)
  have : x⁻¹ * u = 1 := congrArg Subtype.val hu'
  have e : (u : L) = x := by rw [eq_inv_of_mul_eq_one_right this, inv_inv]
  exact hx (e ▸ u.2)

/- English proof (translation)
Set `B` to `Algebra.adjoin R₀ {x}`. Establish `: Module.Finite R₀ B` using `Algebra.finite_adjoin_simple_of_isIntegral hx`. Establish `: IsLocalRing B` using `T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := R₀) B`. Set `S' : Subalgebra R₀ K` to `{ S.toSubring with algebraMap_mem' := h₁ }`. Establish `hB : B ≤ S'` using `Algebra.adjoin_le (by rintro _ rfl; exact hxS)`.

Set `i : B →+* S` to `(B.val : B →+* K).codRestrict S fun b => hB b.2`. Set `p : Ideal B` to `(maximalIdeal S).comap i`. Establish `hp : (p.comap (algebraMap R₀ B)).IsMaximal`. Establish `: maximalIdeal R₀ ≤ p.comap (algebraMap R₀ B)` using `fun r hr => (ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, h₁ r⟩)).mp (h₂ r hr)`. Rewrite using `[← (maximalIdeal.isMaximal R₀).eq_of_le (Ideal.IsPrime.ne_top inferInstance) this]`.

Use `infer_instance`. Establish `hm : p = maximalIdeal B` using `eq_maximalIdeal (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap p hp)`. Establish `hu : IsUnit (⟨x, Algebra.subset_adjoin rfl⟩ : B)`. Assume the negation of the conclusion as `hn`. Establish `: (⟨x, Algebra.subset_adjoin rfl⟩ : B) ∈ p` using `hm ▸ hn`.

Establish `h3 : x ∈ S.nonunits` using `(ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, hxS⟩)).mpr this`. Conclude with `(S.mem_nonunits_iff.1 h3).ne hv`. Take `⟨u, hu'⟩` from `isUnit_iff_exists_inv.1 hu`. Establish `: x * u = 1` using `congrArg Subtype.val hu'`. Rewrite using `[← eq_inv_of_mul_eq_one_right this]`.

Conclude with `(Algebra.IsIntegral.isIntegral (R := R₀) u).map B.val`.
-/
theorem isIntegral_inv {R₀ K : Type} [CommRing R₀] [IsLocalRing R₀] [IsNoetherianRing R₀]
    [IsAdicComplete (maximalIdeal R₀) R₀] [Field K] [Algebra R₀ K] (S : ValuationSubring K)
    (h₁ : ∀ r, algebraMap R₀ K r ∈ S) (h₂ : ∀ r ∈ maximalIdeal R₀, algebraMap R₀ K r ∈ S.nonunits)
    {x : K} (hx : IsIntegral R₀ x) (hxS : x ∈ S) (hv : S.valuation x = 1) : IsIntegral R₀ x⁻¹ := by
  let B := Algebra.adjoin R₀ {x}
  have : Module.Finite R₀ B := Algebra.finite_adjoin_simple_of_isIntegral hx
  have : IsLocalRing B := T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := R₀) B
  let S' : Subalgebra R₀ K := { S.toSubring with algebraMap_mem' := h₁ }
  have hB : B ≤ S' := Algebra.adjoin_le (by rintro _ rfl; exact hxS)
  let i : B →+* S := (B.val : B →+* K).codRestrict S fun b => hB b.2
  let p : Ideal B := (maximalIdeal S).comap i
  have hp : (p.comap (algebraMap R₀ B)).IsMaximal := by
    have : maximalIdeal R₀ ≤ p.comap (algebraMap R₀ B) := fun r hr =>
      (ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, h₁ r⟩)).mp (h₂ r hr)
    rw [← (maximalIdeal.isMaximal R₀).eq_of_le (Ideal.IsPrime.ne_top inferInstance) this]
    infer_instance
  have hm : p = maximalIdeal B := eq_maximalIdeal (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap p hp)
  have hu : IsUnit (⟨x, Algebra.subset_adjoin rfl⟩ : B) := by
    by_contra hn
    have : (⟨x, Algebra.subset_adjoin rfl⟩ : B) ∈ p := hm ▸ hn
    have h3 : x ∈ S.nonunits := (ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, hxS⟩)).mpr this
    exact (S.mem_nonunits_iff.1 h3).ne hv
  obtain ⟨u, hu'⟩ := isUnit_iff_exists_inv.1 hu
  have : x * u = 1 := congrArg Subtype.val hu'
  rw [← eq_inv_of_mul_eq_one_right this]
  exact (Algebra.IsIntegral.isIntegral (R := R₀) u).map B.val

/- English proof (translation)
Use `letI : Algebra R S := ((algebraMap R K).codRestrict S h).toAlgebra`. Establish `: IsScalarTower R S K` using `.of_algebraMap_eq fun _ => rfl`. Take `⟨y, rfl⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := S) (K := K)).mp (IsIntegral.tower_top (R := R) hx)`. Conclude with `y.2`.
-/
theorem mem_of_isIntegral {R K : Type} [CommRing R] [Field K] [Algebra R K] (S : ValuationSubring K)
    (h : ∀ r, algebraMap R K r ∈ S) {x : K} (hx : IsIntegral R x) : x ∈ S := by
  letI : Algebra R S := ((algebraMap R K).codRestrict S h).toAlgebra
  have : IsScalarTower R S K := .of_algebraMap_eq fun _ => rfl
  obtain ⟨y, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := S) (K := K)).mp
    (IsIntegral.tower_top (R := R) hx)
  exact y.2

/- English proof (translation)
Introduce `O' _ _ _ ϖ hO R₁ _ _ g hg hfin P hR hP`. Choose the witnesses or unpack the hypotheses as in `⟨_, _, hc⟩ : ∃ _ : IsLocalRing O', IsPrincipalIdealRing O' ∧ IsAdicComplete (maximalIdeal O') O' := by`. Break down `hO with ⟨hF, -⟩ | ⟨hD, hi, hc⟩` into its components or cases. Use `letI := hF.toField`. Use `⟨inferInstance, inferInstance, ?_⟩` and prove the remaining obligations.

Rewrite using `[IsLocalRing.maximalIdeal_eq_bot]`. Use `infer_instance`. Use `⟨inferInstance, inferInstance, ?_⟩` and prove the remaining obligations. Rewrite using `[hi.maximalIdeal_eq]` and apply the resulting hypothesis. Establish `hps : IsAdicComplete (maximalIdeal (PowerSeries O')) (PowerSeries O')` using `ReciprocityTheory.P1.isAdicComplete_ps`.

Establish `: CharZero (PowerSeries O')` using `charZero_of_injective_ringHom (PowerSeries.C_injective (R := O'))`. Establish `: CharZero R₁` using `charZero_of_injective_ringHom hg`. Use `letI := g.toAlgebra`. Establish `: Module.Finite (PowerSeries O') R₁` using `hfin`. Establish `: IsLocalRing R₁` using `T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := PowerSeries O') R₁`.

Establish `: IsNoetherianRing R₁` using `IsNoetherianRing.of_finite (PowerSeries O') R₁`. Establish `: FaithfulSMul (PowerSeries O') R₁` using `(faithfulSMul_iff_algebraMap_injective _ _).2 hg`. Establish `hloc : IsLocalHom (algebraMap (PowerSeries O') R₁)` using `inferInstance`. Establish `hR' : ∀ S ∈ P, ∀ r : R₁, algebraMap R₁ (AlgebraicClosure (FractionRing R₁)) r ∈ S` using `fun S hS r => by`. Rewrite using `[IsScalarTower.algebraMap_apply R₁ (FractionRing R₁)]`.

Conclude with `hR S hS r`. Establish `hinj : Function.Injective (algebraMap R₁ (AlgebraicClosure (FractionRing R₁)))`. Rewrite using `[IsScalarTower.algebraMap_eq R₁ (FractionRing R₁)]`. Conclude with `(algebraMap (FractionRing R₁) _).injective.comp (IsFractionRing.injective R₁ _)`. Establish `hnf : ¬ IsField R₁` using `fun h => by`.

Establish `hX : ¬ IsUnit (PowerSeries.X : PowerSeries O')` using `PowerSeries.X_prime.not_isUnit`. Use `hX (hloc.1 _ ?_)` and prove the remaining obligations. Take `⟨b, hb⟩` from `h.mul_inv_cancel ((map_ne_zero_iff g hg).2 PowerSeries.X_ne_zero)`. Conclude with `IsUnit.of_mul_eq_one b hb`. Establish `hint : ∀ x, (∀ S ∈ P, x ∈ S) → IsIntegral R₁ x` using `fun x hx => by`.

Assume the negation of the conclusion as `hn`. Set `L` to `IntermediateField.adjoin (FractionRing R₁) {x}`. Establish `: FiniteDimensional (FractionRing R₁) L` using `IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)`. Establish `: Algebra.EssFiniteType R₁ (FractionRing R₁)` using `.of_isLocalization _ (nonZeroDivisors R₁)`. Establish `: Algebra.EssFiniteType R₁ L` using `.comp R₁ (FractionRing R₁) L`.

Set `x' : L` to `⟨x, IntermediateField.subset_adjoin _ _ rfl⟩`. Establish `: IsScalarTower R₁ L (AlgebraicClosure (FractionRing R₁))` using `.of_algebraMap_eq fun _ => rfl`. Establish `hn' : ¬ IsIntegral R₁ x'` using `fun h => hn (h.map (IsScalarTower.toAlgHom R₁ L _))`. Take `⟨W, _, h2, h3⟩` from `exists_discreteValuationSubring_dominating_notMem (R := R₁) hn'`. Take `⟨S, hS, h⟩` from `exists_mem_of_dvr P hP L W ((localSubring_range_le_valuationSubring_iff _ _).1 h2).1`.

Conclude with `h x' h3 (hx S hS)`. Set `L : IntermediateField (FractionRing R₁) (AlgebraicClosure (FractionRing R₁))` to `⊥`. Take `⟨W, _, h2⟩` from `exists_discreteValuationSubring_dominating R₁ (FractionRing R₁) L hnf`. Take `⟨h2, h3⟩` from `(localSubring_range_le_valuationSubring_iff _ _).1 h2`. Take `⟨S₀, hS₀, h⟩` from `exists_mem_of_dvr P hP L W h2`.

Use `⟨S₀, hS₀, fun x hx hv S hS => ?_⟩` and prove the remaining obligations. Establish `e : ∀ r, algebraMap (PowerSeries O') (AlgebraicClosure (FractionRing R₁)) r = algebraMap R₁ _ (g r)` using `fun r => IsScalarTower.algebraMap_apply _ R₁ _ r`. Establish `hi : IsIntegral (PowerSeries O') x⁻¹`. Use `isIntegral_inv S₀ (fun r => e r ▸ hR' S₀ hS₀ (g r)) (fun r hr => ?_) (isIntegral_trans x (hint x hx)) (hx S₀ hS₀) hv` and prove the remaining obligations. Establish `h4` using `h3 (g r) (fun hu => hr (hloc.1 r hu))`.

Rewrite using `[e]`. Rewrite `h4`, the goal using `[ValuationSubring.mem_nonunits_iff_or]`. Conclude with `h4.imp (fun e => congrArg Subtype.val e) (fun e => h _ e)`. Establish `h5 : x⁻¹ ∈ S` using `mem_of_isIntegral S (hR' S hS) hi.tower_top`. Establish `hx0 : x ≠ 0`.

Introduce and unpack `rfl`. Simplify using `at hv`. Use `le_antisymm ((S.valuation_le_one_iff x).2 (hx S hS)) ?_` and prove the remaining obligations. Establish `h6` using `(S.valuation_le_one_iff _).2 h5`. Rewrite `h6` using `[map_inv₀, inv_le_one₀ (by simpa [Valuation.pos_iff] using hx0)]`. Then use the resulting hypothesis.
-/
theorem exists_place_detecting_units : ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (ϖ : O'), ArcBase O' ϖ → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁), Function.Injective g → g.Finite → ∀ P : Set (ValuationSubring (AlgebraicClosure (FractionRing R₁))), (∀ S ∈ P, ∀ r : R₁, algebraMap (FractionRing R₁) _ (algebraMap R₁ _ r) ∈ S) → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (φ : R₁ →+* V) (gam : FractionRing R₁ →+* FractionRing V), (∀ r, gam (algebraMap R₁ _ r) = algebraMap V _ (φ r)) → ∀ σ : AlgebraicClosure (FractionRing R₁) →+* AlgebraicClosure (FractionRing V), (∀ x, σ (algebraMap (FractionRing R₁) _ x) = algebraMap (FractionRing V) _ (gam x)) → ∃ S ∈ P, ∀ x (y : FractionRing V), σ x = algebraMap (FractionRing V) _ y → (x ∈ S ↔ y ∈ Set.range (algebraMap V (FractionRing V)))) → ∃ S₀ ∈ P, ∀ x, (∀ S ∈ P, x ∈ S) → S₀.valuation x = 1 → ∀ S ∈ P, S.valuation x = 1 := by
  intro O' _ _ _ ϖ hO R₁ _ _ g hg hfin P hR hP
  obtain ⟨_, _, hc⟩ : ∃ _ : IsLocalRing O', IsPrincipalIdealRing O' ∧ IsAdicComplete (maximalIdeal O') O' := by
    rcases hO with ⟨hF, -⟩ | ⟨hD, hi, hc⟩
    · letI := hF.toField
      refine ⟨inferInstance, inferInstance, ?_⟩
      rw [IsLocalRing.maximalIdeal_eq_bot]
      infer_instance
    · refine ⟨inferInstance, inferInstance, ?_⟩
      rwa [hi.maximalIdeal_eq]
  have hps : IsAdicComplete (maximalIdeal (PowerSeries O')) (PowerSeries O') := ReciprocityTheory.P1.isAdicComplete_ps
  have : CharZero (PowerSeries O') := charZero_of_injective_ringHom (PowerSeries.C_injective (R := O'))
  have : CharZero R₁ := charZero_of_injective_ringHom hg
  letI := g.toAlgebra
  have : Module.Finite (PowerSeries O') R₁ := hfin
  have : IsLocalRing R₁ := T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := PowerSeries O') R₁
  have : IsNoetherianRing R₁ := IsNoetherianRing.of_finite (PowerSeries O') R₁
  have : FaithfulSMul (PowerSeries O') R₁ := (faithfulSMul_iff_algebraMap_injective _ _).2 hg
  have hloc : IsLocalHom (algebraMap (PowerSeries O') R₁) := inferInstance
  have hR' : ∀ S ∈ P, ∀ r : R₁, algebraMap R₁ (AlgebraicClosure (FractionRing R₁)) r ∈ S := fun S hS r => by
    rw [IsScalarTower.algebraMap_apply R₁ (FractionRing R₁)]
    exact hR S hS r
  have hinj : Function.Injective (algebraMap R₁ (AlgebraicClosure (FractionRing R₁))) := by
    rw [IsScalarTower.algebraMap_eq R₁ (FractionRing R₁)]
    exact (algebraMap (FractionRing R₁) _).injective.comp (IsFractionRing.injective R₁ _)
  have hnf : ¬ IsField R₁ := fun h => by
    have hX : ¬ IsUnit (PowerSeries.X : PowerSeries O') := PowerSeries.X_prime.not_isUnit
    refine hX (hloc.1 _ ?_)
    obtain ⟨b, hb⟩ := h.mul_inv_cancel ((map_ne_zero_iff g hg).2 PowerSeries.X_ne_zero)
    exact IsUnit.of_mul_eq_one b hb
  have hint : ∀ x, (∀ S ∈ P, x ∈ S) → IsIntegral R₁ x := fun x hx => by
    by_contra hn
    let L := IntermediateField.adjoin (FractionRing R₁) {x}
    have : FiniteDimensional (FractionRing R₁) L :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
    have : Algebra.EssFiniteType R₁ (FractionRing R₁) := .of_isLocalization _ (nonZeroDivisors R₁)
    have : Algebra.EssFiniteType R₁ L := .comp R₁ (FractionRing R₁) L
    let x' : L := ⟨x, IntermediateField.subset_adjoin _ _ rfl⟩
    have : IsScalarTower R₁ L (AlgebraicClosure (FractionRing R₁)) := .of_algebraMap_eq fun _ => rfl
    have hn' : ¬ IsIntegral R₁ x' := fun h => hn (h.map (IsScalarTower.toAlgHom R₁ L _))
    obtain ⟨W, _, h2, h3⟩ := exists_discreteValuationSubring_dominating_notMem (R := R₁) hn'
    obtain ⟨S, hS, h⟩ := exists_mem_of_dvr P hP L W
      ((localSubring_range_le_valuationSubring_iff _ _).1 h2).1
    exact h x' h3 (hx S hS)
  let L : IntermediateField (FractionRing R₁) (AlgebraicClosure (FractionRing R₁)) := ⊥
  obtain ⟨W, _, h2⟩ := exists_discreteValuationSubring_dominating R₁ (FractionRing R₁) L hnf
  obtain ⟨h2, h3⟩ := (localSubring_range_le_valuationSubring_iff _ _).1 h2
  obtain ⟨S₀, hS₀, h⟩ := exists_mem_of_dvr P hP L W h2
  refine ⟨S₀, hS₀, fun x hx hv S hS => ?_⟩
  have e : ∀ r, algebraMap (PowerSeries O') (AlgebraicClosure (FractionRing R₁)) r = algebraMap R₁ _ (g r) :=
    fun r => IsScalarTower.algebraMap_apply _ R₁ _ r
  have hi : IsIntegral (PowerSeries O') x⁻¹ := by
    refine isIntegral_inv S₀ (fun r => e r ▸ hR' S₀ hS₀ (g r)) (fun r hr => ?_)
      (isIntegral_trans x (hint x hx)) (hx S₀ hS₀) hv
    have h4 := h3 (g r) (fun hu => hr (hloc.1 r hu))
    rw [e]
    rw [ValuationSubring.mem_nonunits_iff_or] at h4 ⊢
    exact h4.imp (fun e => congrArg Subtype.val e) (fun e => h _ e)
  have h5 : x⁻¹ ∈ S := mem_of_isIntegral S (hR' S hS) hi.tower_top
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hv
  refine le_antisymm ((S.valuation_le_one_iff x).2 (hx S hS)) ?_
  have h6 := (S.valuation_le_one_iff _).2 h5
  rwa [map_inv₀, inv_le_one₀ (by simpa [Valuation.pos_iff] using hx0)] at h6

end GlobalTheory.CentredPlace
