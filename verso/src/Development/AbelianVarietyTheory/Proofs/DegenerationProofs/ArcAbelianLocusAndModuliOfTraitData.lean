import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcWitMemRangeJKOfMemRangeJ

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory
namespace ArcLocus

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

/- English proof (translation)
Introduce `h₁`. Take `⟨W⟩` from `(Y.hasArcData_iff a _ f u χ).1 h`. Establish `h₂` using `(abLocus_pullback abLocusOne Y.t.semi W.m.cart.1 _).1 h₁`. Establish `hmax : (IsLocalRing.maximalIdeal R ^ (0 + 1)).IsMaximal`. Rewrite using `[zero_add, pow_one]`.

Use `infer_instance`. Establish `hF : IsField (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1))` using `(Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax`. Choose the witnesses or unpack the hypotheses as in `⟨p, hp⟩ : IsLocalRing.closedPoint R ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (0 + 1)))) := by`. Rewrite using `[range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, zero_add, pow_one]`. Conclude with `le_refl (IsLocalRing.maximalIdeal R)`.

Set `g` to `W.P.U.gt 0`. Establish `m : Mono g.i` using `⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩`. Establish `hp' : thick R (IsLocalRing.maximalIdeal R) 0 p ∈ abLocus W.t.G`. Rewrite `h₂` using `[← hp]`. Conclude with `h₂`.

Establish `hs` using `ArcNotAbelian.subsingleton_of_mem_abLocus W.t.G W.t.semi _ hF _ p hp' W.P.D.toPre.X g.i g.i_hom`. Establish `hn : Nontrivial a.D₀.X` using `a.nontriv`. Conclude with `not_subsingleton _ (W.e.toEquiv.subsingleton)`.
-/
theorem closedPoint_notMem (Y : Model Xo c β) {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}
    (a : ArcIn D l β O' b) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (f : O' →+* R) (u : R)
    (χ : Sp R ⟶ Y.X) (h : Y.HasArcData a (IsLocalRing.maximalIdeal R) f u χ) :
    χ (IsLocalRing.closedPoint R) ∉ abLocus Y.t.G := by
  intro h₁
  obtain ⟨W⟩ := (Y.hasArcData_iff a _ f u χ).1 h
  have h₂ := (abLocus_pullback abLocusOne Y.t.semi W.m.cart.1 _).1 h₁
  have hmax : (IsLocalRing.maximalIdeal R ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1)) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  obtain ⟨p, hp⟩ : IsLocalRing.closedPoint R ∈ Set.range (PrimeSpectrum.comap
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (0 + 1)))) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, zero_add, pow_one]
    exact le_refl (IsLocalRing.maximalIdeal R)
  let g := W.P.U.gt 0
  have m : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have hp' : thick R (IsLocalRing.maximalIdeal R) 0 p ∈ abLocus W.t.G := by
    rw [← hp] at h₂; exact h₂
  have hs := ArcNotAbelian.subsingleton_of_mem_abLocus W.t.G W.t.semi _ hF _ p hp' W.P.D.toPre.X g.i g.i_hom
  have hn : Nontrivial a.D₀.X := a.nontriv
  exact not_subsingleton _ (W.e.toEquiv.subsingleton)

/- English proof (translation)
Take `⟨W, _, _, _, _, φ, h1, h2⟩` from `exists_complete_discreteValuationRing_of_prime_lt (⊥ : Ideal R) x.asIdeal (bot_lt_iff_ne_bot.2 hx)`. Establish `hφ : Function.Injective φ` using `(RingHom.injective_iff_ker_eq_bot φ).2 h1`. Establish `hφ' : Function.Injective ((algebraMap W (FractionRing W)).comp φ)` using `(IsFractionRing.injective W (FractionRing W)).comp hφ`. Conclude with `⟨W, inferInstance, inferInstance, inferInstance, φ, IsFractionRing.lift hφ', ⟨inferInstance, inferInstance, charZero_of_injective_ringHom hφ⟩, fun r => IsFractionRing.lift_algebraMap hφ' r, h2⟩`.
-/
theorem exists_trait (R : Type) [CommRing R] [IsDomain R] [CharZero R] [IsNoetherianRing R] (x : PrimeSpectrum R)
    (hx : x.asIdeal ≠ ⊥) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W)
      (gam : FractionRing R →+* FractionRing W), CDvr W ∧ (∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) ∧
      (IsLocalRing.maximalIdeal W).comap φ = x.asIdeal := by
  obtain ⟨W, _, _, _, _, φ, h1, h2⟩ :=
    exists_complete_discreteValuationRing_of_prime_lt (⊥ : Ideal R) x.asIdeal (bot_lt_iff_ne_bot.2 hx)
  have hφ : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 h1
  have hφ' : Function.Injective ((algebraMap W (FractionRing W)).comp φ) :=
    (IsFractionRing.injective W (FractionRing W)).comp hφ
  exact ⟨W, inferInstance, inferInstance, inferInstance, φ, IsFractionRing.lift hφ',
    ⟨inferInstance, inferInstance, charZero_of_injective_ringHom hφ⟩,
    fun r => IsFractionRing.lift_algebraMap hφ' r, h2⟩

/- English proof (translation)
Establish `hz : Y.jQ p ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G`. Rewrite using `[Y.ab_gen]`. Conclude with `⟨_, rfl⟩`. Conclude with `hz`.
-/
theorem j_mem (Y : Model Xo c β) (p : Xo.XF c) : Y.j p ∈ abLocus Y.t.G := by
  have hz : Y.jQ p ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
    rw [Y.ab_gen]; exact ⟨_, rfl⟩
  exact hz

/- English proof (translation)
Establish `h₁ : z ∈ Set.range (pullback.fst Y.s (spMap β))`. Rewrite using `[Scheme.Pullback.range_fst, Set.mem_preimage, hp]`. Establish `: Y.j p ∈ Set.range (pullback.fst Y.s (spMap β))` using `⟨Y.jQ p, rfl⟩`. Rewrite `this` using `[Scheme.Pullback.range_fst]`. Then use the resulting hypothesis. Take `⟨w, rfl⟩` from `h₁`.

Establish `h₂ : w ∈ Set.range Y.jQ` using `by rw [← Y.ab_gen]; exact hz`. Take `⟨q, rfl⟩` from `h₂`. Conclude with `⟨q, rfl⟩`.
-/
theorem mem_range_j (Y : Model Xo c β) (z : Y.X) (hz : z ∈ abLocus Y.t.G) (p : Xo.XF c)
    (hp : Y.s z = Y.s (Y.j p)) : z ∈ Set.range Y.j := by
  have h₁ : z ∈ Set.range (pullback.fst Y.s (spMap β)) := by
    rw [Scheme.Pullback.range_fst, Set.mem_preimage, hp]
    have : Y.j p ∈ Set.range (pullback.fst Y.s (spMap β)) := ⟨Y.jQ p, rfl⟩
    rwa [Scheme.Pullback.range_fst] at this
  obtain ⟨w, rfl⟩ := h₁
  have h₂ : w ∈ Set.range Y.jQ := by rw [← Y.ab_gen]; exact hz
  obtain ⟨q, rfl⟩ := h₂
  exact ⟨q, rfl⟩

/- English proof (translation)
Use `⟨(⊥ : PrimeSpectrum (FractionRing R)), PrimeSpectrum.ext ?_⟩` and prove the remaining obligations. Conclude with `(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))`.
-/
theorem exists_jK_eq_bot (R : Type) [CommRing R] [IsDomain R] :
    ∃ pt : Sp (FractionRing R), jK R pt = (⊥ : PrimeSpectrum R) := by
  refine ⟨(⊥ : PrimeSpectrum (FractionRing R)), PrimeSpectrum.ext ?_⟩
  exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))

end ArcLocus

open ArcLocus in

/- English proof (translation)
Introduce `_ _ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b a ϖ hb y χ hχ hT`. Establish `hN : IsNoetherianRing O'`. Break down `hb with h | h` into its components or cases. Use `letI := h.1.toField`. Use `infer_instance`.

Use `h.1` as an intermediate fact. Use `infer_instance`. Establish `hc : CharZero (PowerSeries O')` using `charZero_of_injective_ringHom (PowerSeries.C_injective (R := O'))`. Take `⟨pt, hpt⟩` from `exists_jK_eq_bot (PowerSeries O')`. Establish `h0 : χ (⊥ : PrimeSpectrum (PowerSeries O')) = Y.j (y pt)`.

Rewrite using `[← hpt, ← Scheme.Hom.comp_apply, hχ, Scheme.Hom.comp_apply]`. Establish `h1 : χ ≫ Y.s = spMap (PowerSeries.C (R` using `O')) ≫ spMap b := by`. Establish `hd : IsDominant (jK (PowerSeries O'))`. Prove the components needed by the constructor for the conclusion. Conclude with `(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap (PowerSeries O') (FractionRing (PowerSeries O')))).2 (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective (PowerSeries O') _)]; exact bot_le)`.

Use `ext_of_isDominant (jK (PowerSeries O')) ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, hχ, Category.assoc, hT.1]`. Establish `: spMap (RingHom.id (PowerSeries O')) = 𝟙 _` using `Spec.map_id _`. Rewrite using `[this, Category.id_comp]`. Establish `h2 : ∀ x : Sp (PowerSeries O'), χ x ∈ abLocus Y.t.G ↔ PowerSeries.X ∉ x.asIdeal`.

Introduce `x`. Distinguish the cases in `hx : x.asIdeal = ⊥`. Establish `e : x = (⊥ : PrimeSpectrum (PowerSeries O'))` using `PrimeSpectrum.ext hx`. Use `iff_of_true ?_ ?_` and prove the remaining obligations. Rewrite using `[e, h0]`.

Conclude with `j_mem Y _`. Rewrite using `[hx]`. Conclude with `PowerSeries.X_ne_zero`. Take `⟨W, _, _, _, φ, gam, hW, hg, hφ⟩` from `exists_trait (PowerSeries O') x hx`. Establish `key : spMap gam ≫ jK (PowerSeries O') = jK W ≫ spMap φ` using `by show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _`.

Rewrite using `[← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Conclude with `RingHom.ext hg`. Establish `ht` using `hT.2 W hW φ gam hg (spMap φ ≫ χ) (by rw [← hχ, ← Category.assoc, key, Category.assoc])`. Establish `hu : PowerSeries.X ∉ x.asIdeal ↔ IsUnit (φ PowerSeries.X)`.

Rewrite using `[← hφ, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]`. Establish `hcl : spMap φ (IsLocalRing.closedPoint W) = x` using `PrimeSpectrum.ext hφ`. Rewrite using `[hu]`. Use `⟨fun hab => ?_, fun h => ht.1 h ⟨IsLocalRing.closedPoint W, (Scheme.Hom.comp_apply _ _ _).trans (congrArg χ hcl)⟩⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`.

Take `⟨W', _, _, _, io, -, -, hfin, hA⟩` from `ht.2 h`. Use `closedPoint_notMem Y a _ _ _ hA ?_` and prove the remaining obligations. Establish `hcl' : spMap io (IsLocalRing.closedPoint W') = IsLocalRing.closedPoint W`. Use `PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal ?_)` and prove the remaining obligations. Conclude with `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' io hfin.to_isIntegral (IsLocalRing.maximalIdeal W')`.

Establish `e : (spMap io ≫ spMap φ ≫ χ) (IsLocalRing.closedPoint W') = χ x` using `(Scheme.Hom.comp_apply _ _ _).trans ((congrArg (spMap φ ≫ χ) hcl').trans ((Scheme.Hom.comp_apply _ _ _).trans (congrArg χ hcl)))`. Rewrite using `[e]`. Conclude with `hab`. Use `⟨h1, h2, fun x hx => mem_range_j Y _ ((h2 x).2 fun h => hx (Ideal.mul_mem_left _ _ h)) (y pt) ?_⟩` and prove the remaining obligations. Establish `hC : ∀ z : Sp (PowerSeries O'), PowerSeries.C ϖ * PowerSeries.X ∉ z.asIdeal → spMap (PowerSeries.C (R` using `O')) z = (⊥ : PrimeSpectrum O') := by`.

Introduce `z hz`. Use `PrimeSpectrum.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `z.asIdeal.comap (PowerSeries.C (R := O')) = ⊥`. Establish `hzp` using `z.isPrime`. Break down `hb with h | h` into its components or cases.

Use `letI := h.1.toField`. Conclude with `Ideal.eq_bot_of_prime _`. Use `h.1` as an intermediate fact. Assume the negation of the conclusion as `hne`. Establish `hm` using `IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hne inferInstance)`.

Establish `: ϖ ∈ z.asIdeal.comap (PowerSeries.C (R` using `O')) := by`. Rewrite using `[hm]`. Conclude with `h.2.1.not_isUnit`. Conclude with `hz (Ideal.mul_mem_right _ _ this)`. Establish `hb0 : spMap (PowerSeries.C (R` using `O')) (⊥ : PrimeSpectrum (PowerSeries O')) = (⊥ : PrimeSpectrum O') := PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot _).1 (PowerSeries.C_injective (R := O')))`.

Establish `h3 : ∀ z : Sp (PowerSeries O'), Y.s (χ z) = spMap b (spMap (PowerSeries.C (R` using `O')) z) := fun z => by`. Rewrite using `[← Scheme.Hom.comp_apply, h1, Scheme.Hom.comp_apply]`. Rewrite using `[← h0, h3, hC x hx]`. Conclude with `((h3 _).trans (congrArg (spMap b) hb0)).symm`.
-/
theorem arc_abLocus_of_traitData : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (ϖ : O'), ArcBase O' ϖ → ∀ (y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c) (χ : Sp (PowerSeries O') ⟶ Y.X), jK _ ≫ χ = y ≫ Y.j → TraitData Y a (RingHom.id _) y → χ ≫ Y.s = spMap (PowerSeries.C (R := O')) ≫ spMap b ∧ (∀ x : Sp (PowerSeries O'), χ x ∈ abLocus Y.t.G ↔ PowerSeries.X ∉ x.asIdeal) ∧ ∀ x : Sp (PowerSeries O'), PowerSeries.C ϖ * PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j := by
  intro _ _ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b a ϖ hb y χ hχ hT
  have hN : IsNoetherianRing O' := by
    rcases hb with h | h
    · letI := h.1.toField; infer_instance
    · have := h.1; infer_instance
  have hc : CharZero (PowerSeries O') := charZero_of_injective_ringHom (PowerSeries.C_injective (R := O'))
  obtain ⟨pt, hpt⟩ := exists_jK_eq_bot (PowerSeries O')
  have h0 : χ (⊥ : PrimeSpectrum (PowerSeries O')) = Y.j (y pt) := by
    rw [← hpt, ← Scheme.Hom.comp_apply, hχ, Scheme.Hom.comp_apply]
  have h1 : χ ≫ Y.s = spMap (PowerSeries.C (R := O')) ≫ spMap b := by
    have hd : IsDominant (jK (PowerSeries O')) := by
      constructor
      exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap (PowerSeries O') (FractionRing (PowerSeries O')))).2
        (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective (PowerSeries O') _)]; exact bot_le)
    refine ext_of_isDominant (jK (PowerSeries O')) ?_
    rw [← Category.assoc, hχ, Category.assoc, hT.1]
    have : spMap (RingHom.id (PowerSeries O')) = 𝟙 _ := Spec.map_id _
    rw [this, Category.id_comp]
  have h2 : ∀ x : Sp (PowerSeries O'), χ x ∈ abLocus Y.t.G ↔ PowerSeries.X ∉ x.asIdeal := by
    intro x
    by_cases hx : x.asIdeal = ⊥
    · have e : x = (⊥ : PrimeSpectrum (PowerSeries O')) := PrimeSpectrum.ext hx
      refine iff_of_true ?_ ?_
      · rw [e, h0]; exact j_mem Y _
      · rw [hx]; exact PowerSeries.X_ne_zero
    obtain ⟨W, _, _, _, φ, gam, hW, hg, hφ⟩ := exists_trait (PowerSeries O') x hx
    have key : spMap gam ≫ jK (PowerSeries O') = jK W ≫ spMap φ := by
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact RingHom.ext hg
    have ht := hT.2 W hW φ gam hg (spMap φ ≫ χ) (by rw [← hχ, ← Category.assoc, key, Category.assoc])
    have hu : PowerSeries.X ∉ x.asIdeal ↔ IsUnit (φ PowerSeries.X) := by
      rw [← hφ, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    have hcl : spMap φ (IsLocalRing.closedPoint W) = x := PrimeSpectrum.ext hφ
    rw [hu]
    refine ⟨fun hab => ?_, fun h => ht.1 h ⟨IsLocalRing.closedPoint W, (Scheme.Hom.comp_apply _ _ _).trans (congrArg χ hcl)⟩⟩
    by_contra h
    obtain ⟨W', _, _, _, io, -, -, hfin, hA⟩ := ht.2 h
    refine closedPoint_notMem Y a _ _ _ hA ?_
    have hcl' : spMap io (IsLocalRing.closedPoint W') = IsLocalRing.closedPoint W := by
      refine PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal ?_)
      exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' io hfin.to_isIntegral (IsLocalRing.maximalIdeal W')
    have e : (spMap io ≫ spMap φ ≫ χ) (IsLocalRing.closedPoint W') = χ x :=
      (Scheme.Hom.comp_apply _ _ _).trans ((congrArg (spMap φ ≫ χ) hcl').trans
        ((Scheme.Hom.comp_apply _ _ _).trans (congrArg χ hcl)))
    rw [e]
    exact hab
  refine ⟨h1, h2, fun x hx => mem_range_j Y _ ((h2 x).2 fun h => hx (Ideal.mul_mem_left _ _ h)) (y pt) ?_⟩
  have hC : ∀ z : Sp (PowerSeries O'), PowerSeries.C ϖ * PowerSeries.X ∉ z.asIdeal →
      spMap (PowerSeries.C (R := O')) z = (⊥ : PrimeSpectrum O') := by
    intro z hz
    refine PrimeSpectrum.ext ?_
    change z.asIdeal.comap (PowerSeries.C (R := O')) = ⊥
    have hzp := z.isPrime
    rcases hb with h | h
    · letI := h.1.toField
      exact Ideal.eq_bot_of_prime _
    · have := h.1
      by_contra hne
      have hm := IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hne inferInstance)
      have : ϖ ∈ z.asIdeal.comap (PowerSeries.C (R := O')) := by
        rw [hm]; exact h.2.1.not_isUnit
      exact hz (Ideal.mul_mem_right _ _ this)
  have hb0 : spMap (PowerSeries.C (R := O')) (⊥ : PrimeSpectrum (PowerSeries O')) = (⊥ : PrimeSpectrum O') :=
    PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot _).1 (PowerSeries.C_injective (R := O')))
  have h3 : ∀ z : Sp (PowerSeries O'), Y.s (χ z) = spMap b (spMap (PowerSeries.C (R := O')) z) := fun z => by
    rw [← Scheme.Hom.comp_apply, h1, Scheme.Hom.comp_apply]
  rw [← h0, h3, hC x hx]
  exact ((h3 _).trans (congrArg (spMap b) hb0)).symm

end GlobalTheory
