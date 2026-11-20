import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPAdicArcBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowerSeriesArcAbelianLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelPointsEqOfSameDegenerationData
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AdmissibleBasePowerSeriesSpanX
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPeriod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPolarization
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratorExtendsPower
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdealAlongDvrArcs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratorExtendsTensor
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericSectionExtendsNormal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegrallyClosedPowerSeries

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.AnyChartExtend

/- English proof (translation)
Break down `h with ⟨hF, -⟩ | ⟨hD, -, -⟩` into its components or cases. Use `letI := hF.toField`. Conclude with `⟨inferInstance, inferInstance, GlobalTheory.PowerSeriesNormal.isIntegrallyClosed_powerSeries O'⟩`. Conclude with `⟨inferInstance, inferInstance, GlobalTheory.PowerSeriesNormal.isIntegrallyClosed_powerSeries O'⟩`.
-/
theorem powerSeries_props (O' : Type) [CommRing O'] [IsDomain O'] (ϖ : O') (h : IsArcBase O' ϖ) :
    ∃ (_ : IsLocalRing (PowerSeries O')), IsNoetherianRing (PowerSeries O') ∧ IsIntegrallyClosed (PowerSeries O') := by
  rcases h with ⟨hF, -⟩ | ⟨hD, -, -⟩
  · letI := hF.toField
    exact ⟨inferInstance, inferInstance, GlobalTheory.PowerSeriesNormal.isIntegrallyClosed_powerSeries O'⟩
  · exact ⟨inferInstance, inferInstance, GlobalTheory.PowerSeriesNormal.isIntegrallyClosed_powerSeries O'⟩

/- English proof (translation)
Use `show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`. Use `congr 1`. Conclude with `CommRingCat.hom_ext (RingHom.ext h)`.
-/
theorem spMap_jK' {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {g : R →+* R'}
    {gam : FractionRing R →+* FractionRing R'} (h : ∀ r, gam (algebraMap R _ r) = algebraMap R' _ (g r)) :
    spMap gam ≫ Out.jK R = Out.jK R' ≫ spMap g := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext h)

open GlobalTheory.ArcOrder in

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c p W hp hW Z Y bV hbV φ m BD hφ hpol O' _ _ _ b' ϖ a χ₀ hbase hchart x₀ hx₀`. Take `⟨hL, hL₂, hL₃, hL₄, hL₅, hL₆⟩` from `GlobalTheory.allSixLaws`. Take `⟨W₀⟩` from `(Y.hasArcData_iff (GlobalTheory.PolArc.moveV bV hbV b' a) _ _ _ _).1 hchart.2.2.2`. Establish `hR : AdmBase (PowerSeries O') (Ideal.span {PowerSeries.X})`. Break down `hbase with ⟨hf, -⟩ | ⟨hd, -, -⟩` into its components or cases.

Use `letI := hf.toField`. Conclude with `GlobalTheory.ArcPull.admissibleBase_powerSeries_span_X O'`. Conclude with `GlobalTheory.ArcPull.admissibleBase_powerSeries_span_X O'`. Use `haveI : Module.Finite (𝓞 E) (GlobalTheory.PolArc.moveV bV hbV b' a).D₀.X := Module.Finite.equiv W₀.e.symm`. Take `⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = φ.eval (GlobalTheory.PolArc.moveV bV hbV b' a).D₀.X (fun p q => ((GlobalTheory.PolArc.moveV bV hbV b' a).be p q : ℝ))` from `⟨_, rfl⟩`.

Establish `inj : ∀ (V : Type) [CommRing V] [IsDomain V] (ψ : PowerSeries O' →+* V) (gam : FractionRing (PowerSeries O') →+* FractionRing V), (∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap V _ (ψ r)) → Function.Injective ψ` using `fun V _ _ ψ gam hg x y e => IsFractionRing.injective (PowerSeries O') (FractionRing (PowerSeries O')) (gam.injective (by rw [hg, hg, e]))`. Establish `hYc : ∀ (V : Type) [CommRing V] [IsDomain V] (ψ : PowerSeries O' →+* V) (gam : FractionRing (PowerSeries O') →+* FractionRing V), (∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap V _ (ψ r)) → jK V ≫ spMap ψ ≫ χ₀ = (spMap gam ≫ x₀) ≫ Y.j` using `fun V _ _ ψ gam hg => by`. Rewrite using `[← Category.assoc, ← ArcExtends.spMap_jK hg, Category.assoc, Category.assoc, hx₀]`. Establish `key : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (ψ : PowerSeries O' →+* V) (gam : FractionRing (PowerSeries O') →+* FractionRing V), (∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap V _ (ψ r)) → ∀ χ : Sp V ⟶ Z.X, spMap gam ≫ x₀ ≫ Z.j = jK V ≫ χ → …`. Introduce `V _ _ _ hV ψ gam hg χ hχ ϖ' hϖ' v k hk hu`.

Use `hV.1` as an intermediate fact. Establish `hψ` using `inj V ψ gam hg`. Establish `hsub : (Ideal.span {(PowerSeries.X : PowerSeries O')}).map ψ ≤ maximalIdeal V`. Rewrite using `[Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem, hu]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ ((mem_maximalIdeal _).2 hϖ'.not_isUnit) _ (Nat.pos_of_ne_zero hk))`.

Take `⟨A, -⟩` from `ArcWit.baseChange hL₃.cubePull hL.polBaseChange hL₄.unifBaseChange hL₅ (qkPullExists hL.globalFns) polOActPull hR (GlobalTheory.ArcPointDescent.admissibleBase_maximalIdeal_completeDVR hV) W₀ ψ hψ hsub`. Rewrite using `[hc₀]`. Conclude with `order_of_arcWit Z Y BD φ hφ hpol.1 hV (f := ψ.comp PowerSeries.C) (show Function.Injective (ψ.comp PowerSeries.C) from hψ.comp PowerSeries.C_injective) A (spMap gam ≫ x₀) χ (by rw [Category.assoc]; exact hχ.symm) (hYc V ψ gam hg) hϖ' v k hu`. Establish `hK : CharZero (FractionRing O')` using `IsFractionRing.charZero_of_isFractionRing O'`. Take `⟨ψ₁, hψ₁⟩ : ∃ ψ₁ : PowerSeries O' →+* PowerSeries (FractionRing O'), ψ₁ = PowerSeries.map (algebraMap O' (FractionRing O'))` from `⟨_, rfl⟩`.

Establish `hψi : Function.Injective ψ₁` using `hψ₁ ▸ PowerSeries.map_injective _ (IsFractionRing.injective O' _)`. Establish `j : Function.Injective ((algebraMap (PowerSeries (FractionRing O')) (FractionRing (PowerSeries (FractionRing O')))).comp ψ₁)` using `(IsFractionRing.injective _ _).comp hψi`. Take `⟨gam₁, hg₁⟩ : ∃ gam₁ : FractionRing (PowerSeries O') →+* FractionRing (PowerSeries (FractionRing O')), ∀ r, gam₁ (algebraMap (PowerSeries O') _ r) = algebraMap (PowerSeries (FractionRing O')) _ (ψ₁ r)` from `⟨IsFractionRing.lift j, fun r => IsFractionRing.lift_algebraMap j r⟩`. Establish `hV₁ : CDvr (PowerSeries (FractionRing O'))` using `GlobalTheory.ArcPointDescent.cDvr_powerSeries _`. Use `isProper_toroidalModel_structureMap Z` as an intermediate fact.

Establish `hjZ : Z.j ≫ Z.s = pullback.snd _ _ ≫ spMap (algebraMap (𝓞 c.F) c.F)`. Rewrite using `[Model.j, Category.assoc, pullback.condition, ← Category.assoc, Z.jQ_over]`. Establish `hjY : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap (c.V W).subtype`. Rewrite using `[Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]`. Establish `hb : spMap (algebraMap (𝓞 c.F) c.F) = spMap (c.V W).subtype ≫ spMap bV`.

Rewrite using `[← spMap_comp]`. Conclude with `congrArg spMap (RingHom.ext fun x => (hbV x).symm)`. Establish `hjj : Z.j ≫ Z.s = Y.j ≫ Y.s ≫ spMap bV`. Rewrite using `[hjZ, hb, ← Category.assoc Y.j, hjY, Category.assoc]`. Establish `hs : x₀ ≫ Z.j ≫ Z.s = jK (PowerSeries O') ≫ spMap (PowerSeries.C (R` using `O')) ≫ spMap b' ≫ spMap bV := by`.

Rewrite using `[hjj, ← Category.assoc x₀, ← hx₀, Category.assoc, ← Category.assoc χ₀, hchart.1, Category.assoc]`. Take `⟨χ₁, hχ₁, -⟩` from `val_exists Z.s (spMap gam₁ ≫ x₀ ≫ Z.j) (spMap ψ₁ ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b' ≫ spMap bV) (by`. Rewrite using `[Category.assoc, Category.assoc, hs, ← Category.assoc, ArcExtends.spMap_jK hg₁, Category.assoc])`. Take `⟨n, hn, -⟩` from `key _ hV₁ ψ₁ gam₁ hg₁ χ₁ hχ₁.symm PowerSeries.X PowerSeries.X_prime.irreducible 1 1 one_ne_zero (by simp [hψ₁])`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Introduce `V _ _ _ hV ψ gam hg χ hχ`. Use `hV.1` as an intermediate fact. Establish `hψ` using `inj V ψ gam hg`. Establish `hZc : jK V ≫ χ = (spMap gam ≫ x₀) ≫ Z.j` using `by rw [Category.assoc]; exact hχ.symm`. Distinguish the cases in `hU : IsUnit (ψ PowerSeries.X)`.

Take `⟨t₁, ⟨n₁⟩⟩` from `GlobalTheory.TraitOrder.exists_pull (spMap ψ ≫ χ₀) Y.t`. Take `⟨mZ⟩` from `exists_sabMap_of_generic Z Y hV (spMap gam ≫ x₀) χ (spMap ψ ≫ χ₀) hZc (hYc V ψ gam hg) n₁`. Establish `hab : ∀ p, χ p ∈ abLocus Z.t.G` using `fun p => by`. Use `(abLocus_pullback abLocusOne Z.t.semi mZ.cart.1 p).2 ((abLocus_pullback abLocusOne Y.t.semi n₁.cart.1 p).1 ?_)` and prove the remaining obligations. Use `(congrArg (· ∈ abLocus Y.t.G) (Scheme.Hom.comp_apply (spMap ψ) χ₀ p)).mpr ((hchart.2.1 _).2 fun hX => ?_)` and prove the remaining obligations.

Establish `h' : ψ PowerSeries.X ∈ p.asIdeal` using `hX`. Conclude with `p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' hU)`. Rewrite using `[idlAlong_eq_top_of_abelian Z BD φ hpol.1 hV (spMap gam ≫ x₀) χ hZc hab]`. Conclude with `(Ideal.span_singleton_eq_top.2 (hU.pow n)).symm`. Take `⟨ϖ', hϖ'⟩` from `IsDiscreteValuationRing.exists_irreducible V`.

Establish `hne : ψ PowerSeries.X ≠ 0` using `fun h => PowerSeries.X_ne_zero (hψ (h.trans (map_zero ψ).symm))`. Take `⟨k, v, hk⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ'`. Establish `hk0 : k ≠ 0`. Introduce and unpack `rfl`. Conclude with `hU (by simp [hk])`.

Take `⟨n₂, hn₂, hid⟩` from `key V hV ψ gam hg χ hχ ϖ' hϖ' v k hk0 hk`. Establish `e : n₂ = k * n`. Establish `: (n₂ : ℝ) = k * n` using `by rw [hn₂, hn]; simp`. Conclude with `this` after adjusting the coercions. Rewrite using `[hid, e, hk, mul_pow, pow_mul, Ideal.span_singleton_mul_left_unit (v.isUnit.pow n)]`.
-/
theorem order : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype) (bV : 𝓞 c.F →+* c.V W)
    (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F)) (φ : InvFun (𝓞 E)) (m : ℕ) (BD : GlobalTheory.EffCartierData Z.X),
      (∀ (n : ℕ) (k : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ), φ.toFun n (fun a b => k * B a b) = k * φ.toFun n B) →
      IsPol φ m Z BD →
      ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b' : c.V W →+* O') (ϖ : O')
        (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' (b'.comp bV)) (χ₀ : Sp (PowerSeries O') ⟶ Y.X),
        IsArcBase O' ϖ → IsArcChart Y (GlobalTheory.PolArc.moveV bV hbV b' a) ϖ χ₀ →
        ∀ x₀ : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, Out.jK (PowerSeries O') ≫ χ₀ = x₀ ≫ Y.j →
        ∃ n : ℕ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V →
    ∀ (ψ : PowerSeries O' →+* V) (gam : FractionRing (PowerSeries O') →+* FractionRing V),
    (∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap V _ (ψ r)) →
    ∀ χ : Sp V ⟶ Z.X, spMap gam ≫ x₀ ≫ Z.j = Out.jK V ≫ χ → GlobalTheory.LocM.idlAlong BD.idealSheaf χ = Ideal.span {ψ PowerSeries.X ^ n} := by
  intro E _ _ _ H D l Xo c p W hp hW Z Y bV hbV φ m BD hφ hpol O' _ _ _ b' ϖ a χ₀ hbase hchart x₀ hx₀
  obtain ⟨hL, hL₂, hL₃, hL₄, hL₅, hL₆⟩ := GlobalTheory.allSixLaws
  obtain ⟨W₀⟩ := (Y.hasArcData_iff (GlobalTheory.PolArc.moveV bV hbV b' a) _ _ _ _).1 hchart.2.2.2
  have hR : AdmBase (PowerSeries O') (Ideal.span {PowerSeries.X}) := by
    rcases hbase with ⟨hf, -⟩ | ⟨hd, -, -⟩
    · letI := hf.toField
      exact GlobalTheory.ArcPull.admissibleBase_powerSeries_span_X O'
    · exact GlobalTheory.ArcPull.admissibleBase_powerSeries_span_X O'
  haveI : Module.Finite (𝓞 E) (GlobalTheory.PolArc.moveV bV hbV b' a).D₀.X := Module.Finite.equiv W₀.e.symm
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = φ.eval (GlobalTheory.PolArc.moveV bV hbV b' a).D₀.X
      (fun p q => ((GlobalTheory.PolArc.moveV bV hbV b' a).be p q : ℝ)) := ⟨_, rfl⟩
  have inj : ∀ (V : Type) [CommRing V] [IsDomain V] (ψ : PowerSeries O' →+* V)
      (gam : FractionRing (PowerSeries O') →+* FractionRing V),
      (∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap V _ (ψ r)) → Function.Injective ψ :=
    fun V _ _ ψ gam hg x y e => IsFractionRing.injective (PowerSeries O') (FractionRing (PowerSeries O'))
      (gam.injective (by rw [hg, hg, e]))
  have hYc : ∀ (V : Type) [CommRing V] [IsDomain V] (ψ : PowerSeries O' →+* V)
      (gam : FractionRing (PowerSeries O') →+* FractionRing V),
      (∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap V _ (ψ r)) →
      jK V ≫ spMap ψ ≫ χ₀ = (spMap gam ≫ x₀) ≫ Y.j := fun V _ _ ψ gam hg => by
    rw [← Category.assoc, ← ArcExtends.spMap_jK hg, Category.assoc, Category.assoc, hx₀]
  have key : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (ψ : PowerSeries O' →+* V)
      (gam : FractionRing (PowerSeries O') →+* FractionRing V),
      (∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap V _ (ψ r)) →
      ∀ χ : Sp V ⟶ Z.X, spMap gam ≫ x₀ ≫ Z.j = jK V ≫ χ → ∀ ϖ' : V, Irreducible ϖ' → ∀ (v : Vˣ) (k : ℕ), k ≠ 0 →
      ψ PowerSeries.X = v * ϖ' ^ k →
      ∃ n : ℕ, (n : ℝ) = k * c₀ ∧ GlobalTheory.LocM.idlAlong BD.idealSheaf χ = Ideal.span {ϖ' ^ n} := by
    intro V _ _ _ hV ψ gam hg χ hχ ϖ' hϖ' v k hk hu
    have := hV.1
    have hψ := inj V ψ gam hg
    have hsub : (Ideal.span {(PowerSeries.X : PowerSeries O')}).map ψ ≤ maximalIdeal V := by
      rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem, hu]
      exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ ((mem_maximalIdeal _).2 hϖ'.not_isUnit) _ (Nat.pos_of_ne_zero hk))
    obtain ⟨A, -⟩ := ArcWit.baseChange hL₃.cubePull hL.polBaseChange hL₄.unifBaseChange hL₅ (qkPullExists hL.globalFns)
      polOActPull hR (GlobalTheory.ArcPointDescent.admissibleBase_maximalIdeal_completeDVR hV) W₀ ψ hψ hsub
    rw [hc₀]
    exact order_of_arcWit Z Y BD φ hφ hpol.1 hV (f := ψ.comp PowerSeries.C)
      (show Function.Injective (ψ.comp PowerSeries.C) from hψ.comp PowerSeries.C_injective) A (spMap gam ≫ x₀) χ
      (by rw [Category.assoc]; exact hχ.symm) (hYc V ψ gam hg) hϖ' v k hu

  have hK : CharZero (FractionRing O') := IsFractionRing.charZero_of_isFractionRing O'
  obtain ⟨ψ₁, hψ₁⟩ : ∃ ψ₁ : PowerSeries O' →+* PowerSeries (FractionRing O'),
      ψ₁ = PowerSeries.map (algebraMap O' (FractionRing O')) := ⟨_, rfl⟩
  have hψi : Function.Injective ψ₁ := hψ₁ ▸ PowerSeries.map_injective _ (IsFractionRing.injective O' _)
  have j : Function.Injective ((algebraMap (PowerSeries (FractionRing O'))
      (FractionRing (PowerSeries (FractionRing O')))).comp ψ₁) := (IsFractionRing.injective _ _).comp hψi
  obtain ⟨gam₁, hg₁⟩ : ∃ gam₁ : FractionRing (PowerSeries O') →+* FractionRing (PowerSeries (FractionRing O')),
      ∀ r, gam₁ (algebraMap (PowerSeries O') _ r) = algebraMap (PowerSeries (FractionRing O')) _ (ψ₁ r) :=
    ⟨IsFractionRing.lift j, fun r => IsFractionRing.lift_algebraMap j r⟩
  have hV₁ : CDvr (PowerSeries (FractionRing O')) := GlobalTheory.ArcPointDescent.cDvr_powerSeries _
  have := isProper_toroidalModel_structureMap Z
  have hjZ : Z.j ≫ Z.s = pullback.snd _ _ ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Z.jQ_over]
  have hjY : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap (c.V W).subtype := by
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
  have hb : spMap (algebraMap (𝓞 c.F) c.F) = spMap (c.V W).subtype ≫ spMap bV := by
    rw [← spMap_comp]
    exact congrArg spMap (RingHom.ext fun x => (hbV x).symm)
  have hjj : Z.j ≫ Z.s = Y.j ≫ Y.s ≫ spMap bV := by
    rw [hjZ, hb, ← Category.assoc Y.j, hjY, Category.assoc]
  have hs : x₀ ≫ Z.j ≫ Z.s = jK (PowerSeries O') ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b' ≫ spMap bV := by
    rw [hjj, ← Category.assoc x₀, ← hx₀, Category.assoc, ← Category.assoc χ₀, hchart.1, Category.assoc]
  obtain ⟨χ₁, hχ₁, -⟩ := val_exists Z.s (spMap gam₁ ≫ x₀ ≫ Z.j)
    (spMap ψ₁ ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b' ≫ spMap bV) (by
      rw [Category.assoc, Category.assoc, hs, ← Category.assoc, ArcExtends.spMap_jK hg₁, Category.assoc])
  obtain ⟨n, hn, -⟩ := key _ hV₁ ψ₁ gam₁ hg₁ χ₁ hχ₁.symm PowerSeries.X PowerSeries.X_prime.irreducible 1 1 one_ne_zero
    (by simp [hψ₁])
  refine ⟨n, ?_⟩
  intro V _ _ _ hV ψ gam hg χ hχ
  have := hV.1
  have hψ := inj V ψ gam hg
  have hZc : jK V ≫ χ = (spMap gam ≫ x₀) ≫ Z.j := by rw [Category.assoc]; exact hχ.symm
  by_cases hU : IsUnit (ψ PowerSeries.X)
  · obtain ⟨t₁, ⟨n₁⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap ψ ≫ χ₀) Y.t
    obtain ⟨mZ⟩ := exists_sabMap_of_generic Z Y hV (spMap gam ≫ x₀) χ (spMap ψ ≫ χ₀) hZc (hYc V ψ gam hg) n₁
    have hab : ∀ p, χ p ∈ abLocus Z.t.G := fun p => by
      refine (abLocus_pullback abLocusOne Z.t.semi mZ.cart.1 p).2 ((abLocus_pullback abLocusOne Y.t.semi n₁.cart.1 p).1 ?_)
      refine (congrArg (· ∈ abLocus Y.t.G) (Scheme.Hom.comp_apply (spMap ψ) χ₀ p)).mpr ((hchart.2.1 _).2 fun hX => ?_)
      have h' : ψ PowerSeries.X ∈ p.asIdeal := hX
      exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' hU)
    rw [idlAlong_eq_top_of_abelian Z BD φ hpol.1 hV (spMap gam ≫ x₀) χ hZc hab]
    exact (Ideal.span_singleton_eq_top.2 (hU.pow n)).symm
  · obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible V
    have hne : ψ PowerSeries.X ≠ 0 := fun h => PowerSeries.X_ne_zero (hψ (h.trans (map_zero ψ).symm))
    obtain ⟨k, v, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ'
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hU (by simp [hk])
    obtain ⟨n₂, hn₂, hid⟩ := key V hV ψ gam hg χ hχ ϖ' hϖ' v k hk0 hk
    have e : n₂ = k * n := by
      have : (n₂ : ℝ) = k * n := by rw [hn₂, hn]; simp
      exact_mod_cast this
    rw [hid, e, hk, mul_pow, pow_mul, Ideal.span_singleton_mul_left_unit (v.isUnit.pow n)]

open GlobalTheory.FlagMod GlobalTheory.Reg GlobalTheory.PolFin GlobalTheory.TraitGen in
attribute [local instance] Over.cartesianMonoidalCategory in

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c p W _ _ Z Y bV hbV O' _ _ _ b' ϖ a χ₀ hO _ x₀ hx`. Establish `: IsLocalRing O'`. Break down `hO with ⟨h, -⟩ | ⟨h, -⟩` into its components or cases. Conclude with `h.toField.instIsLocalRing`. Use `infer_instance`.

Take `⟨tR, ⟨mt⟩⟩` from `exists_sabPull χ₀ Y.t`. Take `⟨u, ⟨n₀⟩⟩` from `exists_sabPull x₀ Z.oF.t`. Take `⟨aC, -⟩` from `LevelCover.sab_comp n₀ Z.m (e := x₀ ≫ Z.j) rfl`. Take `⟨n₁, -⟩` from `LevelCover.sab_comp n₀ Z.m0.toSABMap rfl`. Take `⟨n₂, -⟩` from `LevelCover.sab_cancel Y.m0.toSABMap n₁ x₀ rfl`.

Take `⟨n₃, -⟩` from `LevelCover.sab_comp n₂ Y.m (e := x₀ ≫ Y.j) rfl`. Take `⟨aT, -⟩` from `LevelCover.sab_cancel mt n₃ (jK _) hx`. Establish `hu : IsProper u.G.hom` using `MorphismProperty.of_isPullback (P := @IsProper) n₀.cart.1 Z.oF.proper`. Conclude with `exists_detOm_gen_extAt hu aT aC`.
-/
theorem detFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype) (bV : 𝓞 c.F →+* c.V W)
    (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F)),
      ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b' : c.V W →+* O') (ϖ : O')
        (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' (b'.comp bV)) (χ₀ : Sp (PowerSeries O') ⟶ Y.X),
        IsArcBase O' ϖ → IsArcChart Y (GlobalTheory.PolArc.moveV bV hbV b' a) ϖ χ₀ →
        ∀ x₀ : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, Out.jK (PowerSeries O') ≫ χ₀ = x₀ ≫ Y.j →
        ∃ e : LB.Gen ((GlobalTheory.FlagMod.detOm Z).pull (x₀ ≫ Z.j)), e.IsGen ∧ GlobalTheory.TraitGen.ExtAt (GlobalTheory.FlagMod.detOm Z) (x₀ ≫ Z.j) e := by
  intro E _ _ _ H D l Xo c p W _ _ Z Y bV hbV O' _ _ _ b' ϖ a χ₀ hO _ x₀ hx
  have : IsLocalRing O' := by
    rcases hO with ⟨h, -⟩ | ⟨h, -⟩
    · exact h.toField.instIsLocalRing
    · infer_instance
  obtain ⟨tR, ⟨mt⟩⟩ := exists_sabPull χ₀ Y.t
  obtain ⟨u, ⟨n₀⟩⟩ := exists_sabPull x₀ Z.oF.t
  obtain ⟨aC, -⟩ := LevelCover.sab_comp n₀ Z.m (e := x₀ ≫ Z.j) rfl
  obtain ⟨n₁, -⟩ := LevelCover.sab_comp n₀ Z.m0.toSABMap rfl
  obtain ⟨n₂, -⟩ := LevelCover.sab_cancel Y.m0.toSABMap n₁ x₀ rfl
  obtain ⟨n₃, -⟩ := LevelCover.sab_comp n₂ Y.m (e := x₀ ≫ Y.j) rfl
  obtain ⟨aT, -⟩ := LevelCover.sab_cancel mt n₃ (jK _) hx
  have hu : IsProper u.G.hom := MorphismProperty.of_isPullback (P := @IsProper) n₀.cart.1 Z.oF.proper
  exact exists_detOm_gen_extAt hu aT aC

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c p W hp hW Z Y bV hbV φ m BD hhom hpol O' _ _ _ b' ϖ a χ₀ hB hC x₀ hx₀ n hn`. Take `⟨e₁, he₁, hx₁⟩` from `detFrame E H D l Xo c p W hp hW Z Y bV hbV O' b' ϖ a χ₀ hB hC x₀ hx₀`. Take `⟨e₂, he₂, hx₂⟩` from `GlobalTheory.TraitGen.extAt_lbPow _ _ _ _ e₁ m he₁ hx₁`. Take `⟨e₃, he₃, hx₃⟩` from `GlobalTheory.TraitGen.exists_dual_gen_extAt Z.X BD (PowerSeries O') PowerSeries.X PowerSeries.X_ne_zero (x₀ ≫ Z.j) n hn`. Conclude with `GlobalTheory.TraitGen.exists_tens_extAt _ _ _ _ _ e₂ e₃ he₂ he₃ hx₂ hx₃`.
-/
theorem polGen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype) (bV : 𝓞 c.F →+* c.V W)
    (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F)) (φ : InvFun (𝓞 E)) (m : ℕ) (BD : GlobalTheory.EffCartierData Z.X),
      (∀ (n : ℕ) (k : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ), φ.toFun n (fun a b => k * B a b) = k * φ.toFun n B) →
      IsPol φ m Z BD →
      ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b' : c.V W →+* O') (ϖ : O')
        (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' (b'.comp bV)) (χ₀ : Sp (PowerSeries O') ⟶ Y.X),
        IsArcBase O' ϖ → IsArcChart Y (GlobalTheory.PolArc.moveV bV hbV b' a) ϖ χ₀ →
        ∀ x₀ : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, Out.jK (PowerSeries O') ≫ χ₀ = x₀ ≫ Y.j →
        ∀ n : ℕ, (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V →
    ∀ (ψ : PowerSeries O' →+* V) (gam : FractionRing (PowerSeries O') →+* FractionRing V),
    (∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap V _ (ψ r)) →
    ∀ χ : Sp V ⟶ Z.X, spMap gam ≫ x₀ ≫ Z.j = Out.jK V ≫ χ → GlobalTheory.LocM.idlAlong BD.idealSheaf χ = Ideal.span {ψ PowerSeries.X ^ n}) →
  ∃ e : LB.Gen ((polOf Z m BD).pull (x₀ ≫ Z.j)), e.IsGen ∧ GlobalTheory.TraitGen.ExtAt (polOf Z m BD) (x₀ ≫ Z.j) e := by
  intro E _ _ _ H D l Xo c p W hp hW Z Y bV hbV φ m BD hhom hpol O' _ _ _ b' ϖ a χ₀ hB hC x₀ hx₀ n hn
  obtain ⟨e₁, he₁, hx₁⟩ := detFrame E H D l Xo c p W hp hW Z Y bV hbV O' b' ϖ a χ₀ hB hC x₀ hx₀
  obtain ⟨e₂, he₂, hx₂⟩ := GlobalTheory.TraitGen.extAt_lbPow _ _ _ _ e₁ m he₁ hx₁
  obtain ⟨e₃, he₃, hx₃⟩ := GlobalTheory.TraitGen.exists_dual_gen_extAt Z.X BD (PowerSeries O') PowerSeries.X
    PowerSeries.X_ne_zero (x₀ ≫ Z.j) n hn
  exact GlobalTheory.TraitGen.exists_tens_extAt _ _ _ _ _ e₂ e₃ he₂ he₃ hx₂ hx₃

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c p W hp hpW Z Y bV hbV φ m BD hhom hpol O' _ _ _ b' ϖ a χ₀ hO hχ₀ x₀ hx₀`. Take `⟨_, _, _⟩` from `powerSeries_props O' ϖ hO`. Establish `: CharZero (PowerSeries O')` using `charZero_of_injective_ringHom (PowerSeries.C_injective (R := O'))`. Use `isProper_toroidalModel_structureMap Z` as an intermediate fact. Establish `: CompactSpace Z.X` using `hpol.2.compactSpace`.

Establish `: QuasiSeparatedSpace Z.X` using `quasiSeparatedSpace_of_quasiSeparated Z.s`. Establish `eF : spMap (algebraMap (𝓞 c.F) c.F) = spMap (c.V W).subtype ≫ spMap bV`. Rewrite using `[← spMap_comp]`. Use `congr 1`. Use extensionality with `x`.

Conclude with `congrArg (fun y : c.F => (y : ℂ)) (hbV x).symm`. Establish `hZs : x₀ ≫ Z.j ≫ Z.s = Out.jK (PowerSeries O') ≫ spMap (PowerSeries.C (R` using `O')) ≫ spMap b' ≫ spMap bV := by`. Establish `hY : x₀ ≫ Y.j ≫ Y.s = Out.jK (PowerSeries O') ≫ spMap (PowerSeries.C (R` using `O')) ≫ spMap b' := by`. Rewrite using `[← Category.assoc, ← hx₀, Category.assoc, hχ₀.1]`. Rewrite `hY`, the goal using `[Model.j_s]`.

Rewrite using `[eF]`. Simplify using `only [← Category.assoc] at hY ⊢`. Rewrite using `[hY]`. Take `⟨n, hn⟩` from `order E H D l Xo c p W hp hpW Z Y bV hbV φ m BD hhom hpol O' b' ϖ a χ₀ hO hχ₀ x₀ hx₀`. Take `⟨e, he, htr⟩` from `polGen E H D l Xo c p W hp hpW Z Y bV hbV φ m BD hhom hpol O' b' ϖ a χ₀ hO hχ₀ x₀ hx₀ n hn`.

Use `GlobalTheory.ExtLB.exists_extension Z.X (polOf Z m BD) hpol.2.isLB (fun z => GlobalTheory.PolFin.exists_H0_of_isAmpleLB hpol.2 z) (PowerSeries O') (x₀ ≫ Z.j) e he fun V _ _ _ hV ψ gam hg => ?_` and prove the remaining obligations. Use `hV.1` as an intermediate fact. Take `⟨χ, hχ, -⟩` from `val_exists Z.s (spMap gam ≫ x₀ ≫ Z.j) (spMap ψ ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b' ≫ spMap bV) (by`. Rewrite using `[Category.assoc, Category.assoc, hZs, ← Category.assoc (spMap gam), spMap_jK' hg, Category.assoc])`. Conclude with `⟨χ, hχ.symm, htr V hV ψ gam hg χ hχ.symm⟩`.
-/
theorem extend : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype) (bV : 𝓞 c.F →+* c.V W)
    (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F)) (φ : InvFun (𝓞 E)) (m : ℕ) (BD : GlobalTheory.EffCartierData Z.X),
      (∀ (n : ℕ) (k : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ), φ.toFun n (fun a b => k * B a b) = k * φ.toFun n B) →
      IsPol φ m Z BD →
      ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b' : c.V W →+* O') (ϖ : O')
        (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' (b'.comp bV)) (χ₀ : Sp (PowerSeries O') ⟶ Y.X),
        IsArcBase O' ϖ → IsArcChart Y (GlobalTheory.PolArc.moveV bV hbV b' a) ϖ χ₀ →
        ∀ x₀ : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, Out.jK (PowerSeries O') ≫ χ₀ = x₀ ≫ Y.j →
        ∃ χ : Sp (PowerSeries O') ⟶ Z.X, Out.jK (PowerSeries O') ≫ χ = x₀ ≫ Z.j := by
  intro E _ _ _ H D l Xo c p W hp hpW Z Y bV hbV φ m BD hhom hpol O' _ _ _ b' ϖ a χ₀ hO hχ₀ x₀ hx₀
  obtain ⟨_, _, _⟩ := powerSeries_props O' ϖ hO
  have : CharZero (PowerSeries O') := charZero_of_injective_ringHom (PowerSeries.C_injective (R := O'))
  have := isProper_toroidalModel_structureMap Z
  have : CompactSpace Z.X := hpol.2.compactSpace
  have : QuasiSeparatedSpace Z.X := quasiSeparatedSpace_of_quasiSeparated Z.s
  have eF : spMap (algebraMap (𝓞 c.F) c.F) = spMap (c.V W).subtype ≫ spMap bV := by
    rw [← spMap_comp]
    congr 1
    ext x
    exact congrArg (fun y : c.F => (y : ℂ)) (hbV x).symm
  have hZs : x₀ ≫ Z.j ≫ Z.s = Out.jK (PowerSeries O') ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b' ≫ spMap bV := by
    have hY : x₀ ≫ Y.j ≫ Y.s = Out.jK (PowerSeries O') ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b' := by
      rw [← Category.assoc, ← hx₀, Category.assoc, hχ₀.1]
    rw [Model.j_s] at hY ⊢
    rw [eF]
    simp only [← Category.assoc] at hY ⊢
    rw [hY]
  obtain ⟨n, hn⟩ := order E H D l Xo c p W hp hpW Z Y bV hbV φ m BD hhom hpol O' b' ϖ a χ₀ hO hχ₀ x₀ hx₀
  obtain ⟨e, he, htr⟩ := polGen E H D l Xo c p W hp hpW Z Y bV hbV φ m BD hhom hpol O' b' ϖ a χ₀ hO hχ₀ x₀ hx₀ n hn
  refine GlobalTheory.ExtLB.exists_extension Z.X (polOf Z m BD) hpol.2.isLB
    (fun z => GlobalTheory.PolFin.exists_H0_of_isAmpleLB hpol.2 z) (PowerSeries O') (x₀ ≫ Z.j) e he fun V _ _ _ hV ψ gam hg => ?_
  have := hV.1
  obtain ⟨χ, hχ, -⟩ := val_exists Z.s (spMap gam ≫ x₀ ≫ Z.j)
    (spMap ψ ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b' ≫ spMap bV) (by
      rw [Category.assoc, Category.assoc, hZs, ← Category.assoc (spMap gam), spMap_jK' hg, Category.assoc])
  exact ⟨χ, hχ.symm, htr V hV ψ gam hg χ hχ.symm⟩

end GlobalTheory.AnyChartExtend
