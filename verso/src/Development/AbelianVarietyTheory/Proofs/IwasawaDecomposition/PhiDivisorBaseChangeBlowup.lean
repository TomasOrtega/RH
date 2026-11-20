import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorArcBlowup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptySabMapOfCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcDataSpecialiseAtUniformiser
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPeriod
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExtendedArcUAdicUniformisationOfArcData
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistedPrincipalPolarisationSectionsBaseChange
import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.MapPowLeOfIsPullUnif
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProperSemiAbelianFamily

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.ArcGenOrder

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c X K _ x hx`. Use `c.fin` as an intermediate fact. Establish `: NumberField c.F` using `{}`. Establish `hβ : Function.Injective (algebraMap (𝓞 c.F) c.F)` using `IsFractionRing.injective _ _`. Set `f : 𝓞 c.F →+* K` to `(Spec.preimage (x ≫ X.s)).hom`.

Establish `hxs : x ≫ X.s = spMap f` using `by simp only [spMap, f, CommRingCat.ofHom_hom, Spec.map_preimage]`. Set `p0 : Sp K` to `IsLocalRing.closedPoint K`. Take `⟨q, hq⟩` from `hx ⟨p0, rfl⟩`. Establish `hf : Function.Injective f`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `r hr`. Establish `e1 : (x ≫ X.s) p0 = (X.jQ ≫ pullback.snd _ _ ≫ spMap (algebraMap (𝓞 c.F) c.F)) q`. Rewrite using `[← pullback.condition]`. Simplify using `only [Scheme.Hom.comp_apply]`. Rewrite using `[← hq]`.

Both sides reduce to the same expression. Establish `h1 : r ∈ ((x ≫ X.s) p0).asIdeal`. Rewrite using `[hxs]`. Use `show f r ∈ (IsLocalRing.closedPoint K).asIdeal`. Rewrite using `[hr]`.

Conclude with `Ideal.zero_mem _`. Rewrite `h1` using `[e1]`. Establish `h2 : algebraMap (𝓞 c.F) c.F r ∈ ((X.jQ ≫ pullback.snd _ _) q).asIdeal` using `h1`. Rewrite `h2` using `[@Ideal.eq_bot_of_prime _ _ _ ((X.jQ ≫ pullback.snd _ _) q).isPrime, Ideal.mem_bot]`. Conclude with `(map_eq_zero_iff _ hβ).1 h2`.

Set `g : c.F →+* K` to `IsLocalization.lift (M := nonZeroDivisors (𝓞 c.F)) (S := c.F) (g := f) fun y => IsUnit.mk0 _ ((map_ne_zero_iff f hf).2 (nonZeroDivisors.ne_zero y.2))`. Establish `hg : g.comp (algebraMap (𝓞 c.F) c.F) = f` using `IsLocalization.lift_comp _`. Establish `hsq : x ≫ X.s = spMap g ≫ spMap (algebraMap (𝓞 c.F) c.F)`. Rewrite using `[hxs, ← hg]`. Simplify using `only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`.

Set `z : Sp K ⟶ pullback X.s (spMap (algebraMap (𝓞 c.F) c.F))` to `pullback.lift x (spMap g) hsq`. Establish `hz : z ≫ pullback.fst _ _ = x` using `pullback.lift_fst _ _ _`. Use `haveI : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) := IsPreimmersion.of_isLocalization (R := 𝓞 c.F) (S := c.F) (nonZeroDivisors (𝓞 c.F))`. Establish `hinj : Function.Injective (pullback.fst X.s (spMap (algebraMap (𝓞 c.F) c.F)))` using `(Scheme.Hom.isEmbedding _).injective`. Establish `hrange : Set.range z ⊆ Set.range X.jQ`.

Introduce `w ⟨p, hp⟩`. Take `⟨q', hq'⟩` from `hx ⟨p, rfl⟩`. Use `⟨q', hinj ?_⟩` and prove the remaining obligations. Rewrite using `[← hp]`. Use `show X.j q' = (z ≫ pullback.fst _ _) p`.

Rewrite using `[hz]`. Conclude with `hq'`. Use `haveI := X.jQ_open`. Use `⟨IsOpenImmersion.lift X.jQ z hrange, ?_⟩` and prove the remaining obligations. Rewrite using `[Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, hz]`.
-/
theorem exists_moduli_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X : GMod Xo c) (K : Type) [Field K] (x : Sp K ⟶ X.X), Set.range x ⊆ Set.range X.j → ∃ y : Sp K ⟶ Xo.XF c, y ≫ X.j = x := by
  intro E _ _ _ H D l Xo c X K _ x hx
  have := c.fin
  have : NumberField c.F := {}
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := IsFractionRing.injective _ _
  let f : 𝓞 c.F →+* K := (Spec.preimage (x ≫ X.s)).hom
  have hxs : x ≫ X.s = spMap f := by simp only [spMap, f, CommRingCat.ofHom_hom, Spec.map_preimage]

  let p0 : Sp K := IsLocalRing.closedPoint K
  obtain ⟨q, hq⟩ := hx ⟨p0, rfl⟩
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    have e1 : (x ≫ X.s) p0 = (X.jQ ≫ pullback.snd _ _ ≫ spMap (algebraMap (𝓞 c.F) c.F)) q := by
      rw [← pullback.condition]
      simp only [Scheme.Hom.comp_apply]
      rw [← hq]; rfl
    have h1 : r ∈ ((x ≫ X.s) p0).asIdeal := by
      rw [hxs]
      show f r ∈ (IsLocalRing.closedPoint K).asIdeal
      rw [hr]; exact Ideal.zero_mem _
    rw [e1] at h1
    have h2 : algebraMap (𝓞 c.F) c.F r ∈ ((X.jQ ≫ pullback.snd _ _) q).asIdeal := h1
    rw [@Ideal.eq_bot_of_prime _ _ _ ((X.jQ ≫ pullback.snd _ _) q).isPrime, Ideal.mem_bot] at h2
    exact (map_eq_zero_iff _ hβ).1 h2
  let g : c.F →+* K := IsLocalization.lift (M := nonZeroDivisors (𝓞 c.F)) (S := c.F) (g := f)
    fun y => IsUnit.mk0 _ ((map_ne_zero_iff f hf).2 (nonZeroDivisors.ne_zero y.2))
  have hg : g.comp (algebraMap (𝓞 c.F) c.F) = f := IsLocalization.lift_comp _
  have hsq : x ≫ X.s = spMap g ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [hxs, ← hg]; simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let z : Sp K ⟶ pullback X.s (spMap (algebraMap (𝓞 c.F) c.F)) := pullback.lift x (spMap g) hsq
  have hz : z ≫ pullback.fst _ _ = x := pullback.lift_fst _ _ _

  haveI : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 c.F) (S := c.F) (nonZeroDivisors (𝓞 c.F))
  have hinj : Function.Injective (pullback.fst X.s (spMap (algebraMap (𝓞 c.F) c.F))) :=
    (Scheme.Hom.isEmbedding _).injective
  have hrange : Set.range z ⊆ Set.range X.jQ := by
    intro w ⟨p, hp⟩
    obtain ⟨q', hq'⟩ := hx ⟨p, rfl⟩
    refine ⟨q', hinj ?_⟩
    rw [← hp]
    show X.j q' = (z ≫ pullback.fst _ _) p
    rw [hz]; exact hq'
  haveI := X.jQ_open
  refine ⟨IsOpenImmersion.lift X.jQ z hrange, ?_⟩
  rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, hz]

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c X Z π hj hs W _ _ _ hW χ y hy`. Use `haveI : IsDiscreteValuationRing W := hW.1`. Use `haveI : IsProper Z.s := GlobalTheory.ProperFamily.isProper_of_isProjOver Z.proj`. Use `haveI : IsProper X.s := GlobalTheory.ProperFamily.isProper_of_isProjOver X.proj`. Use `haveI : IsProper (π ≫ X.s) := by rw [hs]; infer_instance`.

Use `haveI : IsProper π := IsProper.of_comp π X.s`. Establish `hv : ValuativeCriterion.Existence π`. Establish `h : UniversallyClosed π` using `inferInstance`. Rewrite `h` using `[UniversallyClosed.eq_valuativeCriterion]`. Conclude with `h.1`.

Establish `hp : (y ≫ Z.j) ≫ π = jK W ≫ χ` using `by rw [Category.assoc, hj, hy]`. Take `⟨⟨q, q1, q2⟩⟩` from `(hv ⟨W, FractionRing W, y ≫ Z.j, χ, ⟨hp⟩⟩).exists_lift`. Conclude with `⟨q, q2, q1⟩`.
-/
theorem exists_lift_of_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X), Z.j ≫ π = X.j → π ≫ X.s = Z.s → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (χ : Sp W ⟶ X.X) (y : Sp (FractionRing W) ⟶ Xo.XF c), y ≫ X.j = jK W ≫ χ → ∃ χZ : Sp W ⟶ Z.X, χZ ≫ π = χ ∧ jK W ≫ χZ = y ≫ Z.j := by
  intro E _ _ _ H D l Xo c X Z π hj hs W _ _ _ hW χ y hy
  haveI : IsDiscreteValuationRing W := hW.1
  haveI : IsProper Z.s := GlobalTheory.ProperFamily.isProper_of_isProjOver Z.proj
  haveI : IsProper X.s := GlobalTheory.ProperFamily.isProper_of_isProjOver X.proj
  haveI : IsProper (π ≫ X.s) := by rw [hs]; infer_instance
  haveI : IsProper π := IsProper.of_comp π X.s
  have hv : ValuativeCriterion.Existence π := by
    have h : UniversallyClosed π := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have hp : (y ≫ Z.j) ≫ π = jK W ≫ χ := by rw [Category.assoc, hj, hy]
  obtain ⟨⟨q, q1, q2⟩⟩ := (hv ⟨W, FractionRing W, y ≫ Z.j, χ, ⟨hp⟩⟩).exists_lift
  exact ⟨q, q2, q1⟩

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c X Z Y BY π e J EX n d' φ hPhi hB O' _ _ _ _ b ϖ a _ hϖ hcpl χA h1 h2 h3 h4 m hm`. Establish `hinjK : Function.Injective (algebraMap O' (FractionRing O'))` using `IsFractionRing.injective O' _`. Use `haveI : CharZero (FractionRing O') := charZero_of_injective_algebraMap hinjK`. Set `g : PowerSeries O' →+* PowerSeries (FractionRing O')` to `PowerSeries.map (algebraMap O' (FractionRing O'))`. Establish `hg : Function.Injective g` using `PowerSeries.map_injective _ hinjK`.

Establish `hW : CDvr (PowerSeries (FractionRing O'))` using `GlobalTheory.ArcData.cdvr_powerSeries _`. Use `haveI : IsDiscreteValuationRing (PowerSeries (FractionRing O')) := hW.1`. Establish `hgen : Set.range (jK (PowerSeries (FractionRing O')) ≫ spMap g ≫ χA) ⊆ Set.range X.j`. Introduce and unpack `_ ⟨p, rfl⟩`. Use `h3 _ fun hmem => ?_` and prove the remaining obligations.

Set `ψ : PowerSeries O' →+* FractionRing (PowerSeries (FractionRing O'))` to `(algebraMap (PowerSeries (FractionRing O')) _).comp g`. Establish `hψ : Function.Injective ψ` using `(IsFractionRing.injective (PowerSeries (FractionRing O')) (FractionRing (PowerSeries (FractionRing O')))).comp hg`. Establish `e1 : jK (PowerSeries (FractionRing O')) ≫ spMap g = spMap ψ`. Simplify using `only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Establish `hp : p.asIdeal = ⊥` using `@Ideal.eq_bot_of_prime _ _ _ p.isPrime`.

Establish `e2 : (jK (PowerSeries (FractionRing O')) ≫ spMap g) p = spMap ψ p` using `by rw [e1]`. Establish `hx : PowerSeries.C ϖ * PowerSeries.X ∈ (spMap ψ p).asIdeal`. Rewrite using `[← e2]`. Conclude with `hmem`. Establish `hmem' : ψ (PowerSeries.C ϖ * PowerSeries.X) ∈ p.asIdeal` using `hx`.

Rewrite `hmem'` using `[hp, Ideal.mem_bot, map_eq_zero_iff _ hψ]`. Conclude with `mul_ne_zero ((map_ne_zero_iff _ PowerSeries.C_injective).2 hϖ.ne_zero) PowerSeries.X_ne_zero hmem'`. Take `⟨Wt⟩` from `(X.hasArcData_iff _ _ _ _ _).1 h4`. Take `⟨hL, hL₂, -, -, h5, -⟩` from `GlobalTheory.allSixLaws`. Establish `hmax : maximalIdeal O' = Ideal.span {ϖ}` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ`.

Establish `hcpl' : IsAdicComplete (maximalIdeal O') O'` using `hmax ▸ hcpl`. Establish `hR` using `(GlobalTheory.ArcData.powerSeries_dvr_admissible_X_ideal O' hcpl').1.1`. Establish `hR'` using `(GlobalTheory.ArcData.admissible_maximal_ideal_of_complete_dvr_char_zero hW).1.1`. Establish `hI : (Ideal.span {(PowerSeries.X : PowerSeries O')}).map g ≤ maximalIdeal (PowerSeries (FractionRing O'))`. Rewrite using `[Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem, PowerSeries.map_X, PowerSeries.maximalIdeal_eq_span_X]`.

Conclude with `Ideal.mem_span_singleton_self _`. Establish `hu : g PowerSeries.X ≠ 0` using `by rw [PowerSeries.map_X]; exact PowerSeries.X_ne_zero`. Establish `hS : ∀ (F : Type) [Field F] (i : PowerSeries (FractionRing O') →+* F), Function.Injective i → ∃ σ : PowerSeries O' →+* PowerSeries F, Function.Injective σ ∧ (∀ x, σ (PowerSeries.C x) = PowerSeries.C (i (g (PowerSeries.C x)))) ∧ ∀ r, PowerSeries.constantCoeff (σ r) = i (g r)` using `fun F _ i hi => ⟨(PowerSeries.C (R := F)).comp (i.comp g), PowerSeries.C_injective.comp (hi.comp hg), fun _ => rfl, fun r => PowerSeries.constantCoeff_C _⟩`. Take `⟨A⟩` from `GlobalTheory.ArcSpecialise.specialise hL hL₂ GlobalTheory.twistBaseChange GlobalTheory.UnifPullGuards.unifBaseChange_holds h5 hR hR' PowerSeries.C_injective Wt h1 g hI hu hgen hS`. Establish `hXirr : Irreducible (PowerSeries.X : PowerSeries (FractionRing O'))` using `PowerSeries.X_irreducible`.

Use `haveI : CharZero (PowerSeries (FractionRing O')) := charZero_of_injective_ringHom PowerSeries.C_injective`. Establish `hfi : Function.Injective (g.comp (PowerSeries.C (R` using `O'))) := hg.comp PowerSeries.C_injective`. Take `⟨be, hbe, hmon, hbeq⟩` from `GlobalTheory.ArcOrder.exists_form hfi A hXirr 1 1 (by show PowerSeries.map _ PowerSeries.X = _; rw [PowerSeries.map_X]; simp)`. Take `⟨y, hy⟩` from `exists_moduli_point E H D l Xo c X _ (jK (PowerSeries (FractionRing O')) ≫ spMap g ≫ χA) hgen`. Take `⟨χZ, hχZ, hjZ⟩` from `exists_lift_of_generic E H D l Xo c X Z π hB.2.1 hB.2.2.1 _ hW (spMap g ≫ χA) y hy`.

Take `⟨mZ⟩` from `GlobalTheory.T.nonempty_sabMap_of_compatible E H D l Xo c X Z π hB.2.1 hB.2.2.1`. Take `⟨mA⟩` from `GlobalTheory.TraitOrder.cancel hχZ mZ A.m`. Establish `hr : Set.range (jK (PowerSeries (FractionRing O')) ≫ χZ) ⊆ Set.range Z.j`. Introduce and unpack `_ ⟨p, rfl⟩`. Conclude with `⟨y p, by rw [hjZ]; rfl⟩`.

Establish `hprim : ∀ p : ℕ, p.Prime → IsUnit (p : PowerSeries (FractionRing O'))` using `fun p hp => by`. Rewrite using `[← map_natCast (PowerSeries.C (R := FractionRing O'))]`. Conclude with `(IsUnit.mk0 _ (Nat.cast_ne_zero.2 hp.ne_zero)).map _`. Take `⟨m', hm', hid⟩` from `GlobalTheory.TorRef.blowOrd_eqChar E H D l Xo c X Z Y BY π e J EX n d' φ hPhi hB _ hW hprim PowerSeries.X hXirr χZ A.t mA A.P hr be hbe hmon`. Establish `hev : (comb 0 φ (n * d') φ).evalZ be = (comb 0 φ (n * d') φ).evalZ a.be`.

Unfold `InvFun.evalZ`. Rewrite using `[← InvFun.eval_equiv _ A.e]`. Use `congr 1`. Use function extensionality and compare the values at `u v`. Rewrite using `[hbeq u v]`.

Simplify using the standard rewrite rules. Establish `hmm : m' = m` using `by exact_mod_cast hm'.trans (hev.trans hm.symm)`. Substitute `hmm` using the available equality. Rewrite using `[← hχZ, ← GlobalTheory.TorRef.idlAlong_comap, ← hB.2.2.2.2.1, hid]`.
-/
theorem idlAlong_generic_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : EffCartierData Y.X) (π : Z.X ⟶ X.X) (e : gen Y ≅ gen Z) (J : X.X.IdealSheafData) (EX : EffCartierData Z.X) (n d' : ℕ) (φ : InvFun (𝓞 E)), IsPhiDiv (comb 0 φ d' φ) Y BY → IsBlowOf X Z Y BY π e J EX n → ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [CharZero O'] (b : 𝓞 c.F →+* O') (ϖ : O') (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' b) [Module.Finite (𝓞 E) a.D₀.X], Irreducible ϖ → IsAdicComplete (Ideal.span {ϖ}) O' → ∀ χA : Sp (PowerSeries O') ⟶ X.X, χA ≫ X.s = spMap (PowerSeries.C (R := O')) ≫ spMap b → (∀ x : Sp (PowerSeries O'), χA x ∈ abLocus X.t.G ↔ PowerSeries.X ∉ x.asIdeal) → (∀ x : Sp (PowerSeries O'), PowerSeries.C ϖ * PowerSeries.X ∉ x.asIdeal → χA x ∈ Set.range X.j) → X.HasArcData a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := O')) PowerSeries.X χA → ∀ m : ℕ, (m : ℝ) = (comb 0 φ (n * d') φ).evalZ a.be → idlAlong J (spMap (PowerSeries.map (algebraMap O' (FractionRing O'))) ≫ χA) ≤ Ideal.span {PowerSeries.X ^ m} := by
  intro E _ _ _ H D l Xo c X Z Y BY π e J EX n d' φ hPhi hB O' _ _ _ _ b ϖ a _ hϖ hcpl χA h1 h2 h3 h4 m hm
  have hinjK : Function.Injective (algebraMap O' (FractionRing O')) := IsFractionRing.injective O' _
  haveI : CharZero (FractionRing O') := charZero_of_injective_algebraMap hinjK
  let g : PowerSeries O' →+* PowerSeries (FractionRing O') := PowerSeries.map (algebraMap O' (FractionRing O'))
  have hg : Function.Injective g := PowerSeries.map_injective _ hinjK
  have hW : CDvr (PowerSeries (FractionRing O')) := GlobalTheory.ArcData.cdvr_powerSeries _
  haveI : IsDiscreteValuationRing (PowerSeries (FractionRing O')) := hW.1

  have hgen : Set.range (jK (PowerSeries (FractionRing O')) ≫ spMap g ≫ χA) ⊆ Set.range X.j := by
    rintro _ ⟨p, rfl⟩
    refine h3 _ fun hmem => ?_
    let ψ : PowerSeries O' →+* FractionRing (PowerSeries (FractionRing O')) :=
      (algebraMap (PowerSeries (FractionRing O')) _).comp g
    have hψ : Function.Injective ψ :=
      (IsFractionRing.injective (PowerSeries (FractionRing O')) (FractionRing (PowerSeries (FractionRing O')))).comp hg
    have e1 : jK (PowerSeries (FractionRing O')) ≫ spMap g = spMap ψ := by
      simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hp : p.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ _ p.isPrime
    have e2 : (jK (PowerSeries (FractionRing O')) ≫ spMap g) p = spMap ψ p := by rw [e1]
    have hx : PowerSeries.C ϖ * PowerSeries.X ∈ (spMap ψ p).asIdeal := by
      rw [← e2]; exact hmem
    have hmem' : ψ (PowerSeries.C ϖ * PowerSeries.X) ∈ p.asIdeal := hx
    rw [hp, Ideal.mem_bot, map_eq_zero_iff _ hψ] at hmem'
    exact mul_ne_zero ((map_ne_zero_iff _ PowerSeries.C_injective).2 hϖ.ne_zero) PowerSeries.X_ne_zero hmem'

  obtain ⟨Wt⟩ := (X.hasArcData_iff _ _ _ _ _).1 h4
  obtain ⟨hL, hL₂, -, -, h5, -⟩ := GlobalTheory.allSixLaws
  have hmax : maximalIdeal O' = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hcpl' : IsAdicComplete (maximalIdeal O') O' := hmax ▸ hcpl
  have hR := (GlobalTheory.ArcData.powerSeries_dvr_admissible_X_ideal O' hcpl').1.1
  have hR' := (GlobalTheory.ArcData.admissible_maximal_ideal_of_complete_dvr_char_zero hW).1.1
  have hI : (Ideal.span {(PowerSeries.X : PowerSeries O')}).map g ≤ maximalIdeal (PowerSeries (FractionRing O')) := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem, PowerSeries.map_X,
      PowerSeries.maximalIdeal_eq_span_X]
    exact Ideal.mem_span_singleton_self _
  have hu : g PowerSeries.X ≠ 0 := by rw [PowerSeries.map_X]; exact PowerSeries.X_ne_zero
  have hS : ∀ (F : Type) [Field F] (i : PowerSeries (FractionRing O') →+* F), Function.Injective i →
      ∃ σ : PowerSeries O' →+* PowerSeries F, Function.Injective σ ∧
        (∀ x, σ (PowerSeries.C x) = PowerSeries.C (i (g (PowerSeries.C x)))) ∧
        ∀ r, PowerSeries.constantCoeff (σ r) = i (g r) := fun F _ i hi =>
    ⟨(PowerSeries.C (R := F)).comp (i.comp g), PowerSeries.C_injective.comp (hi.comp hg), fun _ => rfl,
      fun r => PowerSeries.constantCoeff_C _⟩
  obtain ⟨A⟩ := GlobalTheory.ArcSpecialise.specialise hL hL₂ GlobalTheory.twistBaseChange GlobalTheory.UnifPullGuards.unifBaseChange_holds h5 hR hR'
    PowerSeries.C_injective Wt h1 g hI hu hgen hS
  have hXirr : Irreducible (PowerSeries.X : PowerSeries (FractionRing O')) := PowerSeries.X_irreducible
  haveI : CharZero (PowerSeries (FractionRing O')) := charZero_of_injective_ringHom PowerSeries.C_injective
  have hfi : Function.Injective (g.comp (PowerSeries.C (R := O'))) := hg.comp PowerSeries.C_injective
  obtain ⟨be, hbe, hmon, hbeq⟩ := GlobalTheory.ArcOrder.exists_form hfi A hXirr 1 1
    (by show PowerSeries.map _ PowerSeries.X = _; rw [PowerSeries.map_X]; simp)

  obtain ⟨y, hy⟩ := exists_moduli_point E H D l Xo c X _ (jK (PowerSeries (FractionRing O')) ≫ spMap g ≫ χA) hgen
  obtain ⟨χZ, hχZ, hjZ⟩ := exists_lift_of_generic E H D l Xo c X Z π hB.2.1 hB.2.2.1 _ hW (spMap g ≫ χA) y hy
  obtain ⟨mZ⟩ := GlobalTheory.T.nonempty_sabMap_of_compatible E H D l Xo c X Z π hB.2.1 hB.2.2.1
  obtain ⟨mA⟩ := GlobalTheory.TraitOrder.cancel hχZ mZ A.m
  have hr : Set.range (jK (PowerSeries (FractionRing O')) ≫ χZ) ⊆ Set.range Z.j := by
    rintro _ ⟨p, rfl⟩
    exact ⟨y p, by rw [hjZ]; rfl⟩
  have hprim : ∀ p : ℕ, p.Prime → IsUnit (p : PowerSeries (FractionRing O')) := fun p hp => by
    rw [← map_natCast (PowerSeries.C (R := FractionRing O'))]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hp.ne_zero)).map _
  obtain ⟨m', hm', hid⟩ := GlobalTheory.TorRef.blowOrd_eqChar E H D l Xo c X Z Y BY π e J EX n d' φ hPhi hB _ hW hprim
    PowerSeries.X hXirr χZ A.t mA A.P hr be hbe hmon

  have hev : (comb 0 φ (n * d') φ).evalZ be = (comb 0 φ (n * d') φ).evalZ a.be := by
    unfold InvFun.evalZ
    rw [← InvFun.eval_equiv _ A.e]
    congr 1
    funext u v
    rw [hbeq u v]
    simp
  have hmm : m' = m := by exact_mod_cast hm'.trans (hev.trans hm.symm)
  subst hmm
  rw [← hχZ, ← GlobalTheory.TorRef.idlAlong_comap, ← hB.2.2.2.2.1, hid]

end GlobalTheory.ArcGenOrder
