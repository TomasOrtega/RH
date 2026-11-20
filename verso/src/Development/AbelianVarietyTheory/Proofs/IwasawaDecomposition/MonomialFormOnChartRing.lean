import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasConesIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialSupportHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordOfIsPullDegId
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DegenerationDataCoordsNeZeroLatticesIsomorphic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProperOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVGenericFibreOfTriple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpec
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TraitChartForm

/- English proof (translation)
Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Ideal.comap (algebraMap R (FractionRing R)) p.asIdeal = ⊥`. Rewrite using `[@Ideal.eq_bot_of_prime _ _ p.asIdeal p.isPrime]`. Conclude with `Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)`.
-/
theorem jK_apply_eq_bot (R : Type) [CommRing R] [IsDomain R] (p : Sp (FractionRing R)) :
    (jK R) p = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) := by
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap R (FractionRing R)) p.asIdeal = ⊥
  rw [@Ideal.eq_bot_of_prime _ _ p.asIdeal p.isPrime]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)

/- English proof (translation)
The claim follows from `PrimeSpectrum.ext rfl`.
-/
theorem ker_eq_spMap_bot {R S : Type} [CommRing R] [CommRing S] [IsDomain S] (φ : R →+* S) :
    (⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩ : PrimeSpectrum R) = spMap φ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum S) :=
  PrimeSpectrum.ext rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l}

/- English proof (translation)
Establish `h : Y.jQ w ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G` using `by rw [Y.ab_gen]; exact ⟨_, rfl⟩`. Conclude with `h`.
-/
theorem j_mem_abLocus {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) (w : Xo.XF c) :
    Y.j w ∈ abLocus Y.t.G := by
  have h : Y.jQ w ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by rw [Y.ab_gen]; exact ⟨_, rfl⟩
  exact h

end GlobalTheory.TraitChartForm

open GlobalTheory.TraitChartForm in

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c Y k _ m e ξ tC mC PC γ hmonC W _ _ _ hW ϖ hϖ χ t mt P hr be hmon V _ _ _ hV ϖ' hϖ' f ψ hfi hfl hψl hc r u hu n v hv`. Take `⟨hWd, hWc, hW0⟩` from `hW`. Take `⟨hVd, hVc, hV0⟩` from `hV`. Take `⟨L₁, L₂, -⟩` from `GlobalTheory.firstFiveLaws`. Establish `: CharZero (ChartRing k m e)` using `(Spec.preimage (ξ ≫ genStr Y)).hom.charZero_iff (RingHom.injective _) |>.1 inferInstance`.

Establish `: IsRegularLocalRing (ChartRing k m e)` using `GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k (Fin m ⊕ Fin e)`. Establish `hCI : IsIntegrallyClosed (ChartRing k m e)` using `(GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing _).2`. Establish `: IsAdicComplete (maximalIdeal k) k` using `by rw [maximalIdeal_eq_bot]; infer_instance`. Establish `hCA : IsAdicComplete (maximalIdeal (ChartRing k m e)) (ChartRing k m e)` using `GlobalTheory.PlaceInt.isAdicComplete_mvPowerSeries_finite (V := k) _`. Take `⟨tV, ⟨mV⟩⟩` from `GlobalTheory.TraitOrder.exists_pull (spMap f) t`.

Take `⟨tCV, ⟨mCV⟩⟩` from `GlobalTheory.TraitOrder.exists_pull (spMap ψ) tC`. Take `⟨n₁⟩` from `GlobalTheory.TraitOrder.comp rfl mt mV`. Take `⟨n₂⟩` from `GlobalTheory.TraitOrder.comp rfl mC mCV`. Take `⟨k₁⟩` from `GlobalTheory.TraitOrder.cancel (show 𝟙 _ ≫ (spMap f ≫ χ) = spMap ψ ≫ ξ ≫ genι Y by rw [Category.id_comp, hc]) n₁ n₂`. Establish `j : Function.Injective ((algebraMap V (FractionRing V)).comp f)` using `(IsFractionRing.injective V _).comp hfi`.

Set `g : FractionRing W →+* FractionRing V` to `IsFractionRing.lift j`. Establish `eg : jK V ≫ spMap f = spMap g ≫ jK W` using `(GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).trans (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).symm`. Establish `hpV : PolAt tV (jK V)` using `GlobalTheory.DatUniq.polAt_pull mV (GlobalTheory.DatUniq.polAt_of_unif P) (jK V) (spMap g) eg.symm`. Establish `hpCV : PolAt tCV (jK V)` using `GlobalTheory.DatUniq.polAt_pull k₁ hpV (jK V) (𝟙 _) (by rw [Category.id_comp, Category.comp_id])`. Take `⟨B, -, gen, hg, hw, -⟩` from `GlobalTheory.LN.exists_polAV_of_polAt L₁ L₂ E H V tV hpV`.

Take `⟨BC, -, genC, hgC, hwC, -⟩` from `GlobalTheory.LN.exists_polAV_of_polAt L₁ L₂ E H V tCV hpCV`. Establish `hχgen : χ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum W) ∈ abLocus Y.t.G`. Set `p : Sp (FractionRing W)` to `(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing W))`. Take `⟨w, hw⟩` from `hr ⟨p, rfl⟩`. Rewrite using `[← jK_apply_eq_bot W p, ← Scheme.Hom.comp_apply, ← hw]`.

Conclude with `j_mem_abLocus Y w`. Establish `hfbot : spMap f (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V) = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum W)`. Rewrite using `[← ker_eq_spMap_bot]`. Conclude with `PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot f).1 hfi)`. Establish `hlocW : ∀ a ∈ maximalIdeal W, f a ∈ maximalIdeal V` using `fun a ha => (mem_maximalIdeal _).2 fun h => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit f a h)`.

Set `Ww : Set (Sp W)` to `abLocus t.G ∩ {p | ϖ ∉ p.asIdeal}`. Establish `hWo : IsOpen Ww` using `(GlobalTheory.AbLocusOpen.isOpen_abLocus_local t.G t.semi).inter (PrimeSpectrum.isOpen_basicOpen (a := ϖ))`. Establish `hkerW : (⟨RingHom.ker f, RingHom.ker_isPrime f⟩ : PrimeSpectrum W) ∈ Ww`. Rewrite using `[ker_eq_spMap_bot, hfbot]`. Use `⟨(abLocus_pullback abLocusOne Y.t.semi mt.cart.1 _).1 hχgen, fun h => hϖ.ne_zero ((Submodule.mem_bot W).1 h)⟩` and prove the remaining obligations.

Establish `hψW : ∀ y, PsiUnitOn P.D.toPre y Ww` using `fun y => hmon.psiUnitOn y fun p hp => by simpa using hp.2`. Take `⟨PV, e₁, he₁⟩` from `GlobalTheory.PelCoordPull.exists_pelUnif_psiCoord E H W V f t tV mV P Ww inferInstance inferInstance hWc inferInstance inferInstance hVc hlocW hWo Set.inter_subset_left hψW hkerW ⟨B, gen, hg, hw⟩`. Establish `hlocC : ∀ a ∈ maximalIdeal (ChartRing k m e), ψ a ∈ maximalIdeal V` using `fun a ha => (mem_maximalIdeal _).2 fun h => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit ψ a h)`. Establish `hvne : ∀ i, ψ (bdParam k m e i) ≠ 0` using `fun i h => by`. Rewrite `h` using `[hv i]`.

Conclude with `mul_ne_zero (v i).ne_zero (pow_ne_zero _ hϖ'.ne_zero) h`. Establish `hgenC : (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum (ChartRing k m e)) ∈ abLocus tC.G`. Rewrite using `[ker_eq_spMap_bot]`. Use `(abLocus_pullback abLocusOne Y.t.semi mC.cart.1 _).1 ?_` and prove the remaining obligations. Establish `key : (ξ ≫ genι Y) (spMap ψ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V)) = χ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum W)` using `(Scheme.Hom.comp_apply (spMap ψ) (ξ ≫ genι Y) _).symm.trans ((congrArg (fun g : Sp V ⟶ Y.X => g (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V)) hc).symm.trans ((Scheme.Hom.comp_apply (spMap f) χ _).trans (congrArg χ hfbot)))`.

Rewrite using `[key]`. Conclude with `hχgen`. Set `Wc : Set (Sp (ChartRing k m e))` to `abLocus tC.G ∩ {p | ∏ i, bdParam k m e i ∉ p.asIdeal}`. Establish `hWco : IsOpen Wc` using `(GlobalTheory.AbLocusOpen.isOpen_abLocus_local tC.G tC.semi).inter (PrimeSpectrum.isOpen_basicOpen (a := ∏ i, bdParam k m e i))`. Establish `hkerC : (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum (ChartRing k m e)) ∈ Wc`.

Use `⟨hgenC, fun h => ?_⟩` and prove the remaining obligations. Establish `h' : ψ (∏ i, bdParam k m e i) = 0` using `(RingHom.mem_ker).1 h`. Rewrite `h'` using `[map_prod]`. Conclude with `Finset.prod_ne_zero_iff.2 (fun i _ => hvne i) h'`. Establish `hψC : ∀ y, PsiUnitOn PC.D.toPre y Wc` using `fun y => hmonC.psiUnitOn y fun p hp => hp.2`.

Take `⟨PCV, e₂, he₂⟩` from `GlobalTheory.PelCoordPull.exists_pelUnif_psiCoord E H (ChartRing k m e) V ψ tC tCV mCV PC Wc inferInstance hCI hCA inferInstance inferInstance hVc hlocC hWco Set.inter_subset_left hψC hkerC ⟨BC, genC, hgC, hwC⟩`. Take `⟨e₃, he₃⟩` from `GlobalTheory.SameCoord.exists_equiv_psiCoord E H V tV tCV k₁ PV PCV inferInstance inferInstance hVc`. Use `⟨(e₁.trans e₃).trans e₂.symm, fun y => ?_⟩` and prove the remaining obligations. Use `set y' := ((e₁.trans e₃).trans e₂.symm) y with hy'`. Establish `hy2 : e₂ y' = e₃ (e₁ y)` using `by simp [hy']`.

Take `⟨u₀, nW, hnW, hcW⟩` from `hmon y`. Take `⟨u₁, h₁⟩` from `he₁ y _ hcW`. Take `⟨u₃, h₃⟩` from `he₃ _ _ h₁`. Take `⟨uC, nC, hnC, hcC⟩` from `hmonC y'`. Take `⟨u₂, h₂⟩` from `he₂ y' _ hcC`.

Rewrite `h₂` using `[hy2]`. Take `⟨w, hw⟩` from `GlobalTheory.PsiCoordLocal.exists_unit_of_coord h₃ h₂`. Establish `hA : (w : V) * (u₃ * (u₁ * f (u₀ * ∏ i, ![ϖ] i ^ nW i))) = ((w * u₃ * u₁ * Units.map f.toMonoidHom u₀ * u ^ nW 0 : Vˣ) : V) * ϖ' ^ (r * nW 0)`. Rewrite using `[Fin.prod_univ_one, Matrix.cons_val_zero, map_mul, map_pow, hu]`. Simplify using `only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hB : (u₂ : V) * ψ (uC * ∏ i, bdParam k m e i ^ nC i) = ((u₂ * Units.map ψ.toMonoidHom uC * ∏ i, v i ^ nC i : Vˣ) : V) * ϖ' ^ (∑ i, n i * nC i)`. Rewrite using `[map_mul, map_prod]`. Repeatedly rewrite using `[map_pow, hv, mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum]`. Simplify using `only [Units.val_mul, Units.coe_prod, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hexp : r * nW 0 = ∑ i, n i * nC i` using `IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ' hϖ' _ _ _ _ (hA.symm.trans (hw.symm.trans hB))`. Establish `h0 : be y y = 2 * nW 0` using `by simpa using hnW 0`. Combine the equalities or inequalities in the displayed calculation. Repeatedly rewrite using `[hnC]`.

Use `push_cast`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem GlobalTheory.TraitChartForm.main : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) {k : Type} [Field k] {m e : ℕ} (ξ : Sp (ChartRing k m e) ⟶ gen Y) {tC : SAB H (Sp (ChartRing k m e))} (_ : SABMap tC Y.t (ξ ≫ genι Y)) (PC : PELUnif (maximalIdeal (ChartRing k m e)) tC) (γ : Fin m → LinearMap.BilinForm ℤ PC.D.toPre.X), IsMonomial PC.D.toPre (bdParam k m e) γ → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (ϖ : W), Irreducible ϖ → ∀ (χ : Sp W ⟶ Y.X) (t : SAB H (Sp W)) (_ : SABMap t Y.t χ) (P : PELUnif (maximalIdeal W) t), Set.range (jK W ≫ χ) ⊆ Set.range Y.j → ∀ (be : LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre ![ϖ] ![be] → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (ϖ' : V), Irreducible ϖ' → ∀ (f : W →+* V) (ψ : ChartRing k m e →+* V), Function.Injective f → IsLocalHom f → IsLocalHom ψ → spMap f ≫ χ = spMap ψ ≫ ξ ≫ genι Y → ∀ (r : ℕ) (u : Vˣ), f ϖ = u * ϖ' ^ r → ∀ (n : Fin m → ℕ) (v : Fin m → Vˣ), (∀ i, ψ (bdParam k m e i) = v i * ϖ' ^ n i) → ∃ ε : P.D.toPre.X ≃ₗ[𝓞 E] PC.D.toPre.X, ∀ y, (r : ℤ) * be y y = ∑ i, (n i : ℤ) * γ i (ε y) (ε y) := by
  intro E _ _ _ H D l Xo c Y k _ m e ξ tC mC PC γ hmonC W _ _ _ hW ϖ hϖ χ t mt P hr be hmon V _ _ _ hV ϖ' hϖ' f ψ hfi
    hfl hψl hc r u hu n v hv
  obtain ⟨hWd, hWc, hW0⟩ := hW
  obtain ⟨hVd, hVc, hV0⟩ := hV
  obtain ⟨L₁, L₂, -⟩ := GlobalTheory.firstFiveLaws
  have : CharZero (ChartRing k m e) :=
    (Spec.preimage (ξ ≫ genStr Y)).hom.charZero_iff (RingHom.injective _) |>.1 inferInstance
  have : IsRegularLocalRing (ChartRing k m e) := GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k (Fin m ⊕ Fin e)
  have hCI : IsIntegrallyClosed (ChartRing k m e) := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing _).2
  have : IsAdicComplete (maximalIdeal k) k := by rw [maximalIdeal_eq_bot]; infer_instance
  have hCA : IsAdicComplete (maximalIdeal (ChartRing k m e)) (ChartRing k m e) :=
    GlobalTheory.PlaceInt.isAdicComplete_mvPowerSeries_finite (V := k) _

  obtain ⟨tV, ⟨mV⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap f) t
  obtain ⟨tCV, ⟨mCV⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap ψ) tC
  obtain ⟨n₁⟩ := GlobalTheory.TraitOrder.comp rfl mt mV
  obtain ⟨n₂⟩ := GlobalTheory.TraitOrder.comp rfl mC mCV
  obtain ⟨k₁⟩ := GlobalTheory.TraitOrder.cancel (show 𝟙 _ ≫ (spMap f ≫ χ) = spMap ψ ≫ ξ ≫ genι Y by rw [Category.id_comp, hc])
    n₁ n₂

  have j : Function.Injective ((algebraMap V (FractionRing V)).comp f) := (IsFractionRing.injective V _).comp hfi
  let g : FractionRing W →+* FractionRing V := IsFractionRing.lift j
  have eg : jK V ≫ spMap f = spMap g ≫ jK W :=
    (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).symm
  have hpV : PolAt tV (jK V) := GlobalTheory.DatUniq.polAt_pull mV (GlobalTheory.DatUniq.polAt_of_unif P) (jK V) (spMap g) eg.symm
  have hpCV : PolAt tCV (jK V) :=
    GlobalTheory.DatUniq.polAt_pull k₁ hpV (jK V) (𝟙 _) (by rw [Category.id_comp, Category.comp_id])
  obtain ⟨B, -, gen, hg, hw, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt L₁ L₂ E H V tV hpV
  obtain ⟨BC, -, genC, hgC, hwC, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt L₁ L₂ E H V tCV hpCV

  have hχgen : χ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum W) ∈ abLocus Y.t.G := by
    let p : Sp (FractionRing W) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing W))
    obtain ⟨w, hw⟩ := hr ⟨p, rfl⟩
    rw [← jK_apply_eq_bot W p, ← Scheme.Hom.comp_apply, ← hw]
    exact j_mem_abLocus Y w
  have hfbot : spMap f (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V) = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum W) := by
    rw [← ker_eq_spMap_bot]
    exact PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot f).1 hfi)

  have hlocW : ∀ a ∈ maximalIdeal W, f a ∈ maximalIdeal V := fun a ha =>
    (mem_maximalIdeal _).2 fun h => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit f a h)
  let Ww : Set (Sp W) := abLocus t.G ∩ {p | ϖ ∉ p.asIdeal}
  have hWo : IsOpen Ww :=
    (GlobalTheory.AbLocusOpen.isOpen_abLocus_local t.G t.semi).inter (PrimeSpectrum.isOpen_basicOpen (a := ϖ))
  have hkerW : (⟨RingHom.ker f, RingHom.ker_isPrime f⟩ : PrimeSpectrum W) ∈ Ww := by
    rw [ker_eq_spMap_bot, hfbot]
    refine ⟨(abLocus_pullback abLocusOne Y.t.semi mt.cart.1 _).1 hχgen, fun h => hϖ.ne_zero ((Submodule.mem_bot W).1 h)⟩
  have hψW : ∀ y, PsiUnitOn P.D.toPre y Ww := fun y => hmon.psiUnitOn y fun p hp => by simpa using hp.2
  obtain ⟨PV, e₁, he₁⟩ := GlobalTheory.PelCoordPull.exists_pelUnif_psiCoord E H W V f t tV mV P Ww inferInstance inferInstance
    hWc inferInstance inferInstance hVc hlocW hWo Set.inter_subset_left hψW hkerW ⟨B, gen, hg, hw⟩

  have hlocC : ∀ a ∈ maximalIdeal (ChartRing k m e), ψ a ∈ maximalIdeal V := fun a ha =>
    (mem_maximalIdeal _).2 fun h => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit ψ a h)
  have hvne : ∀ i, ψ (bdParam k m e i) ≠ 0 := fun i h => by
    rw [hv i] at h
    exact mul_ne_zero (v i).ne_zero (pow_ne_zero _ hϖ'.ne_zero) h
  have hgenC : (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum (ChartRing k m e)) ∈ abLocus tC.G := by
    rw [ker_eq_spMap_bot]
    refine (abLocus_pullback abLocusOne Y.t.semi mC.cart.1 _).1 ?_
    have key : (ξ ≫ genι Y) (spMap ψ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V)) =
        χ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum W) :=
      (Scheme.Hom.comp_apply (spMap ψ) (ξ ≫ genι Y) _).symm.trans
        ((congrArg (fun g : Sp V ⟶ Y.X => g (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V)) hc).symm.trans
          ((Scheme.Hom.comp_apply (spMap f) χ _).trans (congrArg χ hfbot)))
    rw [key]
    exact hχgen
  let Wc : Set (Sp (ChartRing k m e)) := abLocus tC.G ∩ {p | ∏ i, bdParam k m e i ∉ p.asIdeal}
  have hWco : IsOpen Wc := (GlobalTheory.AbLocusOpen.isOpen_abLocus_local tC.G tC.semi).inter
    (PrimeSpectrum.isOpen_basicOpen (a := ∏ i, bdParam k m e i))
  have hkerC : (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum (ChartRing k m e)) ∈ Wc := by
    refine ⟨hgenC, fun h => ?_⟩
    have h' : ψ (∏ i, bdParam k m e i) = 0 := (RingHom.mem_ker).1 h
    rw [map_prod] at h'
    exact Finset.prod_ne_zero_iff.2 (fun i _ => hvne i) h'
  have hψC : ∀ y, PsiUnitOn PC.D.toPre y Wc := fun y => hmonC.psiUnitOn y fun p hp => hp.2
  obtain ⟨PCV, e₂, he₂⟩ := GlobalTheory.PelCoordPull.exists_pelUnif_psiCoord E H (ChartRing k m e) V ψ tC tCV mCV PC Wc
    inferInstance hCI hCA inferInstance inferInstance hVc hlocC hWco Set.inter_subset_left hψC hkerC
    ⟨BC, genC, hgC, hwC⟩

  obtain ⟨e₃, he₃⟩ := GlobalTheory.SameCoord.exists_equiv_psiCoord E H V tV tCV k₁ PV PCV inferInstance inferInstance hVc
  refine ⟨(e₁.trans e₃).trans e₂.symm, fun y => ?_⟩
  set y' := ((e₁.trans e₃).trans e₂.symm) y with hy'
  have hy2 : e₂ y' = e₃ (e₁ y) := by simp [hy']
  obtain ⟨u₀, nW, hnW, hcW⟩ := hmon y
  obtain ⟨u₁, h₁⟩ := he₁ y _ hcW
  obtain ⟨u₃, h₃⟩ := he₃ _ _ h₁
  obtain ⟨uC, nC, hnC, hcC⟩ := hmonC y'
  obtain ⟨u₂, h₂⟩ := he₂ y' _ hcC
  rw [hy2] at h₂
  obtain ⟨w, hw⟩ := GlobalTheory.PsiCoordLocal.exists_unit_of_coord h₃ h₂
  have hA : (w : V) * (u₃ * (u₁ * f (u₀ * ∏ i, ![ϖ] i ^ nW i))) =
      ((w * u₃ * u₁ * Units.map f.toMonoidHom u₀ * u ^ nW 0 : Vˣ) : V) * ϖ' ^ (r * nW 0) := by
    rw [Fin.prod_univ_one, Matrix.cons_val_zero, map_mul, map_pow, hu]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
    ring
  have hB : (u₂ : V) * ψ (uC * ∏ i, bdParam k m e i ^ nC i) =
      ((u₂ * Units.map ψ.toMonoidHom uC * ∏ i, v i ^ nC i : Vˣ) : V) * ϖ' ^ (∑ i, n i * nC i) := by
    rw [map_mul, map_prod]
    simp_rw [map_pow, hv, mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum]
    simp only [Units.val_mul, Units.coe_prod, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe,
      RingHom.toMonoidHom_eq_coe]
    ring
  have hexp : r * nW 0 = ∑ i, n i * nC i :=
    IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ' hϖ' _ _ _ _ (hA.symm.trans (hw.symm.trans hB))
  have h0 : be y y = 2 * nW 0 := by simpa using hnW 0
  calc (r : ℤ) * be y y = 2 * ((r * nW 0 : ℕ) : ℤ) := by rw [h0]; push_cast; ring
    _ = 2 * ((∑ i, n i * nC i : ℕ) : ℤ) := by rw [hexp]
    _ = ∑ i, (n i : ℤ) * γ i y' y' := by
      simp_rw [hnC]
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
