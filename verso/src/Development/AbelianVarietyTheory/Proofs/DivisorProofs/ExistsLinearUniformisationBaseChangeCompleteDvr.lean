import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonomialFormOnChartRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PsiUnitOnOfNeUniv
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperIffOfSplit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc Formalism.L2.Pj
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnifDvrBaseChange

/- English proof (translation)
Introduce `E _ _ _ H V _ _ _ hV t P W _ _ _ hW hWd f hfi hfl tW ⟨m⟩`. Take `⟨hVd, hVc, hV0⟩` from `hV`. Take `⟨⟨hWN, -, hWI, hWc⟩, hW0⟩` from `hW`. Take `⟨L₁, L₂, -⟩` from `GlobalTheory.firstFiveLaws`. Establish `j : Function.Injective ((algebraMap W (FractionRing W)).comp f)` using `(IsFractionRing.injective W _).comp hfi`.

Set `g : FractionRing V →+* FractionRing W` to `IsFractionRing.lift j`. Establish `eg : jK W ≫ spMap f = spMap g ≫ jK V` using `(GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).trans (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).symm`. Establish `hpW : GlobalTheory.LN.PolAt tW (jK W)` using `GlobalTheory.DatUniq.polAt_pull m (GlobalTheory.DatUniq.polAt_of_unif P) (jK W) (spMap g) eg.symm`. Take `⟨B, -, gen, hg, hw, -⟩` from `GlobalTheory.LN.exists_polAV_of_polAt L₁ L₂ E H W tW hpW`. Use `t.semi.separated` as an intermediate fact.

Use `t.semi.smooth` as an intermediate fact. Set `p₀ : Sp (FractionRing V)` to `(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))`. Establish `hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V) ∈ abLocus t.G`. Rewrite using `[← GlobalTheory.TraitChartForm.jK_apply_eq_bot V p₀]`. Conclude with `(GlobalTheory.ZJ.AbelianLocus.mem_abLocus_iff t.G (IsPullback.of_hasPullback t.G.hom (jK V)) p₀).2 (GlobalTheory.DatUniq.polAt_of_unif P).1`.

Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible V`. Set `Wv : Set (Sp V)` to `abLocus t.G ∩ {p | ϖ ∉ p.asIdeal}`. Establish `hWo : IsOpen Wv` using `(GlobalTheory.AbLocusOpen.isOpen_abLocus_local t.G t.semi).inter (PrimeSpectrum.isOpen_basicOpen (a := ϖ))`. Establish `hne : Wv ≠ Set.univ` using `fun h => by`. Establish `: closedPoint V ∈ Wv` using `h ▸ Set.mem_univ _`.

Conclude with `this.2 hϖ.not_isUnit`. Establish `hψ : ∀ y, PsiUnitOn P.D.toPre y Wv` using `fun y => GlobalTheory.DvrDataCompare.psiUnitOn_of_ne_univ P.D.toPre y hne`. Establish `hker : (⟨RingHom.ker f, RingHom.ker_isPrime f⟩ : PrimeSpectrum V) ∈ Wv`. Establish `hk : (⟨RingHom.ker f, RingHom.ker_isPrime f⟩ : PrimeSpectrum V) = ⟨⊥, Ideal.isPrime_bot⟩` using `PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot f).1 hfi)`. Rewrite using `[hk]`.

Conclude with `⟨hgen, fun h => hϖ.ne_zero ((Submodule.mem_bot V).1 h)⟩`. Establish `hloc : ∀ a ∈ maximalIdeal V, f a ∈ maximalIdeal W` using `fun a ha => (mem_maximalIdeal _).2 fun h => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit f a h)`. Take `⟨PW, e, he⟩` from `GlobalTheory.PelCoordPull.exists_pelUnif_psiCoord E H V W f t tW m P Wv inferInstance inferInstance hVc hWN hWI hWc hloc hWo Set.inter_subset_left hψ hker ⟨B, gen, hg, hw⟩`. Use `⟨PW, e.symm, fun y r hr => ?_⟩` and prove the remaining obligations. Take `⟨u, hu⟩` from `he _ r hr`.

Conclude with `⟨u, by simpa using hu⟩`.
-/
theorem exists_pelUnif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V], CDvr V → ∀ (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (W : Type) [CommRing W] [IsDomain W]
    [IsLocalRing W], GlobalTheory.Mum.Base W → IsDiscreteValuationRing W → ∀ f : V →+* W, Function.Injective f → IsLocalHom f →
    ∀ tW : SAB H (Sp W), Nonempty (SABMap tW t (spMap f)) →
      ∃ (PW : PELUnif (maximalIdeal W) tW) (e : PW.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X),
        ∀ y r, PsiCoord P.D.toPre (e y) r → ∃ u : Wˣ, PsiCoord PW.D.toPre y (u * f r) := by
  intro E _ _ _ H V _ _ _ hV t P W _ _ _ hW hWd f hfi hfl tW ⟨m⟩
  obtain ⟨hVd, hVc, hV0⟩ := hV
  obtain ⟨⟨hWN, -, hWI, hWc⟩, hW0⟩ := hW
  obtain ⟨L₁, L₂, -⟩ := GlobalTheory.firstFiveLaws

  have j : Function.Injective ((algebraMap W (FractionRing W)).comp f) := (IsFractionRing.injective W _).comp hfi
  let g : FractionRing V →+* FractionRing W := IsFractionRing.lift j
  have eg : jK W ≫ spMap f = spMap g ≫ jK V :=
    (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).symm
  have hpW : GlobalTheory.LN.PolAt tW (jK W) := GlobalTheory.DatUniq.polAt_pull m (GlobalTheory.DatUniq.polAt_of_unif P) (jK W) (spMap g) eg.symm
  obtain ⟨B, -, gen, hg, hw, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt L₁ L₂ E H W tW hpW

  have := t.semi.separated
  have := t.semi.smooth
  let p₀ : Sp (FractionRing V) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
  have hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V) ∈ abLocus t.G := by
    rw [← GlobalTheory.TraitChartForm.jK_apply_eq_bot V p₀]
    exact (GlobalTheory.ZJ.AbelianLocus.mem_abLocus_iff t.G (IsPullback.of_hasPullback t.G.hom (jK V)) p₀).2
      (GlobalTheory.DatUniq.polAt_of_unif P).1

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let Wv : Set (Sp V) := abLocus t.G ∩ {p | ϖ ∉ p.asIdeal}
  have hWo : IsOpen Wv :=
    (GlobalTheory.AbLocusOpen.isOpen_abLocus_local t.G t.semi).inter (PrimeSpectrum.isOpen_basicOpen (a := ϖ))
  have hne : Wv ≠ Set.univ := fun h => by
    have : closedPoint V ∈ Wv := h ▸ Set.mem_univ _
    exact this.2 hϖ.not_isUnit
  have hψ : ∀ y, PsiUnitOn P.D.toPre y Wv := fun y => GlobalTheory.DvrDataCompare.psiUnitOn_of_ne_univ P.D.toPre y hne
  have hker : (⟨RingHom.ker f, RingHom.ker_isPrime f⟩ : PrimeSpectrum V) ∈ Wv := by
    have hk : (⟨RingHom.ker f, RingHom.ker_isPrime f⟩ : PrimeSpectrum V) = ⟨⊥, Ideal.isPrime_bot⟩ :=
      PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot f).1 hfi)
    rw [hk]
    exact ⟨hgen, fun h => hϖ.ne_zero ((Submodule.mem_bot V).1 h)⟩
  have hloc : ∀ a ∈ maximalIdeal V, f a ∈ maximalIdeal W := fun a ha =>
    (mem_maximalIdeal _).2 fun h => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit f a h)
  obtain ⟨PW, e, he⟩ := GlobalTheory.PelCoordPull.exists_pelUnif_psiCoord E H V W f t tW m P Wv inferInstance inferInstance
    hVc hWN hWI hWc hloc hWo Set.inter_subset_left hψ hker ⟨B, gen, hg, hw⟩
  refine ⟨PW, e.symm, fun y r hr => ?_⟩
  obtain ⟨u, hu⟩ := he _ r hr
  exact ⟨u, by simpa using hu⟩

end GlobalTheory.UnifDvrBaseChange
