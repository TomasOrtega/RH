import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LatticeModelCharts

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef

namespace GlobalTheory.TorRef

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c Z hArc T b ϖ a y hϖ hys hj hA`. Establish `hb : Function.Injective b`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Assume the negation of the conclusion as `h0`.

Take `⟨d, hd⟩` from `Algebra.dvd_algebraMap_intNorm_self ℤ (𝓞 c.F) x`. Establish `hn : Algebra.intNorm ℤ (𝓞 c.F) x ≠ 0` using `Algebra.intNorm_ne_zero.2 h0`. Establish `h1 : b (algebraMap ℤ (𝓞 c.F) (Algebra.intNorm ℤ (𝓞 c.F) x)) = 0`. Rewrite using `[hd, map_mul, hx, zero_mul]`. Rewrite `h1` using `[eq_intCast, map_intCast, Int.cast_eq_zero]`.

Conclude with `hn h1`. Establish `hm : ϖ ∈ maximalIdeal T.V` using `(mem_maximalIdeal ϖ).2 hϖ.not_isUnit`. Establish `hT : IsDiscreteValuationRing T.V ∧ Irreducible ϖ ∧ IsAdicComplete (Ideal.span {ϖ}) T.V`. Use `⟨inferInstance, hϖ, ?_⟩` and prove the remaining obligations. Rewrite using `[← hϖ.maximalIdeal_eq]`.

Use `infer_instance`. Take `⟨χ, hχ, hlast⟩` from `hArc T.V b ϖ a (Or.inr hT)`. Take `⟨hχs, hχab, -, -⟩` from `(hχ χ).1 rfl`. Take `⟨ev, hevC, hevX⟩` from `GlobalTheory.IndefiniteRowSideFullHecke.LatticeModelCharts.exists_evalU T.V ϖ hm`. Establish `hy : spMap ev ≫ χ = y` using `hlast hϖ y ev hys hj hA hevC hevX`.

Set `p : Sp (PowerSeries T.V)` to `(⟨Ideal.span {PowerSeries.X}, PowerSeries.span_X_isPrime⟩ : PrimeSpectrum _)`. Set `pt : Sp c.F` to `(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum c.F)`. Establish `hnab : χ p ∉ abLocus Z.t.G` using `fun h => (hχab p).1 h (Ideal.mem_span_singleton_self _)`. Establish `hpt : Z.s (χ p) = spMap (algebraMap (𝓞 c.F) c.F) pt`. Rewrite using `[← Scheme.Hom.comp_apply, hχs]`.

Use `PrimeSpectrum.ext ?_` and prove the remaining obligations. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `PowerSeries.C (b x) ∈ Ideal.span {PowerSeries.X} ↔ algebraMap (𝓞 c.F) c.F x ∈ (⊥ : Ideal c.F)`. Rewrite using `[Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, PowerSeries.constantCoeff_C, Ideal.mem_bot, map_eq_zero_iff _ hb, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 c.F) c.F)]`. Take `⟨z, hz1, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := Z.s) (g := spMap (algebraMap (𝓞 c.F) c.F)) (χ p) pt hpt`.

Establish `hzb : z ∈ genBd Z` using `mem_genBd_iff.2 (by change (pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F))) z ∉ _; rw [hz1]; exact hnab)`. Establish `hle : p ⤳ spMap ev (closedPoint T.V)`. Use `(PrimeSpectrum.le_iff_specializes _ _).1 ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Ideal.span {PowerSeries.X} ≤ Ideal.comap ev (maximalIdeal T.V)`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`.

Express the relevant statement in the definitionally equal form `ev PowerSeries.X ∈ maximalIdeal T.V`. Rewrite using `[hevX]`. Conclude with `hm`. Rewrite using `[← hy]`. Use `show χ (spMap ev (closedPoint T.V)) ∈ _`.

Conclude with `(hle.map χ.continuous).mem_closed isClosed_closure (subset_closure ⟨z, hzb, hz1⟩)`.
-/
theorem closedPoint_mem_closure_genBd_of_arcData : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)), Z.N4 → ∀ (T : CDVR) (b : 𝓞 c.F →+* T.V) (ϖ : T.V) (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) T.V b) (y : Sp T.V ⟶ Z.X), Irreducible ϖ → y ≫ Z.s = spMap b → Set.range (jK T.V ≫ y) ⊆ Set.range Z.j → Z.HasArcData a (Ideal.span {ϖ}) (RingHom.id T.V) ϖ y → y (closedPoint T.V) ∈ closure (genι Z '' (genBd Z : Set (gen Z))) := by
  intro E _ _ _ H D l Xo c Z hArc T b ϖ a y hϖ hys hj hA

  have hb : Function.Injective b := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    obtain ⟨d, hd⟩ := Algebra.dvd_algebraMap_intNorm_self ℤ (𝓞 c.F) x
    have hn : Algebra.intNorm ℤ (𝓞 c.F) x ≠ 0 := Algebra.intNorm_ne_zero.2 h0
    have h1 : b (algebraMap ℤ (𝓞 c.F) (Algebra.intNorm ℤ (𝓞 c.F) x)) = 0 := by
      rw [hd, map_mul, hx, zero_mul]
    rw [eq_intCast, map_intCast, Int.cast_eq_zero] at h1
    exact hn h1
  have hm : ϖ ∈ maximalIdeal T.V := (mem_maximalIdeal ϖ).2 hϖ.not_isUnit
  have hT : IsDiscreteValuationRing T.V ∧ Irreducible ϖ ∧ IsAdicComplete (Ideal.span {ϖ}) T.V := by
    refine ⟨inferInstance, hϖ, ?_⟩
    rw [← hϖ.maximalIdeal_eq]
    infer_instance
  obtain ⟨χ, hχ, hlast⟩ := hArc T.V b ϖ a (Or.inr hT)
  obtain ⟨hχs, hχab, -, -⟩ := (hχ χ).1 rfl
  obtain ⟨ev, hevC, hevX⟩ := GlobalTheory.IndefiniteRowSideFullHecke.LatticeModelCharts.exists_evalU T.V ϖ hm
  have hy : spMap ev ≫ χ = y := hlast hϖ y ev hys hj hA hevC hevX

  let p : Sp (PowerSeries T.V) := (⟨Ideal.span {PowerSeries.X}, PowerSeries.span_X_isPrime⟩ : PrimeSpectrum _)
  let pt : Sp c.F := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum c.F)
  have hnab : χ p ∉ abLocus Z.t.G := fun h => (hχab p).1 h (Ideal.mem_span_singleton_self _)
  have hpt : Z.s (χ p) = spMap (algebraMap (𝓞 c.F) c.F) pt := by
    rw [← Scheme.Hom.comp_apply, hχs]
    refine PrimeSpectrum.ext ?_
    ext x
    change PowerSeries.C (b x) ∈ Ideal.span {PowerSeries.X} ↔ algebraMap (𝓞 c.F) c.F x ∈ (⊥ : Ideal c.F)
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, PowerSeries.constantCoeff_C, Ideal.mem_bot,
      map_eq_zero_iff _ hb, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 c.F) c.F)]
  obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := Z.s)
    (g := spMap (algebraMap (𝓞 c.F) c.F)) (χ p) pt hpt
  have hzb : z ∈ genBd Z := mem_genBd_iff.2 (by change (pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F))) z ∉ _; rw [hz1]; exact hnab)
  have hle : p ⤳ spMap ev (closedPoint T.V) := by
    refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
    change Ideal.span {PowerSeries.X} ≤ Ideal.comap ev (maximalIdeal T.V)
    rw [Ideal.span_le, Set.singleton_subset_iff]
    change ev PowerSeries.X ∈ maximalIdeal T.V
    rw [hevX]
    exact hm
  rw [← hy]
  show χ (spMap ev (closedPoint T.V)) ∈ _
  exact (hle.map χ.continuous).mem_closed isClosed_closure (subset_closure ⟨z, hzb, hz1⟩)

end GlobalTheory.TorRef
