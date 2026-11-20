import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePointsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOneStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsValuationSubringComplexComapValEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentGeometricallyIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComponentSurjectsClopenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftAlgebraicallyClosedPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentSurjectsOfOpenClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelComponentIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelChangeMapStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c hpq hA hgood hfac Z la p n hp hpla`. Set `l' : Level H` to `{ l with A := p ^ n, A_pos := pow_pos hp.pos n }`. Establish `hdvd : l.Dvd l'` using `⟨dvd_rfl, le_rfl, by rw [hA]; exact one_dvd _⟩`. Set `fam : ∀ l₀ : Level H, Moduli Dw l₀` to `fun l₀ => Classical.choice (GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.1 E H Dw l₀ hpq)`. Set `Xo'` to `fam l'`.

Take `⟨c₁⟩ : Nonempty (Coeff l')` from `inferInstance`. Set `c₀ : Coeff l'` to `{ F := c.F ⊔ c₁.F fin := by`. Use `c.fin` as an intermediate fact. Use `c₁.fin` as an intermediate fact. Conclude with `IntermediateField.finiteDimensional_sup _ _`.

Use `conj := fun τ a => (le_sup_right : c₁.F ≤ c.F ⊔ c₁.F) (c₁.conj τ a)`. Use `zeta_mem := (le_sup_right : c₁.F ≤ c.F ⊔ c₁.F) c₁.zeta_mem`. Use `le := c₁.le.trans le_sup_right }`. Take `⟨-, c', hc', hall⟩` from `GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed E H Dw l' Xo' c₀ hpq`. Establish `hfac' : FnAlgClosed Xo' c'` using `hall c' le_rfl`.

Establish `hle : c.F ≤ c'.F` using `le_sup_left.trans hc'`. Establish `hpU : (p : c.F) ∈ (la.valuation c.F).valuationSubring.nonunits`. Rewrite using `[ValuationSubring.mem_nonunits_iff]`. Establish `h1 : la.valuation c.F (algebraMap (𝓞 c.F) c.F (p : 𝓞 c.F)) < 1` using `(HeightOneSpectrum.valuation_lt_one_iff_mem la _).2 hpla`. Rewrite `h1` using `[map_natCast]`.

Conclude with `((Valuation.isEquiv_valuation_valuationSubring (la.valuation c.F)).lt_one_iff_lt_one).1 h1`. Take `⟨W, hpW, hWU⟩` from `GlobalTheory.exists_valuationSubring_complex_comap_val_eq c.F _ p hpU`. Take `⟨Ysys, -⟩` from `GlobalTheory.T.compactifiedModuli_partOne.2 E H Dw hpq fam`. Set `Y : Model Xo' c' (c'.V W).subtype` to `Ysys p W hp hpW ⟨l', c', hgood p hp⟩`. Take `⟨r, hr, r₀, m, hr₀, hfin, het, hsurj⟩` from `GlobalTheory.T.exists_level_change_map E H Dw l l' Xo Xo' c c' hle hpq hdvd`.

Take `⟨ν₀, -⟩` from `GlobalTheory.ObjMaps.exists_sab_comp m Y.m0.toSABMap`. Take `⟨U, hUZ, hUirr, hUlift⟩` from `GlobalTheory.T.component_surjects_of_open_closed GlobalTheory.T.exists_component_surjects_clopen GlobalTheory.T.exists_lift_algebraically_closed_point E H Dw l l' Xo Xo' c c' hle (GlobalTheory.T.component_geometrically_irreducible E H Dw l Xo c hfac) (GlobalTheory.T.component_geo …`. Take `⟨Xw, hXj, hXp, hXU, hXg⟩` from `GlobalTheory.T.integral_model_component_irreducible E H Dw l' Xo' c' W Y p hp hpW U hUirr`. Use `⟨l', Xo', c', W, Y, r, hr₀ ▸ ν₀, hle, Xw, rfl, hr, fun x => ?_, hpW, ?_, hXj, hXp, fun z hz => hUZ z ((hXU z).1 hz), hXg, ?_⟩` and prove the remaining obligations. Rewrite using `[← Valuation.mem_valuationSubring_iff, ← hWU, ValuationSubring.mem_comap]`.

Both sides reduce to the same expression. Establish `h` using `hpW`. Rewrite `h`, the goal using `[ValuationSubring.mem_nonunits_iff_or]`. Break down `h with h | h` into its components or cases. Conclude with `absurd (by exact_mod_cast h) hp.ne_zero`.

Conclude with `Or.inr fun h' => h (by simpa [Coeff.V] using h')`. Introduce `k _ _ fK x hx hxZ`. Take `⟨yy, h1, h2, h3⟩` from `hUlift k fK x hx hxZ`. Use `⟨yy, h1, h2, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨w, rfl⟩`.

Conclude with `(hXU _).2 (h3 ⟨w, rfl⟩)`.
-/
theorem coverSt_holds : CoverSt := by
  intro E _ _ _ H Dw l Xo c hpq hA hgood hfac Z la p n hp hpla
  classical
  let l' : Level H := { l with A := p ^ n, A_pos := pow_pos hp.pos n }
  have hdvd : l.Dvd l' := ⟨dvd_rfl, le_rfl, by rw [hA]; exact one_dvd _⟩
  let fam : ∀ l₀ : Level H, Moduli Dw l₀ := fun l₀ => Classical.choice (GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.1 E H Dw l₀ hpq)
  let Xo' := fam l'
  obtain ⟨c₁⟩ : Nonempty (Coeff l') := inferInstance
  let c₀ : Coeff l' :=
    { F := c.F ⊔ c₁.F
      fin := by
        have := c.fin
        have := c₁.fin
        exact IntermediateField.finiteDimensional_sup _ _
      conj := fun τ a => (le_sup_right : c₁.F ≤ c.F ⊔ c₁.F) (c₁.conj τ a)
      zeta_mem := (le_sup_right : c₁.F ≤ c.F ⊔ c₁.F) c₁.zeta_mem
      le := c₁.le.trans le_sup_right }
  obtain ⟨-, c', hc', hall⟩ := GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed E H Dw l' Xo' c₀ hpq
  have hfac' : FnAlgClosed Xo' c' := hall c' le_rfl
  have hle : c.F ≤ c'.F := le_sup_left.trans hc'
  have hpU : (p : c.F) ∈ (la.valuation c.F).valuationSubring.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff]
    have h1 : la.valuation c.F (algebraMap (𝓞 c.F) c.F (p : 𝓞 c.F)) < 1 :=
      (HeightOneSpectrum.valuation_lt_one_iff_mem la _).2 hpla
    rw [map_natCast] at h1
    exact ((Valuation.isEquiv_valuation_valuationSubring (la.valuation c.F)).lt_one_iff_lt_one).1 h1
  obtain ⟨W, hpW, hWU⟩ := GlobalTheory.exists_valuationSubring_complex_comap_val_eq c.F _ p hpU
  obtain ⟨Ysys, -⟩ := GlobalTheory.T.compactifiedModuli_partOne.2 E H Dw hpq fam
  let Y : Model Xo' c' (c'.V W).subtype := Ysys p W hp hpW ⟨l', c', hgood p hp⟩
  obtain ⟨r, hr, r₀, m, hr₀, hfin, het, hsurj⟩ := GlobalTheory.T.exists_level_change_map E H Dw l l' Xo Xo' c c' hle hpq hdvd
  obtain ⟨ν₀, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp m Y.m0.toSABMap
  obtain ⟨U, hUZ, hUirr, hUlift⟩ := GlobalTheory.T.component_surjects_of_open_closed GlobalTheory.T.exists_component_surjects_clopen GlobalTheory.T.exists_lift_algebraically_closed_point E H Dw l l' Xo Xo' c c' hle (GlobalTheory.T.component_geometrically_irreducible E H Dw l Xo c hfac)
    (GlobalTheory.T.component_geometrically_irreducible E H Dw l' Xo' c' hfac') r hr hfin het hsurj Z
  obtain ⟨Xw, hXj, hXp, hXU, hXg⟩ := GlobalTheory.T.integral_model_component_irreducible E H Dw l' Xo' c' W Y p hp hpW U hUirr
  refine ⟨l', Xo', c', W, Y, r, hr₀ ▸ ν₀, hle, Xw, rfl, hr, fun x => ?_, hpW, ?_, hXj, hXp,
    fun z hz => hUZ z ((hXU z).1 hz), hXg, ?_⟩
  · rw [← Valuation.mem_valuationSubring_iff, ← hWU, ValuationSubring.mem_comap]
    rfl
  · have h := hpW
    rw [ValuationSubring.mem_nonunits_iff_or] at h ⊢
    rcases h with h | h
    · exact absurd (by exact_mod_cast h) hp.ne_zero
    · exact Or.inr fun h' => h (by simpa [Coeff.V] using h')
  · intro k _ _ fK x hx hxZ
    obtain ⟨yy, h1, h2, h3⟩ := hUlift k fK x hx hxZ
    refine ⟨yy, h1, h2, ?_⟩
    rintro _ ⟨w, rfl⟩
    exact (hXU _).2 (h3 ⟨w, rfl⟩)

end GlobalTheory.FlatModel

end
