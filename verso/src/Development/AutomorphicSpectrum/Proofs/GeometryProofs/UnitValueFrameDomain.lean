import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentFourth
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAtStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentresStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameDomainInSegreChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.UnitValue

/- English proof (translation)
Establish `hu : u = f⁻¹ ^ n * (f ^ n * u)`. Rewrite using `[← _root_.mul_assoc, ← _root_.mul_pow, inv_mul_cancel₀ hf, _root_.one_pow, _root_.one_mul]`. Rewrite using `[hu]`. Conclude with `mul_mem (pow_mem hf' n) h`.
-/
theorem mem_regAt_of_pow_mul {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ}
    {f u : Ω} (hf : f ≠ 0) (hf' : f⁻¹ ∈ regAt ξ p) {n : ℕ} (h : f ^ n * u ∈ regAt ξ p) : u ∈ regAt ξ p := by
  have hu : u = f⁻¹ ^ n * (f ^ n * u) := by
    rw [← _root_.mul_assoc, ← _root_.mul_pow, inv_mul_cancel₀ hf, _root_.one_pow, _root_.one_mul]
  rw [hu]
  exact mul_mem (pow_mem hf' n) h

/- English proof (translation)
Take `⟨h, s, hs, rfl⟩` from `h1`. Take `⟨h', s', hs', rfl⟩` from `h2`. Establish `hss : s = s'` using `hg.inj ⟨GlobalTheory.CompanionTheory.Ar.centre z, h⟩ (hs.trans hs'.symm)`. Rewrite using `[hss]`.
-/
private theorem valAt_unique_lemma {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hg : GlobalTheory.CompanionTheory.Ar.IsCptGen ξ) {z : Spec (CommRingCat.of ℂ) ⟶ X} {a : Ω} {r r' : ℂ}
    (h1 : GlobalTheory.CompanionTheory.Ar.ValAt ξ z a r) (h2 : GlobalTheory.CompanionTheory.Ar.ValAt ξ z a r') : r = r' := by
  obtain ⟨h, s, hs, rfl⟩ := h1
  obtain ⟨h', s', hs', rfl⟩ := h2
  have hss : s = s' := hg.inj ⟨GlobalTheory.CompanionTheory.Ar.centre z, h⟩ (hs.trans hs'.symm)
  rw [hss]

/- English proof (translation)
Take `⟨h', s, hs, hsv⟩` from `h`. Establish `hsu : IsUnit s`. Establish `hi : IsUnit ((Scheme.stalkClosedPointTo z).hom s)`. Rewrite using `[hsv]`. Conclude with `hv.isUnit`.

Establish `hloc : IsLocalHom (Scheme.stalkClosedPointTo z).hom` using `by infer_instance`. Conclude with `hloc.map_nonunit s hi`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hs]`. Conclude with `(hsu.map (GlobalTheory.CompanionTheory.Ar.genMap ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, h'⟩)).ne_zero`.

Establish `hva : ∃ r : ℂ, GlobalTheory.CompanionTheory.Ar.ValAt ξ z a⁻¹ r`. Use `⟨_, h', ↑hsu.unit⁻¹, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[map_units_inv, IsUnit.unit_spec, hs]`. Take `⟨r, hr⟩` from `hva`. Conclude with `GlobalTheory.CompanionTheory.Ar.ChgUnit.mem_regAt_of_valAt hr _ rfl`.
-/
private theorem ne_zero_and_inv_mem_regAt_of_valAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {z : Spec (CommRingCat.of ℂ) ⟶ X} (hz : GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ GlobalTheory.CompanionTheory.Ar.centre z) {a : Ω} {v : ℂ}
    (hv : v ≠ 0) (h : GlobalTheory.CompanionTheory.Ar.ValAt ξ z a v) :
    a ≠ 0 ∧ a⁻¹ ∈ GlobalTheory.CompanionTheory.Ar.regAt ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, hz⟩ := by
  obtain ⟨h', s, hs, hsv⟩ := h
  have hsu : IsUnit s := by
    have hi : IsUnit ((Scheme.stalkClosedPointTo z).hom s) := by
      rw [hsv]; exact hv.isUnit
    have hloc : IsLocalHom (Scheme.stalkClosedPointTo z).hom := by infer_instance
    exact hloc.map_nonunit s hi
  refine ⟨?_, ?_⟩
  · rw [← hs]
    exact (hsu.map (GlobalTheory.CompanionTheory.Ar.genMap ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, h'⟩)).ne_zero
  · have hva : ∃ r : ℂ, GlobalTheory.CompanionTheory.Ar.ValAt ξ z a⁻¹ r := by
      refine ⟨_, h', ↑hsu.unit⁻¹, ?_, rfl⟩
      rw [map_units_inv, IsUnit.unit_spec, hs]
    obtain ⟨r, hr⟩ := hva
    exact GlobalTheory.CompanionTheory.Ar.ChgUnit.mem_regAt_of_valAt hr _ rfl

/- English proof (translation)
Introduce `X Ω _ ξ K _ J _ y z w cc f u hT hz hC hF hU`. Establish `hequiv` using `GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z w hz hC`. Establish `hch` using `GlobalTheory.CompanionTheory.Ar.ChgUnit.inChart_of_coordsAt hC cc (fun k => (hF.1 k).isUnit) ⟨GlobalTheory.CompanionTheory.Ar.centre z, hz⟩ rfl`. Establish `hreg : ∀ a, a ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing ℤ (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) cc → a ∈ GlobalTheory.CompanionTheory.Ar.regAt ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, hz⟩` using `fun a ha => (hT.ring cc hch.1 a).1 ha _ hch`. Take `⟨v, hv, hv0⟩` from `hF.2`.

Take `⟨hf0, hfi⟩` from `ne_zero_and_inv_mem_regAt_of_valAt hz hv0 ((hequiv f v).2 hv)`. Take `⟨hu0, ⟨n, hn⟩, ⟨m, hm⟩⟩` from `hU`. Establish `hu` using `mem_regAt_of_pow_mul hf0 hfi (hreg _ hn)`. Establish `hui` using `mem_regAt_of_pow_mul hf0 hfi (hreg _ hm)`. Take `⟨r, hr0, hr⟩` from `GlobalTheory.CompanionTheory.Ar.ChgUnit.exists_value_of_unit hT.gen z hz hu0 hu hui`.

Establish `hex : ∃ v, GroundTheory.Heights₂.Heights.LowerBoundFree.IsValueAt y u w v` using `⟨r, (hequiv u r).1 hr⟩`. Establish `hval : GroundTheory.Heights₂.Heights.LowerBoundFree.valAt y u w = hex.choose`. Rewrite using `[GroundTheory.Heights₂.Heights.LowerBoundFree.valAt, dif_pos hex]`. Establish `hc : GlobalTheory.CompanionTheory.Ar.ValAt ξ z u hex.choose` using `(hequiv u _).2 hex.choose_spec`. Establish `heq : hex.choose = r` using `valAt_unique_lemma hT.gen hc hr`.

Rewrite using `[hval, heq]`. Conclude with `⟨hr0, hr⟩`.
-/
theorem valAt_ne_zero_of_isUnitOn : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ) (cc : (k : K) → J k) (f u : Ω), CoordTie ℤ ξ (segreCoord y) → genPt ξ ⤳ centre z → CoordsAt ξ y z w → InFrameDomain y cc f w → IsUnitOn y cc f u → valAt y u w ≠ 0 ∧ ValAt ξ z u (valAt y u w) := by
  intro X Ω _ ξ K _ J _ y z w cc f u hT hz hC hF hU
  have hequiv := GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z w hz hC
  have hch := GlobalTheory.CompanionTheory.Ar.ChgUnit.inChart_of_coordsAt hC cc (fun k => (hF.1 k).isUnit)
    ⟨GlobalTheory.CompanionTheory.Ar.centre z, hz⟩ rfl
  have hreg : ∀ a, a ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing ℤ (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) cc →
      a ∈ GlobalTheory.CompanionTheory.Ar.regAt ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, hz⟩ :=
    fun a ha => (hT.ring cc hch.1 a).1 ha _ hch
  obtain ⟨v, hv, hv0⟩ := hF.2
  obtain ⟨hf0, hfi⟩ := ne_zero_and_inv_mem_regAt_of_valAt hz hv0 ((hequiv f v).2 hv)
  obtain ⟨hu0, ⟨n, hn⟩, ⟨m, hm⟩⟩ := hU
  have hu := mem_regAt_of_pow_mul hf0 hfi (hreg _ hn)
  have hui := mem_regAt_of_pow_mul hf0 hfi (hreg _ hm)
  obtain ⟨r, hr0, hr⟩ := GlobalTheory.CompanionTheory.Ar.ChgUnit.exists_value_of_unit hT.gen z hz hu0 hu hui
  have hex : ∃ v, GroundTheory.Heights₂.Heights.LowerBoundFree.IsValueAt y u w v := ⟨r, (hequiv u r).1 hr⟩
  have hval : GroundTheory.Heights₂.Heights.LowerBoundFree.valAt y u w = hex.choose := by
    rw [GroundTheory.Heights₂.Heights.LowerBoundFree.valAt, dif_pos hex]
  have hc : GlobalTheory.CompanionTheory.Ar.ValAt ξ z u hex.choose := (hequiv u _).2 hex.choose_spec
  have heq : hex.choose = r := valAt_unique_lemma hT.gen hc hr
  rw [hval, heq]
  exact ⟨hr0, hr⟩

end GlobalTheory.CompanionTheory.Ar.UnitValue
