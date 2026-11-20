import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
namespace GlobalTheory.AffCover

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

/- English proof (translation)
Use `⟨{a | ∃ i, ∀ p : PrimeSpectrum K, p ∈ PrimeSpectrum.basicOpen a → p ∈ x ⁻¹ᵁ V i}, ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Take `⟨M, hM, hsM⟩` from `Ideal.exists_le_maximal _ hne`. Set `p : PrimeSpectrum K` to `⟨M, hM.isPrime⟩`. Take `⟨i, hi⟩` from `hV p`.

Take `⟨_, ⟨a, rfl⟩, hpa, hsub⟩` from `PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hi (x ⁻¹ᵁ V i).isOpen`. Establish `ha : a ∈ M` using `hsM (Ideal.subset_span ⟨i, fun q hq => hsub hq⟩)`. Conclude with `hpa ha`. Introduce and unpack `⟨a, i, hi⟩`. Use `⟨i, fun q _ => ?_⟩` and prove the remaining obligations.

Establish `hq : PrimeSpectrum.comap (algebraMap K (Localization.Away a)) q ∈ PrimeSpectrum.basicOpen a`. Rewrite using `[← SetLike.mem_coe, ← PrimeSpectrum.localization_away_comap_range (Localization.Away a) a]`. Conclude with `⟨q, rfl⟩`. Conclude with `hi _ hq`.
-/
theorem exists_span_top_basicOpen_cover {K : Type} [CommRing K] {X : Scheme.{0}} (x : Sp K ⟶ X) {ι : Type}
    (V : ι → X.Opens) (hV : ∀ p : Sp K, ∃ i, p ∈ x ⁻¹ᵁ V i) :
    ∃ s : Set K, Ideal.span s = ⊤ ∧
      ∀ a : s, ∃ i, ⊤ ≤ (spMap (algebraMap K (Localization.Away (a : K))) ≫ x) ⁻¹ᵁ V i := by
  refine ⟨{a | ∃ i, ∀ p : PrimeSpectrum K, p ∈ PrimeSpectrum.basicOpen a → p ∈ x ⁻¹ᵁ V i}, ?_, ?_⟩
  · by_contra hne
    obtain ⟨M, hM, hsM⟩ := Ideal.exists_le_maximal _ hne
    let p : PrimeSpectrum K := ⟨M, hM.isPrime⟩
    obtain ⟨i, hi⟩ := hV p
    obtain ⟨_, ⟨a, rfl⟩, hpa, hsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hi (x ⁻¹ᵁ V i).isOpen
    have ha : a ∈ M := hsM (Ideal.subset_span ⟨i, fun q hq => hsub hq⟩)
    exact hpa ha
  · rintro ⟨a, i, hi⟩
    refine ⟨i, fun q _ => ?_⟩
    have hq : PrimeSpectrum.comap (algebraMap K (Localization.Away a)) q ∈ PrimeSpectrum.basicOpen a := by
      rw [← SetLike.mem_coe, ← PrimeSpectrum.localization_away_comap_range (Localization.Away a) a]
      exact ⟨q, rfl⟩
    exact hi _ hq

end GlobalTheory.AffCover
