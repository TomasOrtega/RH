import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.KillCokPf.Lem

/- English proof (translation)
Use `letI := e.hom.toAlgebra`. Use `haveI : Algebra.Etale D D₁ := he`. Conclude with `PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation (R := D) (S := D₁)`.
-/
theorem et_isOpenMap {D D₁ : CommRingCat.{0}} (e : D ⟶ D₁) (he : Et e) : IsOpenMap (PrimeSpectrum.comap e.hom) := by
  letI := e.hom.toAlgebra
  haveI : Algebra.Etale D D₁ := he
  exact PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation (R := D) (S := D₁)

/- English proof (translation)
Take `⟨s, hs⟩` from `isCompact_univ.elim_finite_subcover (fun r => Set.range (PrimeSpectrum.comap (e r).hom)) (fun r => (et_isOpenMap (e r) (he r)).isOpen_range) (fun x _ => Set.mem_iUnion.2 ⟨x, hr x⟩)`. Use `⟨s, fun x => ?_⟩` and prove the remaining obligations. Use `hs (Set.mem_univ x)` as an intermediate fact. Simplify using `only [Set.mem_iUnion] at this`. Take `⟨r, hrs, hx⟩` from `this`.

Conclude with `⟨r, hrs, hx⟩`.
-/
theorem finite_subcover {D : CommRingCat.{0}} (D₁ : PrimeSpectrum D → CommRingCat.{0}) (e : ∀ r, D ⟶ D₁ r)
    (he : ∀ r, Et (e r)) (hr : ∀ r, r ∈ Set.range (PrimeSpectrum.comap (e r).hom)) :
    ∃ s : Finset (PrimeSpectrum D), ∀ x : PrimeSpectrum D, ∃ r ∈ s, x ∈ Set.range (PrimeSpectrum.comap (e r).hom) := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun r => Set.range (PrimeSpectrum.comap (e r).hom))
    (fun r => (et_isOpenMap (e r) (he r)).isOpen_range) (fun x _ => Set.mem_iUnion.2 ⟨x, hr x⟩)
  refine ⟨s, fun x => ?_⟩
  have := hs (Set.mem_univ x)
  simp only [Set.mem_iUnion] at this
  obtain ⟨r, hrs, hx⟩ := this
  exact ⟨r, hrs, hx⟩

end LateralTheory.E.KillCokPf.Lem
