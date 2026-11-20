import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.TrdegPf
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FieldPair

/- English proof (translation)
Break down `lt_trichotomy D r with hlt | heq | hgt` into its components or cases. Take `⟨d, rfl⟩ : ∃ d, D = d + 1` from `⟨D - 1, by omega⟩`. Take `⟨s, rfl⟩ : ∃ s, r = s + 1` from `⟨r - 1, by omega⟩`. Rewrite `h` using `[Nat.choose_succ_succ]`. Establish `h1` using `Nat.choose_pos (show d ≤ s by omega)`.

Establish `h2` using `Nat.choose_pos (show d + 1 ≤ s by omega)`. Rewrite `h` using `[Nat.succ_eq_add_one]`. Use linear arithmetic over natural numbers and integers. Conclude with `heq`. Rewrite `h` using `[Nat.choose_eq_zero_of_lt hgt]`.

Conclude with `absurd h zero_ne_one`.
-/
theorem eq_of_choose_eq_one_of_pos {r D : ℕ} (hD : 0 < D) (h : r.choose D = 1) : D = r := by
  rcases lt_trichotomy D r with hlt | heq | hgt
  · obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    rw [Nat.choose_succ_succ] at h
    have h1 := Nat.choose_pos (show d ≤ s by omega)
    have h2 := Nat.choose_pos (show d + 1 ≤ s by omega)
    rw [Nat.succ_eq_add_one] at h
    omega
  · exact heq
  · rw [Nat.choose_eq_zero_of_lt hgt] at h
    exact absurd h zero_ne_one

/- English proof (translation)
Introduce `L _ cL Q hQ D x hD hx`. Use `letI := cL.toAlgebra`. Set `c0 : ℂ →+* Q` to `cL.codRestrict Q hQ.const_mem`. Use `letI := c0.toAlgebra`. Use `haveI : IsScalarTower ℂ Q L := IsScalarTower.of_algebraMap_eq' rfl`.

Use `haveI : IsFractionRing Q L := IsFractionRing.of_field Q L fun z => by`. Take `⟨a, ha, b, hb, hb0, e⟩` from `hQ.frac z`. Use `⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `z = a / b`. Rewrite using `[eq_div_iff hb0, e]`.

Use `haveI : Algebra.FormallyEtale Q L := .of_isLocalization (nonZeroDivisors Q)`. Establish `hL : IsFreeGen L (TopForm.formMap D Q.subtype rfl (dForm c0 x))` using `hx.of_isBaseChange (isBaseChange_exteriorPower (KaehlerDifferential.isBaseChange_of_formallyEtale ℂ Q L) D)`. Rewrite `hL` using `[TopForm.formMap_dForm]`. Express the relevant statement in the definitionally equal form `IsFreeGen L (dForm cL fun i => (x i : L)) at hL`. Use `haveI : Algebra.EssFiniteType ℂ Q := hQ.essFiniteType`.

Use `haveI : Algebra.EssFiniteType Q L := .of_isLocalization L (nonZeroDivisors Q)`. Use `haveI : Algebra.EssFiniteType ℂ L := .comp ℂ Q L`. Establish `h1 : Module.finrank L (Forms cL D) = 1`. Establish `e : L ≃ₗ[L] Forms cL D` using `LinearEquiv.ofBijective (LinearMap.toSpanSingleton L _ _) hL`. Rewrite using `[← e.finrank_eq, Module.finrank_self]`.

Rewrite `h1` using `[exteriorPower.finrank_eq]`. Establish `hr` using `eq_of_choose_eq_one_of_pos hD h1`. Establish `hli : LinearIndependent L fun i => KaehlerDifferential.D ℂ L (x i : L)`. Assume the negation of the conclusion as `hc`. Establish `h0 : dForm cL (fun i => (x i : L)) = 0`.

Rewrite using `[dForm_eq]`. Conclude with `(exteriorPower.ιMulti L D).map_linearDependent _ hc`. Rewrite `hL` using `[h0]`. Conclude with `one_ne_zero (hL.1 (a₁ := 1) (a₂ := 0) (by simp))`. Establish `hind : AlgebraicIndependent ℂ fun i => (x i : L)` using `ReciprocityTheory.ChartRestriction.G.AR.differentialIndependence ℂ L D _ hli`.

Establish `htr : Algebra.trdeg ℂ L = D`. Rewrite using `[← rank_kaehler_eq_trdeg, ← Module.finrank_eq_rank]`. Conclude with `hr.symm` after adjusting the coercions. Conclude with `hind.isTranscendenceBasis_of_trdeg_le_of_finite (by rw [htr, Cardinal.mk_fin])`.
-/
theorem trBasis_of_isFreeGen_dForm : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L)
    (hQ : IsLocModel cL Q) (D : ℕ) (x : Fin D → Q), 0 < D →
    IsFreeGen Q (dForm (cL.codRestrict Q hQ.const_mem) x) → TrBasis cL (fun i => (x i : L)) := by
  intro L _ cL Q hQ D x hD hx
  letI := cL.toAlgebra
  let c0 : ℂ →+* Q := cL.codRestrict Q hQ.const_mem
  letI := c0.toAlgebra
  haveI : IsScalarTower ℂ Q L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsFractionRing Q L := IsFractionRing.of_field Q L fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hQ.frac z
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    change z = a / b
    rw [eq_div_iff hb0, e]
  haveI : Algebra.FormallyEtale Q L := .of_isLocalization (nonZeroDivisors Q)
  have hL : IsFreeGen L (TopForm.formMap D Q.subtype rfl (dForm c0 x)) :=
    hx.of_isBaseChange (isBaseChange_exteriorPower
      (KaehlerDifferential.isBaseChange_of_formallyEtale ℂ Q L) D)
  rw [TopForm.formMap_dForm] at hL
  change IsFreeGen L (dForm cL fun i => (x i : L)) at hL

  haveI : Algebra.EssFiniteType ℂ Q := hQ.essFiniteType
  haveI : Algebra.EssFiniteType Q L := .of_isLocalization L (nonZeroDivisors Q)
  haveI : Algebra.EssFiniteType ℂ L := .comp ℂ Q L
  have h1 : Module.finrank L (Forms cL D) = 1 := by
    have e : L ≃ₗ[L] Forms cL D := LinearEquiv.ofBijective (LinearMap.toSpanSingleton L _ _) hL
    rw [← e.finrank_eq, Module.finrank_self]
  rw [exteriorPower.finrank_eq] at h1
  have hr := eq_of_choose_eq_one_of_pos hD h1

  have hli : LinearIndependent L fun i => KaehlerDifferential.D ℂ L (x i : L) := by
    by_contra hc
    have h0 : dForm cL (fun i => (x i : L)) = 0 := by
      rw [dForm_eq]
      exact (exteriorPower.ιMulti L D).map_linearDependent _ hc
    rw [h0] at hL
    exact one_ne_zero (hL.1 (a₁ := 1) (a₂ := 0) (by simp))
  have hind : AlgebraicIndependent ℂ fun i => (x i : L) :=
    ReciprocityTheory.ChartRestriction.G.AR.differentialIndependence ℂ L D _ hli
  have htr : Algebra.trdeg ℂ L = D := by
    rw [← rank_kaehler_eq_trdeg, ← Module.finrank_eq_rank]
    exact_mod_cast hr.symm
  exact hind.isTranscendenceBasis_of_trdeg_le_of_finite (by rw [htr, Cardinal.mk_fin])

end GlobalTheory.FieldPair
