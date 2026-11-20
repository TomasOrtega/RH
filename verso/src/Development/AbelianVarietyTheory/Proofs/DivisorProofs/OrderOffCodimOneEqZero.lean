import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

/- English proof (translation)
Introduce `X _ _ U hU z hz a t hcz hdiv v hv ht hne`. Distinguish the cases in `ha : v ∈ X.basicOpen a`. Conclude with `UnitAt.ord_eq_zero ((unitAt_fnOf_iff hv _ a).2 ha)`. Use `Scheme.ord_eq_zero_of_coheight_neq_one (fun hcv => ?_) _` and prove the remaining obligations. Establish `key : ∀ (w : X) (hw : w ∈ U) (f : Γ(X, U)), w ∈ X.basicOpen f ↔ f ∉ (hU.primeIdealOf ⟨w, hw⟩).asIdeal`.

Introduce `w hw f`. Use `letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨w, hw⟩ : U)`. Use `haveI := hU.isLocalization_stalk ⟨w, hw⟩`. Rewrite using `[X.mem_basicOpen f w hw]`. Conclude with `IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk w) _ f`.

Establish `hle : (hU.primeIdealOf ⟨z, hz⟩).asIdeal ≤ (hU.primeIdealOf ⟨v, hv⟩).asIdeal`. Introduce `g hg`. Take `⟨r, hr⟩` from `hdiv g hg`. Establish `haP : a ∈ (hU.primeIdealOf ⟨v, hv⟩).asIdeal`. Assume the negation of the conclusion as `h`.

Conclude with `ha ((key v hv a).2 h)`. Establish `htP : t ∉ (hU.primeIdealOf ⟨v, hv⟩).asIdeal` using `(key v hv t).1 ht`. Establish `htg : t * g ∈ (hU.primeIdealOf ⟨v, hv⟩).asIdeal` using `hr ▸ Ideal.mul_mem_right _ _ haP`. Conclude with `((hU.primeIdealOf ⟨v, hv⟩).isPrime.mem_or_mem htg).resolve_left htP`. Establish `hsp : z ⤳ v`.

Establish `h1` using `((PrimeSpectrum.le_iff_specializes _ _).mp hle).map hU.fromSpec.continuous`. Rewrite `h1` using `[hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf]`. Then use the resulting hypothesis. Establish `hvz : v ≤ z` using `hsp`. Establish `hlt : v < z` using `lt_of_le_not_ge hvz (fun h => hne (hsp.antisymm h).eq.symm)`. Establish `h2` using `Order.coheight_add_one_le hlt`.

Rewrite `h2` using `[hcz, hcv]`. Conclude with `absurd h2 (by norm_num)`.
-/
theorem GlobalTheory.Cartier.ord_fnOf_eq_zero_off_center : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens) (hU : IsAffineOpen U) (z : X) (hz : z ∈ U) (a t : Γ(X, U)), Order.coheight z = 1 → (∀ g ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal, ∃ r, t * g = a * r) → ∀ (v : X) (hv : v ∈ U), v ∈ X.basicOpen t → v ≠ z → Scheme.ord (fnOf U (gen_mem hv) a) v = 0 := by
  intro X _ _ U hU z hz a t hcz hdiv v hv ht hne
  by_cases ha : v ∈ X.basicOpen a
  · exact UnitAt.ord_eq_zero ((unitAt_fnOf_iff hv _ a).2 ha)
  refine Scheme.ord_eq_zero_of_coheight_neq_one (fun hcv => ?_) _
  have key : ∀ (w : X) (hw : w ∈ U) (f : Γ(X, U)),
      w ∈ X.basicOpen f ↔ f ∉ (hU.primeIdealOf ⟨w, hw⟩).asIdeal := by
    intro w hw f
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨w, hw⟩ : U)
    haveI := hU.isLocalization_stalk ⟨w, hw⟩
    rw [X.mem_basicOpen f w hw]
    exact IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk w) _ f
  have hle : (hU.primeIdealOf ⟨z, hz⟩).asIdeal ≤ (hU.primeIdealOf ⟨v, hv⟩).asIdeal := by
    intro g hg
    obtain ⟨r, hr⟩ := hdiv g hg
    have haP : a ∈ (hU.primeIdealOf ⟨v, hv⟩).asIdeal := by
      by_contra h
      exact ha ((key v hv a).2 h)
    have htP : t ∉ (hU.primeIdealOf ⟨v, hv⟩).asIdeal := (key v hv t).1 ht
    have htg : t * g ∈ (hU.primeIdealOf ⟨v, hv⟩).asIdeal := hr ▸ Ideal.mul_mem_right _ _ haP
    exact ((hU.primeIdealOf ⟨v, hv⟩).isPrime.mem_or_mem htg).resolve_left htP
  have hsp : z ⤳ v := by
    have h1 := ((PrimeSpectrum.le_iff_specializes _ _).mp hle).map hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at h1
  have hvz : v ≤ z := hsp
  have hlt : v < z := lt_of_le_not_ge hvz (fun h => hne (hsp.antisymm h).eq.symm)
  have h2 := Order.coheight_add_one_le hlt
  rw [hcz, hcv] at h2
  exact absurd h2 (by norm_num)
