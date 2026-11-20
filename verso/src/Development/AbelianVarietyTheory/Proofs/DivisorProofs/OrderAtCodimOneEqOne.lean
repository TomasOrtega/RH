import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Cartier

/- English proof (translation)
Use `letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨z, hz⟩ : U)`. Use `haveI := hU.isLocalization_stalk ⟨z, hz⟩`. Use `set P := (hU.primeIdealOf ⟨z, hz⟩).asIdeal with hP`. Establish `halg : ∀ b : Γ(X, U), algebraMap Γ(X, U) (X.presheaf.stalk z) b = X.presheaf.germ U z hz b` using `fun b => rfl`. Establish `hmax : IsLocalRing.maximalIdeal (X.presheaf.stalk z) = Ideal.span {X.presheaf.germ U z hz a}`.

Rewrite using `[← IsLocalization.AtPrime.map_eq_maximalIdeal P (X.presheaf.stalk z)]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `g hgP`. Take `⟨r, hr⟩` from `hg g hgP`.

Rewrite using `[Ideal.mem_comap, Ideal.mem_span_singleton]`. Take `⟨u, hu⟩` from `(IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk z) P t).2 ht`. Use `⟨algebraMap Γ(X, U) (X.presheaf.stalk z) r * ↑u⁻¹, ?_⟩` and prove the remaining obligations. Establish `e` using `congrArg (algebraMap Γ(X, U) (X.presheaf.stalk z)) hr`. Rewrite `e` using `[map_mul, map_mul, ← hu]`.

Rewrite using `[← halg]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, ← halg]`. Conclude with `Ideal.mem_map_of_mem _ haP`. Establish `hne : X.presheaf.germ U z hz a ≠ 0` using `fun h0 => ha (fnOf_injective U (gen_mem hz) (by rw [← algebraMap_germ hz, h0, map_zero, map_zero]))`.

Rewrite using `[← algebraMap_germ hz a, ord_algebraMap h1 hne, ← hmax]`. Use `haveI := (isSimpleModule_iff_isCoatom.2 (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk z)).out : IsSimpleModule _ (X.presheaf.stalk z ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk z)))`. Simplify using `[Module.length_eq_one]`.
-/
theorem ord_fnOf_eq_one_of_generates (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens)
    (hU : IsAffineOpen U) (z : X) (hz : z ∈ U) (a t : Γ(X, U)) (h1 : Order.coheight z = 1)
    (ha : a ≠ 0) (haP : a ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal)
    (ht : t ∉ (hU.primeIdealOf ⟨z, hz⟩).asIdeal)
    (hg : ∀ g ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal, ∃ r, t * g = a * r) :
    Scheme.ord (fnOf U (gen_mem hz) a) z = 1 := by
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨z, hz⟩ : U)
  haveI := hU.isLocalization_stalk ⟨z, hz⟩
  set P := (hU.primeIdealOf ⟨z, hz⟩).asIdeal with hP
  have halg : ∀ b : Γ(X, U), algebraMap Γ(X, U) (X.presheaf.stalk z) b = X.presheaf.germ U z hz b :=
    fun b => rfl
  have hmax : IsLocalRing.maximalIdeal (X.presheaf.stalk z) =
      Ideal.span {X.presheaf.germ U z hz a} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P (X.presheaf.stalk z)]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro g hgP
      obtain ⟨r, hr⟩ := hg g hgP
      rw [Ideal.mem_comap, Ideal.mem_span_singleton]
      obtain ⟨u, hu⟩ := (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk z) P t).2 ht
      refine ⟨algebraMap Γ(X, U) (X.presheaf.stalk z) r * ↑u⁻¹, ?_⟩
      have e := congrArg (algebraMap Γ(X, U) (X.presheaf.stalk z)) hr
      rw [map_mul, map_mul, ← hu] at e
      rw [← halg]
      calc algebraMap Γ(X, U) (X.presheaf.stalk z) g
          = ↑u⁻¹ * (↑u * algebraMap Γ(X, U) (X.presheaf.stalk z) g) := by simp
        _ = _ := by rw [e]; ring
    · rw [Ideal.span_le, Set.singleton_subset_iff, ← halg]
      exact Ideal.mem_map_of_mem _ haP
  have hne : X.presheaf.germ U z hz a ≠ 0 := fun h0 =>
    ha (fnOf_injective U (gen_mem hz) (by rw [← algebraMap_germ hz, h0, map_zero, map_zero]))
  rw [← algebraMap_germ hz a, ord_algebraMap h1 hne, ← hmax]
  haveI := (isSimpleModule_iff_isCoatom.2
    (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk z)).out :
      IsSimpleModule _ (X.presheaf.stalk z ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk z)))
  simp [Module.length_eq_one]

end GlobalTheory.Cartier
