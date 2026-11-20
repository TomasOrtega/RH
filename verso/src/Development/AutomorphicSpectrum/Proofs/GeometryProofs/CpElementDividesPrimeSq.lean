import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.HT.KappaDvd

/- English proof (translation)
Introduce `A Ω _ _ _ _ _ _ _ p hp κ h`. Establish `hinj : Function.Injective (algebraMap A Ω)` using `IsFractionRing.injective A Ω`. Unfold `IsCp at h`. Use `split_ifs at h with h2`. Substitute `h2` using the available equality.

Establish `: κ = 4` using `hinj (by rw [h]; exact (map_ofNat _ 4).symm)`. Substitute `this` using the available equality. Conclude with `⟨1, by norm_num⟩`. Take `⟨ζ, hζ, hκ⟩` from `h`. Establish `hp1 : 1 < p` using `hp.out.one_lt`.

Establish `hint : IsIntegral A ζ`. Use `⟨Polynomial.X ^ p - 1, Polynomial.monic_X_pow_sub_C 1 hp.out.ne_zero, ?_⟩` and prove the remaining obligations. Simplify using `[hζ.pow_eq_one]`. Take `⟨z, hz⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hint`. Establish `hz' : IsPrimitiveRoot z p`.

Rewrite `hζ` using `[← hz]`. Conclude with `hζ.of_map_of_injective hinj`. Establish `hκz : κ = z - 1` using `hinj (by rw [hκ, map_sub, map_one, hz])`. Establish `hsum : ∑ i ∈ Finset.range p, z ^ i = 0` using `hz'.geom_sum_eq_zero hp1`. Establish `hp_eq : (p : A) = ∑ i ∈ Finset.range p, (1 - z ^ i)`.

Rewrite using `[Finset.sum_sub_distrib, hsum]`. Simplify using the standard rewrite rules. Establish `hdvd : κ ∣ (p : A)`. Rewrite using `[hp_eq, hκz]`. Use `Finset.dvd_sum fun i _ => ?_` and prove the remaining obligations.

Use `sub_dvd_pow_sub_pow z 1 i` as an intermediate fact. Rewrite `this` using `[one_pow]`. Rewrite using `[show (1 : A) - z ^ i = -(z ^ i - 1) by ring]`. Conclude with `dvd_neg.mpr this`. Conclude with `hdvd.trans (dvd_pow_self _ two_ne_zero)`.
-/
theorem kappa_dvd_sq : ∀ (A Ω : Type) [CommRing A] [IsDomain A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω]
    [IsIntegrallyClosed A] [CharZero Ω] (p : ℕ) [Fact p.Prime] (κ : A),
    IsCp p (algebraMap A Ω κ) → κ ∣ (p : A) ^ 2 := by
  intro A Ω _ _ _ _ _ _ _ p hp κ h
  have hinj : Function.Injective (algebraMap A Ω) := IsFractionRing.injective A Ω
  unfold IsCp at h
  split_ifs at h with h2
  · subst h2
    have : κ = 4 := hinj (by rw [h]; exact (map_ofNat _ 4).symm)
    subst this
    exact ⟨1, by norm_num⟩
  · obtain ⟨ζ, hζ, hκ⟩ := h
    have hp1 : 1 < p := hp.out.one_lt
    have hint : IsIntegral A ζ := by
      refine ⟨Polynomial.X ^ p - 1, Polynomial.monic_X_pow_sub_C 1 hp.out.ne_zero, ?_⟩
      simp [hζ.pow_eq_one]
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    have hz' : IsPrimitiveRoot z p := by
      rw [← hz] at hζ
      exact hζ.of_map_of_injective hinj
    have hκz : κ = z - 1 := hinj (by rw [hκ, map_sub, map_one, hz])
    have hsum : ∑ i ∈ Finset.range p, z ^ i = 0 := hz'.geom_sum_eq_zero hp1
    have hp_eq : (p : A) = ∑ i ∈ Finset.range p, (1 - z ^ i) := by
      rw [Finset.sum_sub_distrib, hsum]; simp
    have hdvd : κ ∣ (p : A) := by
      rw [hp_eq, hκz]
      refine Finset.dvd_sum fun i _ => ?_
      have := sub_dvd_pow_sub_pow z 1 i
      rw [one_pow] at this
      rw [show (1 : A) - z ^ i = -(z ^ i - 1) by ring]
      exact dvd_neg.mpr this
    exact hdvd.trans (dvd_pow_self _ two_ne_zero)

end GlobalTheory.CompanionTheory.Ar.HT.KappaDvd
