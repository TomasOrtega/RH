import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTangent
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo

/- English proof (translation)
Rewrite using `[← e.mem_O]`. Establish `h : IsIntegral e.O x` using `hx.tower_top`. Take `⟨y, hy⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := e.O) (K := AlgebraicClosure F)).1 h`. Rewrite using `[← hy]`. Conclude with `y.2`.
-/
theorem Ext.w_le_one_of_isIntegral {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} (e : Ext v)
    {x : AlgebraicClosure F} (hx : IsIntegral ℤ x) : e.w x ≤ 1 := by
  rw [← e.mem_O]
  have h : IsIntegral e.O x := hx.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := e.O) (K := AlgebraicClosure F)).1 h
  rw [← hy]
  exact y.2

/- English proof (translation)
Establish `hQ : IsAlgebraic ℚ a` using `(Algebra.IsAlgebraic.trans ℚ F (AlgebraicClosure F)).isAlgebraic a`. Establish `hZ : IsAlgebraic ℤ a` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ _).2 hQ`. Take `⟨d, hd, hi⟩` from `hZ.exists_integral_multiple`. Establish `hd' : (Ideal.span {(d : 𝓞 F)}) ≠ 0`. Simplify using `using hd`.

Use `(Ideal.finite_factors hd').subset ?_` and prove the remaining obligations. Introduce and unpack `v ⟨e, he⟩`. Simplify using `only [Set.mem_setOf_eq, Ideal.dvd_span_singleton]`. Assume the negation of the conclusion as `hv`. Establish `h1 : NumberField.HeightOneSpectrum.adicAbv F v ((d : 𝓞 F) : F) = 1` using `(v.adicAbv_coe_eq_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) _).2 hv`.

Establish `h2` using `e.w_le_one_of_isIntegral hi`. Establish `h3 : e.w (d : AlgebraicClosure F) = 1`. Rewrite using `[← h1, ← e.w_alg]`. Simplify using the standard rewrite rules. Rewrite `h2` using `[zsmul_eq_mul, map_mul, h3, one_mul]`.

Conclude with `absurd he (not_lt.2 h2)`.
-/
theorem finite_ext_one_lt (F : Type) [Field F] [NumberField F] (a : AlgebraicClosure F) :
    {v : HeightOneSpectrum (𝓞 F) | ∃ e : Ext v, 1 < e.w a}.Finite := by
  have hQ : IsAlgebraic ℚ a :=
    (Algebra.IsAlgebraic.trans ℚ F (AlgebraicClosure F)).isAlgebraic a
  have hZ : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ _).2 hQ
  obtain ⟨d, hd, hi⟩ := hZ.exists_integral_multiple
  have hd' : (Ideal.span {(d : 𝓞 F)}) ≠ 0 := by
    simpa using hd
  refine (Ideal.finite_factors hd').subset ?_
  rintro v ⟨e, he⟩
  simp only [Set.mem_setOf_eq, Ideal.dvd_span_singleton]
  by_contra hv
  have h1 : NumberField.HeightOneSpectrum.adicAbv F v ((d : 𝓞 F) : F) = 1 :=
    (v.adicAbv_coe_eq_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) _).2 hv
  have h2 := e.w_le_one_of_isIntegral hi
  have h3 : e.w (d : AlgebraicClosure F) = 1 := by
    rw [← h1, ← e.w_alg]
    simp
  rw [zsmul_eq_mul, map_mul, h3, one_mul] at h2
  exact absurd he (not_lt.2 h2)

/- English proof (translation)
Use `((finite_ext_one_lt F a).union (finite_ext_one_lt F a⁻¹)).subset ?_` and prove the remaining obligations. Introduce and unpack `v ⟨e, he⟩`. Break down `lt_or_gt_of_ne he with h | h` into its components or cases. Use `Or.inr ⟨e, ?_⟩` and prove the remaining obligations. Rewrite using `[map_inv₀]`.

Conclude with `(one_lt_inv₀ (e.w.pos ha)).2 h`. Conclude with `Or.inl ⟨e, h⟩`.
-/
theorem finite_ext_ne_one (F : Type) [Field F] [NumberField F] (a : AlgebraicClosure F) (ha : a ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | ∃ e : Ext v, e.w a ≠ 1}.Finite := by
  refine ((finite_ext_one_lt F a).union (finite_ext_one_lt F a⁻¹)).subset ?_
  rintro v ⟨e, he⟩
  rcases lt_or_gt_of_ne he with h | h
  · refine Or.inr ⟨e, ?_⟩
    rw [map_inv₀]
    exact (one_lt_inv₀ (e.w.pos ha)).2 h
  · exact Or.inl ⟨e, h⟩

end GlobalTheory.TrueGeo
