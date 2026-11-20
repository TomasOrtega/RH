import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

namespace MultiHomogMemCoordinate

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

/- English proof (translation)
Use extensionality with `k`. Rewrite using `[Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma, Finset.sum_eq_single k]`. Simplify using `[hm]`. Introduce `b _ hb`. Simplify using `[hb]`.

Simplify using the standard rewrite rules.
-/
theorem mapDomain_fst_eq (m : (Σ k, ι k) →₀ ℕ) (a : K → ℕ) (hm : ∀ k, ∑ i, m ⟨k, i⟩ = a k) :
    Finsupp.mapDomain Sigma.fst m = Finsupp.equivFunOnFinite.symm a := by
  ext k
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum_fintype _ _ (by simp),
    Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp [hm]
  · intro b _ hb
    simp [hb]
  · simp

/- English proof (translation)
Establish `hX : (monomial (Finsupp.mapDomain Sigma.fst m) (1 : Ω) : MvPolynomial K Ω) = m.prod fun p e => (X p.1 : MvPolynomial K Ω) ^ e`. Rewrite using `[← rename_monomial, monomial_eq, C_1, one_mul, map_finsuppProd]`. Simplify using `only [map_pow, rename_X]`. Rewrite using `[← mapDomain_fst_eq m a hm, hX]`. Simplify using `only [mConeMap, aeval_monomial, mul_pow, Finsupp.prod_mul, MvPolynomial.algebraMap_apply, map_finsuppProd, map_pow, map_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem cone_monomial (y : (Σ k, ι k) → Ω) (m : (Σ k, ι k) →₀ ℕ) (c : ℤ) (a : K → ℕ)
    (hm : ∀ k, ∑ i, m ⟨k, i⟩ = a k) :
    mConeMap y (monomial m c) =
      C (aeval y (monomial m c)) * monomial (Finsupp.equivFunOnFinite.symm a) 1 := by
  have hX : (monomial (Finsupp.mapDomain Sigma.fst m) (1 : Ω) : MvPolynomial K Ω) =
      m.prod fun p e => (X p.1 : MvPolynomial K Ω) ^ e := by
    rw [← rename_monomial, monomial_eq, C_1, one_mul, map_finsuppProd]
    simp only [map_pow, rename_X]
  rw [← mapDomain_fst_eq m a hm, hX]
  simp only [mConeMap, aeval_monomial, mul_pow, Finsupp.prod_mul, MvPolynomial.algebraMap_apply, map_finsuppProd,
    map_pow, map_mul]
  ring

/- English proof (translation)
Use `conv_lhs => rw [g.as_sum]`. Use `conv_rhs => rw [g.as_sum]`. Rewrite using `[map_sum, map_sum, map_sum, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun m hm => cone_monomial y m _ a (hg m hm)`.
-/
theorem cone_eq (y : (Σ k, ι k) → Ω) (g : MRing ι) (a : K → ℕ) (hg : IsMultiHomog g a) :
    mConeMap y g = C (aeval y g) * monomial (Finsupp.equivFunOnFinite.symm a) 1 := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun m hm => cone_monomial y m _ a (hg m hm)

end MultiHomogMemCoordinate

open MultiHomogMemCoordinate in

/- English proof (translation)
Introduce `K _ ι _ Ω _ y g a hg`. Rewrite using `[mCoordIdeal, RingHom.mem_ker, cone_eq y g a hg, C_mul_monomial, mul_one, monomial_eq_zero]`.
-/
theorem MultiHomogMemCoord.proof : MultiHomogMemCoord.Statement := by
  intro K _ ι _ Ω _ y g a hg
  rw [mCoordIdeal, RingHom.mem_ker, cone_eq y g a hg, C_mul_monomial, mul_one,
    monomial_eq_zero]

end GroundTheory.Heights₂.Heights
