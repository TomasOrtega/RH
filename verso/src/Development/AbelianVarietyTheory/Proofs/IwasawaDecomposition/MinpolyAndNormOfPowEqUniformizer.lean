import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.TameEis

open Polynomial

/- English proof (translation)
Establish `h : normV v = Ideal.absNorm v.asIdeal`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Both sides reduce to the same expression. Establish `h1 : Ideal.absNorm v.asIdeal ≠ 1` using `fun h' => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h')`. Establish `h0 : Ideal.absNorm v.asIdeal ≠ 0` using `fun h' => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h')`.

Use linear arithmetic over natural numbers and integers.
-/
theorem two_le_normV (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) :
    2 ≤ normV v := by
  have h : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h' => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h')
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h' => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h')
  omega

/- English proof (translation)
Introduce `E Ω _ _ _ _ v ϖ hmem hnot π hπ`. Establish `hq` using `two_le_normV E v`. Use `set n := normV v - 1 with hn`. Establish `hn1 : 0 < n` using `by omega`. Establish `hmon : (X ^ n - C ϖ : (𝓞 E)[X]).Monic` using `monic_X_pow_sub_C ϖ hn1.ne'`.

Establish `hdeg : (X ^ n - C ϖ : (𝓞 E)[X]).natDegree = n` using `natDegree_X_pow_sub_C`. Establish `hEis : (X ^ n - C ϖ : (𝓞 E)[X]).IsEisensteinAt v.asIdeal`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hmon.leadingCoeff]`. Conclude with `fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)`.

Introduce `m hm`. Rewrite `hm` using `[hdeg]`. Rewrite using `[coeff_sub, coeff_X_pow, coeff_C, if_neg hm.ne]`. Distinguish the cases in `h0 : m = 0`. Substitute `h0` using the available equality.

Simplify using `using v.asIdeal.neg_mem_iff.2 hmem`. Simplify using `[h0]`. Rewrite using `[coeff_sub, coeff_X_pow, coeff_C, if_neg hn1.ne, if_pos rfl, zero_sub]`. Rewrite using `[Ideal.neg_mem_iff]` and apply the resulting hypothesis. Establish `hirr : Irreducible (X ^ n - C ϖ : (𝓞 E)[X])` using `hEis.irreducible v.isPrime hmon.isPrimitive (by rw [hdeg]; exact hn1)`.

Establish `hmap : (X ^ n - C ϖ : (𝓞 E)[X]).map (algebraMap (𝓞 E) E) = X ^ n - C (ϖ : E)`. Simplify using `[Polynomial.map_sub]`. Establish `hirrE : Irreducible (X ^ n - C (ϖ : E))`. Rewrite using `[← hmap]`. Conclude with `(hmon.irreducible_iff_irreducible_map_fraction_map (K := E)).1 hirr`.

Establish `hmonE : (X ^ n - C (ϖ : E)).Monic` using `monic_X_pow_sub_C _ hn1.ne'`. Establish `hroot : aeval π (X ^ n - C (ϖ : E)) = 0`. Simplify using `[hπ]`. Establish `hmin : minpoly E π = X ^ n - C (ϖ : E)` using `(minpoly.eq_of_irreducible_of_monic hirrE hroot hmonE).symm`. Use `⟨hmin, ?_⟩` and prove the remaining obligations.

Establish `hx : IsIntegral E π` using `⟨_, hmonE, hroot⟩`. Rewrite using `[← IntermediateField.adjoin.powerBasis_gen hx, Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, IntermediateField.adjoin.powerBasis_gen hx, IntermediateField.minpoly_gen, IntermediateField.adjoin.powerBasis_dim, hmin, natDegree_X_pow_sub_C]`. Rewrite using `[coeff_sub, coeff_X_pow, coeff_C, if_neg hn1.ne, if_pos rfl, zero_sub]`. Establish `: normV v = n + 1` using `by omega`. Rewrite using `[this, pow_succ]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem minpoly_and_norm_of_pow_eq_uniformizer : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E)) (ϖ : 𝓞 E),
    ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ∀ π : Ω, π ^ (normV v - 1) = algebraMap E Ω (ϖ : E) →
      minpoly E π = Polynomial.X ^ (normV v - 1) - Polynomial.C (ϖ : E) ∧
      Algebra.norm E (IntermediateField.AdjoinSimple.gen E π) = (-1) ^ normV v * (ϖ : E) := by
  intro E Ω _ _ _ _ v ϖ hmem hnot π hπ
  have hq := two_le_normV E v
  set n := normV v - 1 with hn
  have hn1 : 0 < n := by omega
  have hmon : (X ^ n - C ϖ : (𝓞 E)[X]).Monic := monic_X_pow_sub_C ϖ hn1.ne'
  have hdeg : (X ^ n - C ϖ : (𝓞 E)[X]).natDegree = n := natDegree_X_pow_sub_C
  have hEis : (X ^ n - C ϖ : (𝓞 E)[X]).IsEisensteinAt v.asIdeal := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hmon.leadingCoeff]; exact fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
    · intro m hm
      rw [hdeg] at hm
      rw [coeff_sub, coeff_X_pow, coeff_C, if_neg hm.ne]
      by_cases h0 : m = 0
      · subst h0; simpa using v.asIdeal.neg_mem_iff.2 hmem
      · simp [h0]
    · rw [coeff_sub, coeff_X_pow, coeff_C, if_neg hn1.ne, if_pos rfl, zero_sub]
      rwa [Ideal.neg_mem_iff]
  have hirr : Irreducible (X ^ n - C ϖ : (𝓞 E)[X]) :=
    hEis.irreducible v.isPrime hmon.isPrimitive (by rw [hdeg]; exact hn1)
  have hmap : (X ^ n - C ϖ : (𝓞 E)[X]).map (algebraMap (𝓞 E) E) = X ^ n - C (ϖ : E) := by
    simp [Polynomial.map_sub]
  have hirrE : Irreducible (X ^ n - C (ϖ : E)) := by
    rw [← hmap]; exact (hmon.irreducible_iff_irreducible_map_fraction_map (K := E)).1 hirr
  have hmonE : (X ^ n - C (ϖ : E)).Monic := monic_X_pow_sub_C _ hn1.ne'
  have hroot : aeval π (X ^ n - C (ϖ : E)) = 0 := by
    simp [hπ]
  have hmin : minpoly E π = X ^ n - C (ϖ : E) :=
    (minpoly.eq_of_irreducible_of_monic hirrE hroot hmonE).symm
  refine ⟨hmin, ?_⟩
  have hx : IsIntegral E π := ⟨_, hmonE, hroot⟩
  rw [← IntermediateField.adjoin.powerBasis_gen hx,
    Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, IntermediateField.adjoin.powerBasis_gen hx,
    IntermediateField.minpoly_gen, IntermediateField.adjoin.powerBasis_dim, hmin, natDegree_X_pow_sub_C]
  rw [coeff_sub, coeff_X_pow, coeff_C, if_neg hn1.ne, if_pos rfl, zero_sub]
  have : normV v = n + 1 := by omega
  rw [this, pow_succ]; ring

end GlobalTheory.TameEis
