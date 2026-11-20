import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Formalism.LocalToGlobal.ProjectiveLattices.DepthPins
import Formalism.LocalToGlobal.ProjectiveLattices.CrudeVal

set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

/- English proof (translation)
Establish `hp` using `Formalism.L2.Pj.Crude.resCharOf_prime la`. Establish `hpP` using `Formalism.L2.Pj.Crude.crv_char_mem la`. Unfold `ramOverZ`. Generalize the expression as in `resCharOf la = p at hp hpP hζ ⊢`. Establish `hP` using `la.isPrime`.

Establish `: Fact p.Prime` using `⟨hp⟩`. Use `set Z : 𝓞 L := ⟨ζ, hζ.isIntegral hp.pos⟩ with hZdef`. Establish `hZ : IsPrimitiveRoot Z p` using `IsPrimitiveRoot.of_map_of_injective (f := algebraMap (𝓞 L) L) hζ RingOfIntegers.coe_injective`. Establish `hassoc : Associated ((Z - 1) ^ (p - 1)) (p : 𝓞 L)`. Establish `h2 : (Polynomial.cyclotomic p (𝓞 L)).eval 1 = p` using `Polynomial.eval_one_cyclotomic_prime`.

Rewrite using `[← h2, Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hZ, Polynomial.eval_prod]`. Simplify using `only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]`. Rewrite using `[← Nat.totient_prime hp, ← hZ.card_primitiveRoots, ← Finset.prod_const]`. Use `Associated.prod _ _ _ fun η hη => ?_` and prove the remaining obligations. Establish `: NeZero p` using `⟨hp.ne_zero⟩`.

Take `⟨i, -, hi, rfl⟩` from `hZ.isPrimitiveRoot_iff.mp (isPrimitiveRoot_of_mem_primitiveRoots hη)`. Simplify using `using (hZ.associated_sub_one_pow_sub_one_of_coprime hi).neg_right`. Establish `hZP : Z - 1 ∈ la.asIdeal`. Take `⟨u, hu⟩` from `hassoc.symm`. Conclude with `hP.mem_of_pow_mem _ (hu ▸ la.asIdeal.mul_mem_right _ hpP)`.

Establish `hmap : Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {((p : ℕ) : ℤ)}) = Ideal.span {((p : ℕ) : 𝓞 L)}`. Rewrite using `[Ideal.map_span, Set.image_singleton, map_natCast]`. Establish `hle : Ideal.span {(p : 𝓞 L)} ≤ la.asIdeal ^ (p - 1)`. Rewrite using `[← Ideal.span_singleton_eq_span_singleton.mpr hassoc, ← Ideal.span_singleton_pow]`. Conclude with `pow_le_pow_left' ((Ideal.span_singleton_le_iff_mem la.asIdeal).mpr hZP) _`.

Establish `hne : Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {((p : ℕ) : ℤ)}) ≠ ⊥`. Rewrite using `[hmap, Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hp.ne_zero` after adjusting the coercions. Rewrite using `[Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity hne hP]`. Apply `FiniteMultiplicity.le_multiplicity_of_pow_dvd` to reduce the goal to its premises.

Conclude with `FiniteMultiplicity.of_not_isUnit (Ideal.isUnit_iff.not.mpr hP.ne_top) hne`. Rewrite using `[Ideal.dvd_iff_le, hmap]`. Conclude with `hle`.
-/
theorem resChar_sub_one_le_ramOverZ_of_primitiveRoot {L : Type} [Field L] [NumberField L]
    (la : HeightOneSpectrum (𝓞 L)) (ζ : L) (hζ : IsPrimitiveRoot ζ (resCharOf la)) :
    resCharOf la - 1 ≤ ramOverZ la := by
  have hp := Formalism.L2.Pj.Crude.resCharOf_prime la
  have hpP := Formalism.L2.Pj.Crude.crv_char_mem la
  unfold ramOverZ
  generalize resCharOf la = p at hp hpP hζ ⊢
  have hP := la.isPrime
  have : Fact p.Prime := ⟨hp⟩
  set Z : 𝓞 L := ⟨ζ, hζ.isIntegral hp.pos⟩ with hZdef
  have hZ : IsPrimitiveRoot Z p :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap (𝓞 L) L) hζ RingOfIntegers.coe_injective
  have hassoc : Associated ((Z - 1) ^ (p - 1)) (p : 𝓞 L) := by
    have h2 : (Polynomial.cyclotomic p (𝓞 L)).eval 1 = p := Polynomial.eval_one_cyclotomic_prime
    rw [← h2, Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hZ, Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [← Nat.totient_prime hp, ← hZ.card_primitiveRoots, ← Finset.prod_const]
    refine Associated.prod _ _ _ fun η hη => ?_
    have : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨i, -, hi, rfl⟩ := hZ.isPrimitiveRoot_iff.mp (isPrimitiveRoot_of_mem_primitiveRoots hη)
    simpa using (hZ.associated_sub_one_pow_sub_one_of_coprime hi).neg_right
  have hZP : Z - 1 ∈ la.asIdeal := by
    obtain ⟨u, hu⟩ := hassoc.symm
    exact hP.mem_of_pow_mem _ (hu ▸ la.asIdeal.mul_mem_right _ hpP)
  have hmap : Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {((p : ℕ) : ℤ)}) = Ideal.span {((p : ℕ) : 𝓞 L)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hle : Ideal.span {(p : 𝓞 L)} ≤ la.asIdeal ^ (p - 1) := by
    rw [← Ideal.span_singleton_eq_span_singleton.mpr hassoc, ← Ideal.span_singleton_pow]
    exact pow_le_pow_left' ((Ideal.span_singleton_le_iff_mem la.asIdeal).mpr hZP) _
  have hne : Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {((p : ℕ) : ℤ)}) ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  rw [Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity hne hP]
  apply FiniteMultiplicity.le_multiplicity_of_pow_dvd
  · exact FiniteMultiplicity.of_not_isUnit (Ideal.isUnit_iff.not.mpr hP.ne_top) hne
  · rw [Ideal.dvd_iff_le, hmap]
    exact hle

/- English proof (translation)
Introduce `E _ _ _ H l c la hd`. Establish `hp` using `Formalism.L2.Pj.Crude.resCharOf_prime la`. Establish `hM : l.M ≠ 0` using `by have := l.three_le; omega`. Establish `h0 : l.M' ≠ 0` using `Nat.lcm_ne_zero hM l.A_pos.ne'`. Establish `hmem` using `Formalism.L2.Pj.zeta_mem_of_dvd c (hd.trans (Nat.dvd_lcm_left l.M l.A)) h0`.

Use `resChar_sub_one_le_ramOverZ_of_primitiveRoot la ⟨_, hmem⟩ ?_` and prove the remaining obligations. Conclude with `IsPrimitiveRoot.of_map_of_injective (f := c.F.val.toRingHom) (Complex.isPrimitiveRoot_exp _ hp.ne_zero) Subtype.val_injective`.
-/
theorem resChar_sub_one_le_ramOverZ_of_dvd_level :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l)
      (la : HeightOneSpectrum (𝓞 c.F)), resCharOf la ∣ l.M → resCharOf la - 1 ≤ ramOverZ la := by
  intro E _ _ _ H l c la hd
  have hp := Formalism.L2.Pj.Crude.resCharOf_prime la
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have h0 : l.M' ≠ 0 := Nat.lcm_ne_zero hM l.A_pos.ne'
  have hmem := Formalism.L2.Pj.zeta_mem_of_dvd c (hd.trans (Nat.dvd_lcm_left l.M l.A)) h0
  refine resChar_sub_one_le_ramOverZ_of_primitiveRoot la ⟨_, hmem⟩ ?_
  exact IsPrimitiveRoot.of_map_of_injective (f := c.F.val.toRingHom)
    (Complex.isPrimitiveRoot_exp _ hp.ne_zero) Subtype.val_injective

end GlobalTheory.RunDepth
