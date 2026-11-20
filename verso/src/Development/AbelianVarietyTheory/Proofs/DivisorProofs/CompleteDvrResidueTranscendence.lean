import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring

open IsLocalRing Formalism.L2.Pj

namespace GlobalTheory.GaussCountable

/- English proof (translation)
Use `set O := Localization.AtPrime p`. Establish `hinj : Function.Injective (algebraMap R O)` using `IsLocalization.injective O (Ideal.primeCompl_le_nonZeroDivisors p)`. Establish `h1 : Ideal.map (algebraMap R O) p = Ideal.span {algebraMap R O g}`. Rewrite using `[congrArg (Ideal.map (algebraMap R O)) hg, Ideal.map_span, Set.image_singleton]`. Establish `hspan : Ideal.span {algebraMap R O g} = IsLocalRing.maximalIdeal O` using `h1.symm.trans (IsLocalization.AtPrime.map_eq_maximalIdeal p O)`.

Establish `hϖ0 : algebraMap R O g ≠ 0` using `by rw [Ne, map_eq_zero_iff _ hinj]; exact hgp.ne_zero`. Establish `hϖ : Prime (algebraMap R O g)` using `(Ideal.span_singleton_prime hϖ0).mp (by rw [hspan]; infer_instance)`. Use `IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨_, hϖ.irreducible, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Take `⟨⟨a, s⟩, hxs⟩` from `IsLocalization.mk'_surjective p.primeCompl x`.

Simplify using `only at hxs`. Substitute `hxs` using the available equality. Establish `ha : a ≠ 0` using `by rintro rfl; exact hx (by simp)`. Take `⟨n, a', hnd, rfl⟩` from `WfDvdMonoid.max_power_factor ha hgp.irreducible`. Establish `ha' : a' ∈ p.primeCompl` using `by show a' ∉ p`.

Rewrite using `[hg, Ideal.mem_span_singleton]`. Conclude with `hnd`. Use `⟨n, ((IsLocalization.AtPrime.isUnit_mk'_iff O p a' s).mpr ha').unit, ?_⟩` and prove the remaining obligations. Rewrite using `[IsUnit.unit_spec, ← map_pow, IsLocalization.mul_mk'_eq_mk'_of_mul]`.
-/
theorem isDiscreteValuationRing_localization {R : Type} [CommRing R] [IsDomain R]
    [WfDvdMonoid R] (p : Ideal R) [p.IsPrime] (g : R) (hgp : Prime g)
    (hg : p = Ideal.span {g}) : IsDiscreteValuationRing (Localization.AtPrime p) := by
  set O := Localization.AtPrime p
  have hinj : Function.Injective (algebraMap R O) :=
    IsLocalization.injective O (Ideal.primeCompl_le_nonZeroDivisors p)
  have h1 : Ideal.map (algebraMap R O) p = Ideal.span {algebraMap R O g} := by
    rw [congrArg (Ideal.map (algebraMap R O)) hg, Ideal.map_span, Set.image_singleton]
  have hspan : Ideal.span {algebraMap R O g} = IsLocalRing.maximalIdeal O :=
    h1.symm.trans (IsLocalization.AtPrime.map_eq_maximalIdeal p O)
  have hϖ0 : algebraMap R O g ≠ 0 := by rw [Ne, map_eq_zero_iff _ hinj]; exact hgp.ne_zero
  have hϖ : Prime (algebraMap R O g) :=
    (Ideal.span_singleton_prime hϖ0).mp (by rw [hspan]; infer_instance)
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨_, hϖ.irreducible, ?_⟩
  intro x hx
  obtain ⟨⟨a, s⟩, hxs⟩ := IsLocalization.mk'_surjective p.primeCompl x
  simp only at hxs
  subst hxs
  have ha : a ≠ 0 := by rintro rfl; exact hx (by simp)
  obtain ⟨n, a', hnd, rfl⟩ := WfDvdMonoid.max_power_factor ha hgp.irreducible
  have ha' : a' ∈ p.primeCompl := by
    show a' ∉ p
    rw [hg, Ideal.mem_span_singleton]; exact hnd
  refine ⟨n, ((IsLocalization.AtPrime.isUnit_mk'_iff O p a' s).mpr ha').unit, ?_⟩
  rw [IsUnit.unit_spec, ← map_pow, IsLocalization.mul_mk'_eq_mk'_of_mul]

/- English proof (translation)
Introduce `T`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible T.V`. Set `A` to `MvPolynomial ℕ T.V`. Establish `hp : Prime (MvPolynomial.C ϖ : A)` using `(MvPolynomial.prime_C_iff _).2 hϖ.prime`. Set `P : Ideal A` to `Ideal.span {MvPolynomial.C ϖ}`.

Use `haveI : P.IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp`. Use `haveI : IsDiscreteValuationRing (Localization.AtPrime P) := isDiscreteValuationRing_localization P _ hp rfl`. Take `⟨O, _, _, _, _, ψ, hψ, _⟩` from `GlobalTheory.exists_complete_discreteValuationRing_dominating (Localization.AtPrime P) (IsDiscreteValuationRing.not_isField _)`. Set `g : A →+* O` to `ψ.comp (algebraMap A (Localization.AtPrime P))`. Establish `hg : Function.Injective g` using `hψ.comp (IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors P))`.

Establish `hmem : ∀ a : A, residue O (g a) = 0 ↔ MvPolynomial.map (residue T.V) a = 0`. Introduce `a`. Rewrite using `[residue_eq_zero_iff, ← RingHom.mem_ker, MvPolynomial.ker_map, ker_residue, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, mem_maximalIdeal, mem_nonunits_iff]`. Express the relevant statement in the definitionally equal form `¬ IsUnit (ψ (algebraMap A (Localization.AtPrime P) a)) ↔ a ∈ P`. Rewrite using `[isUnit_map_iff, IsLocalization.AtPrime.isUnit_to_map_iff _ P]`.

Conclude with `not_not`. Set `φ : T.V →+* O` to `g.comp MvPolynomial.C`. Establish `hφ : Function.Injective φ` using `hg.comp (MvPolynomial.C_injective _ _)`. Use `haveI : CharZero O := charZero_of_injective_ringHom hφ`. Use `haveI hl : IsLocalHom φ := ⟨fun a ha => by`.

Assume the negation of the conclusion as `hn`. Establish `h1 : residue T.V a = 0` using `(residue_eq_zero_iff _).2 hn`. Establish `h2` using `(hmem (MvPolynomial.C a)).2 (by rw [MvPolynomial.map_C, h1, map_zero])`. Conclude with `((residue_eq_zero_iff _).1 h2) ha⟩`. Use `⟨⟨O⟩, φ, hl, hφ, fun i => residue O (g (MvPolynomial.X i)), ?_⟩` and prove the remaining obligations.

Use `letI := (ResidueField.map φ).toAlgebra`. Express the relevant statement in the definitionally equal form `AlgebraicIndependent (ResidueField T.V) (fun i => residue O (g (MvPolynomial.X i)))`. Rewrite using `[algebraicIndependent_iff]`. Introduce `q hq`. Take `⟨a, rfl⟩` from `MvPolynomial.map_surjective (σ := ℕ) (residue T.V) residue_surjective q`.

Rewrite using `[← hmem, ← hq]`. Establish `: (residue O).comp g = ((MvPolynomial.aeval (R` using `ResidueField T.V) (fun i => residue O (g (MvPolynomial.X i)))).toRingHom).comp (MvPolynomial.map (residue T.V)) := by`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using `only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, MvPolynomial.algHom_C, MvPolynomial.map_C]`.

Both sides reduce to the same expression. Introduce `i`. Simplify using the standard rewrite rules. Conclude with `congr($this a)`.
-/
theorem exists_gaussExtension : ∀ T : CDVR, ∃ (T' : CDVR) (φ : T.V →+* T'.V) (_ : IsLocalHom φ),
    Function.Injective φ ∧ ∃ t : ℕ → ResidueField T'.V,
      (letI := (ResidueField.map φ).toAlgebra; AlgebraicIndependent (ResidueField T.V) t) := by
  intro T
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  let A := MvPolynomial ℕ T.V
  have hp : Prime (MvPolynomial.C ϖ : A) := (MvPolynomial.prime_C_iff _).2 hϖ.prime
  let P : Ideal A := Ideal.span {MvPolynomial.C ϖ}
  haveI : P.IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  haveI : IsDiscreteValuationRing (Localization.AtPrime P) :=
    isDiscreteValuationRing_localization P _ hp rfl
  obtain ⟨O, _, _, _, _, ψ, hψ, _⟩ := GlobalTheory.exists_complete_discreteValuationRing_dominating
    (Localization.AtPrime P) (IsDiscreteValuationRing.not_isField _)
  let g : A →+* O := ψ.comp (algebraMap A (Localization.AtPrime P))
  have hg : Function.Injective g :=
    hψ.comp (IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors P))
  have hmem : ∀ a : A, residue O (g a) = 0 ↔ MvPolynomial.map (residue T.V) a = 0 := by
    intro a
    rw [residue_eq_zero_iff, ← RingHom.mem_ker, MvPolynomial.ker_map, ker_residue,
      hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, mem_maximalIdeal, mem_nonunits_iff]
    change ¬ IsUnit (ψ (algebraMap A (Localization.AtPrime P) a)) ↔ a ∈ P
    rw [isUnit_map_iff, IsLocalization.AtPrime.isUnit_to_map_iff _ P]
    exact not_not
  let φ : T.V →+* O := g.comp MvPolynomial.C
  have hφ : Function.Injective φ := hg.comp (MvPolynomial.C_injective _ _)
  haveI : CharZero O := charZero_of_injective_ringHom hφ
  haveI hl : IsLocalHom φ := ⟨fun a ha => by
    by_contra hn
    have h1 : residue T.V a = 0 := (residue_eq_zero_iff _).2 hn
    have h2 := (hmem (MvPolynomial.C a)).2 (by rw [MvPolynomial.map_C, h1, map_zero])
    exact ((residue_eq_zero_iff _).1 h2) ha⟩
  refine ⟨⟨O⟩, φ, hl, hφ, fun i => residue O (g (MvPolynomial.X i)), ?_⟩
  letI := (ResidueField.map φ).toAlgebra
  change AlgebraicIndependent (ResidueField T.V) (fun i => residue O (g (MvPolynomial.X i)))
  rw [algebraicIndependent_iff]
  intro q hq
  obtain ⟨a, rfl⟩ := MvPolynomial.map_surjective (σ := ℕ) (residue T.V) residue_surjective q
  rw [← hmem, ← hq]
  have : (residue O).comp g = ((MvPolynomial.aeval (R := ResidueField T.V)
      (fun i => residue O (g (MvPolynomial.X i)))).toRingHom).comp
      (MvPolynomial.map (residue T.V)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
        Function.comp_apply, MvPolynomial.algHom_C, MvPolynomial.map_C]
      rfl
    · intro i
      simp
  exact congr($this a)

end GlobalTheory.GaussCountable
