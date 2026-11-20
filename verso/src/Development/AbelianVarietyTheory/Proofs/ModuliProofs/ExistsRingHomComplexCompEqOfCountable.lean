import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

/- English proof (translation)
Take `⟨J, v, hv⟩` from `exists_isTranscendenceBasis' R K`. Take `⟨Jc, w, hw⟩` from `exists_isTranscendenceBasis' R ℂ`. Use `haveI : Countable J := hv.1.injective.countable`. Establish `hκ : Cardinal.aleph0 < Cardinal.mk Jc`. Assume the negation of the conclusion as `hlt`.

Establish `hle` using `not_lt.1 hlt`. Establish `h1` using `IsAlgClosed.cardinal_le_max_transcendence_basis' w hw`. Rewrite `h1` using `[Cardinal.mk_complex]`. Conclude with `absurd (h1.trans (max_le (max_le Cardinal.mk_le_aleph0 hle) le_rfl)) (not_le.2 Cardinal.aleph0_lt_continuum)`. Take `⟨e⟩ : Nonempty (J ↪ Jc)` from `(Cardinal.le_def J Jc).1 (Cardinal.mk_le_aleph0.trans hκ.le)`.

Set `S` to `Algebra.adjoin R (Set.range v)`. Set `φ : S →ₐ[R] ℂ` to `(MvPolynomial.aeval (w ∘ e)).comp hv.1.aevalEquiv.symm.toAlgHom`. Establish `hind : AlgebraicIndependent R (w ∘ e)` using `hw.1.comp e e.injective`. Establish `hφ : Function.Injective φ`. Establish `hind' : Function.Injective (MvPolynomial.aeval (R` using `R) (w ∘ e)) := hind`.

Simplify using `only [φ, AlgHom.coe_comp]`. Conclude with `hind'.comp hv.1.aevalEquiv.symm.injective`. Use `letI : Algebra S ℂ := φ.toRingHom.toAlgebra`. Use `haveI : Module.IsTorsionFree S ℂ := Module.isTorsionFree_iff_algebraMap_injective.2 hφ`. Use `haveI : Module.IsTorsionFree S K := Module.isTorsionFree_iff_algebraMap_injective.2 Subtype.val_injective`.

Use `haveI : Algebra.IsAlgebraic S K := hv.isAlgebraic`. Set `g : K →ₐ[S] ℂ` to `IsAlgClosed.lift`. Use `⟨{ g.toRingHom with commutes' := fun r => ?_ }⟩` and prove the remaining obligations. Use `show g (algebraMap R K r) = algebraMap R ℂ r`. Rewrite using `[IsScalarTower.algebraMap_apply R S K r, g.commutes]`.

Conclude with `φ.commutes r`.
-/
theorem nonempty_algHom_complex_of_countable (R K : Type) [CommRing R] [IsDomain R] [Countable R]
    [Field K] [Countable K] [Algebra R K] [Algebra R ℂ] [FaithfulSMul R K] [FaithfulSMul R ℂ] :
    Nonempty (K →ₐ[R] ℂ) := by
  obtain ⟨J, v, hv⟩ := exists_isTranscendenceBasis' R K
  obtain ⟨Jc, w, hw⟩ := exists_isTranscendenceBasis' R ℂ
  haveI : Countable J := hv.1.injective.countable
  have hκ : Cardinal.aleph0 < Cardinal.mk Jc := by
    by_contra hlt
    have hle := not_lt.1 hlt
    have h1 := IsAlgClosed.cardinal_le_max_transcendence_basis' w hw
    rw [Cardinal.mk_complex] at h1
    exact absurd (h1.trans (max_le (max_le Cardinal.mk_le_aleph0 hle) le_rfl))
      (not_le.2 Cardinal.aleph0_lt_continuum)
  obtain ⟨e⟩ : Nonempty (J ↪ Jc) :=
    (Cardinal.le_def J Jc).1 (Cardinal.mk_le_aleph0.trans hκ.le)
  let S := Algebra.adjoin R (Set.range v)
  let φ : S →ₐ[R] ℂ := (MvPolynomial.aeval (w ∘ e)).comp hv.1.aevalEquiv.symm.toAlgHom
  have hind : AlgebraicIndependent R (w ∘ e) := hw.1.comp e e.injective
  have hφ : Function.Injective φ := by
    have hind' : Function.Injective (MvPolynomial.aeval (R := R) (w ∘ e)) := hind
    simp only [φ, AlgHom.coe_comp]
    exact hind'.comp hv.1.aevalEquiv.symm.injective
  letI : Algebra S ℂ := φ.toRingHom.toAlgebra
  haveI : Module.IsTorsionFree S ℂ := Module.isTorsionFree_iff_algebraMap_injective.2 hφ
  haveI : Module.IsTorsionFree S K :=
    Module.isTorsionFree_iff_algebraMap_injective.2 Subtype.val_injective
  haveI : Algebra.IsAlgebraic S K := hv.isAlgebraic
  let g : K →ₐ[S] ℂ := IsAlgClosed.lift
  refine ⟨{ g.toRingHom with commutes' := fun r => ?_ }⟩
  show g (algebraMap R K r) = algebraMap R ℂ r
  rw [IsScalarTower.algebraMap_apply R S K r, g.commutes]
  exact φ.commutes r

/- English proof (translation)
Rewrite using `[isJacobsonRing_iff_prime_eq]`. Introduce `P hP`. Distinguish the cases in `hbot : P = ⊥`. Substitute `hbot` using the available equality. Use `le_antisymm (fun x hx => ?_) Ideal.le_jacobson` and prove the remaining obligations.

Take `⟨z, hz⟩` from `(Ideal.mem_jacobson_iff.1 hx) x`. Rewrite `hz`, the goal using `[Ideal.mem_bot]`. Establish `hu : IsUnit (x * x + 1)` using `IsUnit.of_mul_eq_one z (by linear_combination hz)`. Break down `Int.isUnit_iff.1 hu with h | h` into its components or cases. Conclude with `mul_self_eq_zero.1 (by linarith)`.

Use polynomial arithmetic with `[mul_self_nonneg x]`. Use `haveI := hP.isMaximal hbot`. Conclude with `Ideal.jacobson_eq_self_of_isMaximal`.
-/
private theorem isJacobsonRing_int' : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases hbot : P = ⊥
  · subst hbot
    refine le_antisymm (fun x hx => ?_) Ideal.le_jacobson
    obtain ⟨z, hz⟩ := (Ideal.mem_jacobson_iff.1 hx) x
    rw [Ideal.mem_bot] at hz ⊢
    have hu : IsUnit (x * x + 1) := IsUnit.of_mul_eq_one z (by linear_combination hz)
    rcases Int.isUnit_iff.1 hu with h | h
    · exact mul_self_eq_zero.1 (by linarith)
    · nlinarith [mul_self_nonneg x]
  · haveI := hP.isMaximal hbot
    exact Ideal.jacobson_eq_self_of_isMaximal

/- English proof (translation)
Use `haveI := isJacobsonRing_int'`. Assume the negation of the conclusion as `hβ`. Establish `hker : RingHom.ker β ≠ ⊥` using `fun h => hβ ((RingHom.injective_iff_ker_eq_bot β).2 h)`. Use `haveI : (RingHom.ker β).IsMaximal := (RingHom.ker_isPrime β).isMaximal hker`. Use `letI : Field (o ⧸ RingHom.ker β) := Ideal.Quotient.field _`.

Use `haveI : Algebra.FiniteType ℤ (o ⧸ RingHom.ker β) := Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ _) (Ideal.Quotient.mkₐ_surjective ℤ _)`. Use `haveI : Module.Finite ℤ (o ⧸ RingHom.ker β) := finite_of_finite_type_of_isJacobsonRing ℤ _`. Use `haveI : Algebra.IsIntegral ℤ (o ⧸ RingHom.ker β) := Algebra.IsIntegral.of_finite ℤ _`. Establish `hinj : Function.Injective (algebraMap ℤ (o ⧸ RingHom.ker β))`. Introduce `a b hab`.

Establish `hk` using `congrArg (RingHom.kerLift β) hab`. Simplify using `only [eq_intCast, map_intCast] at hk`. Conclude with `Int.cast_injective hk`. Conclude with `Int.not_isField (isField_of_isIntegral_of_isField hinj (Field.toIsField _))`.
-/
theorem injective_of_finiteType_int_of_charZero {o K : Type} [CommRing o] [IsDomain o]
    [Ring.DimensionLEOne o] [Algebra.FiniteType ℤ o] [Field K] [CharZero K] (β : o →+* K) :
    Function.Injective β := by
  haveI := isJacobsonRing_int'
  by_contra hβ
  have hker : RingHom.ker β ≠ ⊥ := fun h => hβ ((RingHom.injective_iff_ker_eq_bot β).2 h)
  haveI : (RingHom.ker β).IsMaximal := (RingHom.ker_isPrime β).isMaximal hker
  letI : Field (o ⧸ RingHom.ker β) := Ideal.Quotient.field _
  haveI : Algebra.FiniteType ℤ (o ⧸ RingHom.ker β) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ _)
      (Ideal.Quotient.mkₐ_surjective ℤ _)
  haveI : Module.Finite ℤ (o ⧸ RingHom.ker β) := finite_of_finite_type_of_isJacobsonRing ℤ _
  haveI : Algebra.IsIntegral ℤ (o ⧸ RingHom.ker β) := Algebra.IsIntegral.of_finite ℤ _
  have hinj : Function.Injective (algebraMap ℤ (o ⧸ RingHom.ker β)) := by
    intro a b hab
    have hk := congrArg (RingHom.kerLift β) hab
    simp only [eq_intCast, map_intCast] at hk
    exact Int.cast_injective hk
  exact Int.not_isField (isField_of_isIntegral_of_isField hinj (Field.toIsField _))

/- English proof (translation)
Introduce `o _ em K₀ _ _ _ β hD hF hem`. Use `haveI := hD`. Use `haveI := hF`. Establish `hβ : Function.Injective β` using `injective_of_finiteType_int_of_charZero β`. Establish `hcount : Countable o`.

Take `⟨n, f, hf⟩` from `Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hF`. Establish `hc : Countable (MvPolynomial (Fin n) ℤ)`. Rewrite using `[← Cardinal.mk_le_aleph0_iff]`. Conclude with `MvPolynomial.cardinalMk_le_max.trans (max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl)`. Conclude with `hf.countable`.

Use `⟨hcount, ?_⟩` and prove the remaining obligations. Use `haveI := hcount`. Use `letI : Algebra o K₀ := β.toAlgebra`. Use `letI : Algebra o ℂ := em.toAlgebra`. Use `haveI : FaithfulSMul o K₀ := (faithfulSMul_iff_algebraMap_injective o K₀).2 hβ`.

Use `haveI : FaithfulSMul o ℂ := (faithfulSMul_iff_algebraMap_injective o ℂ).2 hem`. Take `⟨g⟩` from `nonempty_algHom_complex_of_countable o K₀`. Conclude with `⟨g.toRingHom, RingHom.ext fun x => g.commutes x⟩`.
-/
theorem exists_ringHom_complex_comp_eq_of_countable :
    ∀ (o : Type) [CommRing o] (em : o →+* ℂ) (K₀ : Type) [Field K₀] [CharZero K₀] [Countable K₀] (β : o →+* K₀), IsDedekindDomain o → Algebra.FiniteType ℤ o → Function.Injective em → Countable o ∧ ∃ j : K₀ →+* ℂ, j.comp β = em := by
  intro o _ em K₀ _ _ _ β hD hF hem
  haveI := hD
  haveI := hF
  have hβ : Function.Injective β := injective_of_finiteType_int_of_charZero β
  have hcount : Countable o := by
    obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hF
    have hc : Countable (MvPolynomial (Fin n) ℤ) := by
      rw [← Cardinal.mk_le_aleph0_iff]
      exact MvPolynomial.cardinalMk_le_max.trans
        (max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl)
    exact hf.countable
  refine ⟨hcount, ?_⟩
  haveI := hcount
  letI : Algebra o K₀ := β.toAlgebra
  letI : Algebra o ℂ := em.toAlgebra
  haveI : FaithfulSMul o K₀ := (faithfulSMul_iff_algebraMap_injective o K₀).2 hβ
  haveI : FaithfulSMul o ℂ := (faithfulSMul_iff_algebraMap_injective o ℂ).2 hem
  obtain ⟨g⟩ := nonempty_algHom_complex_of_countable o K₀
  exact ⟨g.toRingHom, RingHom.ext fun x => g.commutes x⟩

end GlobalTheory
