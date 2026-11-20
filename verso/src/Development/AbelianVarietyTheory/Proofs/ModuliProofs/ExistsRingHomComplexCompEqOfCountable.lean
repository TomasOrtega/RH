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
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Introduce a local definition for the expression.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Equip the data with the indicated structure.

Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Use the polynomial consequences of the given equalities and inequalities.

A detailed English derivation is pending.
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
Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Equip the data with the indicated structure. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Equip the data with the indicated structure. Equip the data with the indicated structure. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. A detailed English derivation is pending.
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
