import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfDimOfFinrankDerivatio

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SmoothDirections

noncomputable def derivationPoint {k R K : Type} [CommRing k] [CommRing R] [Field K]
    [Algebra k R] [Algebra k K] [Algebra R K] [IsScalarTower k R K] {r : ℕ}
    (D : Fin r → Derivation k R K) : R →+* TrivSqZeroExt K (Fin r → K) where
  toFun a := TrivSqZeroExt.inl (algebraMap R K a) + TrivSqZeroExt.inr fun i ↦ D i a
  map_one' := by
    refine TrivSqZeroExt.ext (by simp) ?_
    funext i
    simp
  map_mul' a b := by
    refine TrivSqZeroExt.ext (by simp) ?_
    funext i
    simp [Algebra.smul_def, mul_comm]
  map_zero' := by
    refine TrivSqZeroExt.ext (by simp) ?_
    funext i
    simp
  map_add' a b := by
    refine TrivSqZeroExt.ext (by simp) ?_
    funext i
    simp

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts.
-/
theorem finrank_derivation_le {k R K : Type} [Field k] [CommRing R] [Field K]
    [Algebra k R] [Algebra k K] [Algebra R K] [IsScalarTower k R K] {X : Scheme.{0}}
    (s : X ⟶ Sp k) (j : Sp R ⟶ X) [Mono j] (hj : j ≫ s = spMap (algebraMap k R)) {d : ℕ}
    (ht : ∀ (r : ℕ) (β : k →+* K) (x : Sp (TrivSqZeroExt K (Fin r → K)) ⟶ X),
      x ≫ s = spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) →
      (∀ lam : (Fin r → K) →ₗ[K] K,
        spMap (dirMap lam) ≫ x = constPt (spMap (dirMap lam) ≫ x) → lam = 0) → r ≤ d) :
    Module.finrank K (Derivation k R K) ≤ d := by
  obtain ⟨D, hD⟩ := exists_linearIndependent_of_le_finrank
    (le_refl (Module.finrank K (Derivation k R K)))
  refine ht _ (algebraMap k K) (spMap (derivationPoint D) ≫ j) ?_ ?_
  · rw [Category.assoc, hj, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun a ↦ TrivSqZeroExt.ext ?_ ?_
    · simp [derivationPoint, ← IsScalarTower.algebraMap_apply, TrivSqZeroExt.algebraMap_eq_inl]
    · funext i
      simp [derivationPoint, TrivSqZeroExt.algebraMap_eq_inl]
  · intro lam h
    simp only [constPt, ← Category.assoc, cancel_mono] at h
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp] at h
    have h₁ := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
    have h₂ (a : R) : lam (fun i ↦ D i a) = 0 := by
      have := congrArg TrivSqZeroExt.snd (RingHom.congr_fun h₁ a)
      simpa [dirMap, derivationPoint, TrivSqZeroExt.algebraMap_eq_inl] using this
    have h₃ := Fintype.linearIndependent_iff.mp hD (fun i ↦ lam (Pi.single i 1)) (by
      ext a
      have := h₂ a
      rw [← Finset.univ_sum_single (fun i ↦ D i a), map_sum] at this
      rw [Derivation.zero_apply, ← this]
      refine (congrFun (map_sum (Derivation.coeFnAddMonoidHom (R := k) (A := R) (M := K)) _ _) a).trans ?_
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      change lam (Pi.single i 1) • D i a = _
      rw [smul_eq_mul, mul_comm, ← smul_eq_mul, ← map_smul, ← Pi.single_smul, smul_eq_mul,
        _root_.mul_one])
    refine (Pi.basisFun K _).ext fun i ↦ ?_
    simpa using h₃ i

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

A detailed English derivation is pending.
-/
theorem smoothOfRelativeDimension_of_forall_finrank_derivation_le (k : Type) [Field k]
    [PerfectField k] (R : Type) [CommRing R] [Algebra k R] [Algebra.FiniteType k R] (d : ℕ)
    (hd : ∀ q ∈ minimalPrimes R, (d : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ q))
    (ht : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra k K] [Algebra R K] [IsScalarTower k R K],
      Module.finrank K (Derivation k R K) ≤ d) :
    SmoothOfRelativeDimension d (spMap (algebraMap k R)) := by
  have : Algebra.FinitePresentation k R := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have key (m : Ideal R) (hm : m.IsMaximal) :
      ∃ f ∉ m, Algebra.IsStandardSmoothOfRelativeDimension d k (Localization.Away f) := by
    have h₁ : (d : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime m) := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m)]
      exact_mod_cast SmoothTangent.le_height_of_forall_minimalPrimes k hd m
    have h₂ : Module.finrank (R ⧸ m) m.Cotangent ≤ d := by
      let := Ideal.Quotient.field m
      exact (SmoothTangent.finrank_cotangent_le_finrank_derivation k m
        (AlgebraicClosure (R ⧸ m))).trans (ht _)
    obtain ⟨-, -, -, h₃, -, h₄⟩ := isSmoothAt_of_finrank_cotangent_le_of_perfectField k m h₁ h₂
    exact exists_isStandardSmoothOfRelativeDimension_of_isSmoothAt k m h₄
  refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d)).mpr ?_
  refine ⟨{f | Algebra.IsStandardSmoothOfRelativeDimension d k (Localization.Away f)}, ?_, ?_⟩
  · by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨f, hf, hs⟩ := key m hm
    exact hf (hle (Ideal.subset_span hs))
  · intro f hf
    have := (RingHom.isStandardSmoothOfRelativeDimension_algebraMap d).mpr hf
    rwa [IsScalarTower.algebraMap_eq k R] at this

end GlobalTheory.SmoothDirections

namespace GlobalTheory

open SmoothDirections

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Introduce a local definition for the expression.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem smoothOfRelativeDimension_of_dim_of_directions_le :
    ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) (s : X ⟶ Sp k) (d : ℕ),
      LocallyOfFiniteType s →
      (∀ (R : Type) [CommRing R] [Algebra k R] (x : Sp R ⟶ X), IsOpenImmersion x →
        x ≫ s = spMap (algebraMap k R) →
        ∀ q ∈ minimalPrimes R, (d : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ q)) →
      (∀ (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (β : k →+* K)
        (x : Sp (TrivSqZeroExt K (Fin r → K)) ⟶ X),
        x ≫ s = spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) →
        (∀ lam : (Fin r → K) →ₗ[K] K,
          spMap (dirMap lam) ≫ x = constPt (spMap (dirMap lam) ≫ x) → lam = 0) → r ≤ d) →
      SmoothOfRelativeDimension d s := by
  intro k _ _ X s d _ hd ht
  choose A iA aA j hj q hq hjs using exists_affine_chart_over s
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension d)
  refine IsZariskiLocalAtSource.of_openCover
    (Scheme.Cover.mkOfCovers X (fun x ↦ Sp (A x)) j (fun x ↦ ⟨x, q x, hq x⟩) hj)
    fun (x : X) ↦ ?_
  change SmoothOfRelativeDimension d (j x ≫ s)
  let := iA x
  let := aA x
  have := hj x
  have : Algebra.FiniteType k (A x) := RingHom.finiteType_algebraMap.mp <|
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
      (φ := CommRingCat.ofHom (algebraMap k (A x)))).mp (hjs x ▸ inferInstance)
  rw [hjs]
  exact smoothOfRelativeDimension_of_forall_finrank_derivation_le k (A x) d
    (hd _ (j x) (hj x) (hjs x)) fun K _ _ _ _ _ ↦ finrank_derivation_le s (j x) (hjs x) (ht K)

end GlobalTheory
