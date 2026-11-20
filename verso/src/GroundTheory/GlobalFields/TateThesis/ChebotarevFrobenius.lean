import Mathlib
import GroundTheory.GlobalFields.SplittingFromInequality.Decomposition

namespace GroundTheory.Global

open NumberField IsDedekindDomain IntermediateField
open scoped Pointwise

noncomputable section

section Unique

variable {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
  [IsGalois F L]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem arithFrobAt_eq_of_isArithFrobAt (w : HeightOneSpectrum (𝓞 L))
    (he : w.asIdeal.ramificationIdx (𝓞 F) = 1) {τ : Gal(L/F)}
    (hτ : IsArithFrobAt (𝓞 F) τ w.asIdeal) : arithFrobAt (𝓞 F) Gal(L/F) w.asIdeal = τ := by
  have : IsGaloisGroup Gal(L/F) (𝓞 F) (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ F L
  have hmem := (IsArithFrobAt.arithFrobAt (𝓞 F) Gal(L/F) w.asIdeal).mul_inv_mem_inertia hτ
  have hcard : Nat.card (w.asIdeal.inertia Gal(L/F)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (w.asIdeal.under (𝓞 F)) w.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx _ w.asIdeal Gal(L/F)]
    exact he
  rw [Subgroup.card_eq_one.mp hcard, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  exact hmem

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem ramificationIdx_smul (τ : Gal(L/F)) (w : HeightOneSpectrum (𝓞 L)) :
    (τ • w).asIdeal.ramificationIdx (𝓞 F) = w.asIdeal.ramificationIdx (𝓞 F) := by
  have : IsGaloisGroup Gal(L/F) (𝓞 F) (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ F L
  have : (τ • w).asIdeal.LiesOver (AdeleBaseChange.below F w).asIdeal :=
    (AdeleBaseChange.below_eq_iff _ _).1 (below_smul τ w)
  exact Ideal.ramificationIdx_eq_of_isGaloisGroup (AdeleBaseChange.below F w).asIdeal
    (τ • w).asIdeal w.asIdeal Gal(L/F)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem arithFrobAt_smul (τ : Gal(L/F)) (w : HeightOneSpectrum (𝓞 L))
    (he : w.asIdeal.ramificationIdx (𝓞 F) = 1) :
    arithFrobAt (𝓞 F) Gal(L/F) (τ • w).asIdeal =
      τ * arithFrobAt (𝓞 F) Gal(L/F) w.asIdeal * τ⁻¹ :=
  arithFrobAt_eq_of_isArithFrobAt (τ • w) (by rw [ramificationIdx_smul, he])
    ((IsArithFrobAt.arithFrobAt (𝓞 F) Gal(L/F) w.asIdeal).conj τ)

end Unique

section Tower

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem isArithFrobAt_restrictScalars_iff (E : IntermediateField K L) (w : HeightOneSpectrum (𝓞 L))
    (hf : (w.asIdeal.under (𝓞 E)).inertiaDeg (𝓞 K) = 1) (τ : Gal(L/E)) :
    IsArithFrobAt (𝓞 K) (τ.restrictScalars K) w.asIdeal ↔ IsArithFrobAt (𝓞 E) τ w.asIdeal := by
  have hcard : Nat.card (𝓞 K ⧸ w.asIdeal.under (𝓞 K)) =
      Nat.card (𝓞 E ⧸ w.asIdeal.under (𝓞 E)) := by
    have h := Ideal.absNorm_pow_inertiaDeg ((w.asIdeal.under (𝓞 E)).under (𝓞 K))
      (w.asIdeal.under (𝓞 E))
    rw [hf, pow_one, Ideal.under_under] at h
    rw [← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
      ← Ideal.absNorm_apply, h]
  change (∀ x, _ - x ^ Nat.card (𝓞 K ⧸ w.asIdeal.under (𝓞 K)) ∈ w.asIdeal) ↔
    (∀ x, _ - x ^ Nat.card (𝓞 E ⧸ w.asIdeal.under (𝓞 E)) ∈ w.asIdeal)
  rw [hcard]
  rfl

variable [IsGalois K L]

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem eq_of_under_eq_of_le_stabilizer (H : Subgroup Gal(L/K)) (w w' : HeightOneSpectrum (𝓞 L))
    (hH : H ≤ MulAction.stabilizer Gal(L/K) w.asIdeal)
    (h : w'.asIdeal.under (𝓞 (fixedField H)) = w.asIdeal.under (𝓞 (fixedField H))) : w' = w := by
  have : IsGaloisGroup Gal(L/fixedField H) (𝓞 (fixedField H)) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing _ _ _ (fixedField H) L
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 (fixedField H)) (𝓞 L)
    Gal(L/fixedField H) w.asIdeal w'.asIdeal h.symm
  have hgH : g.restrictScalars K ∈ H := by
    have h1 : g.restrictScalars K ∈ fixingSubgroup (fixedField H) :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx ↦ g.commutes ⟨x, hx⟩
    rwa [fixingSubgroup_fixedField] at h1
  have hs := hH hgH
  rw [MulAction.mem_stabilizer_iff] at hs
  refine HeightOneSpectrum.ext ?_
  rw [hg]
  exact hs

end Tower

end

end GroundTheory.Global
