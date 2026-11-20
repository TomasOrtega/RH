import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneCard

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.UnitaryBC UpperTheory.V
open UpperTheory.V.W (Plc Lp resP)

/- English proof (translation)
Introduce `L Ω _ _ _ _ _ _ h w`. Take `⟨A, hA⟩` from `exists_valuationSubring_over (Ω := Ω) w`. Set `v : Plc (Lp L)` to `⟨w.asIdeal.comap (algebraMap (𝓞 (Lp L)) (𝓞 L)), inferInstance, by`. Conclude with `Ideal.IsMaximal.ne_bot_of_isIntegral_int (Ideal.comap (algebraMap (𝓞 (Lp L)) (𝓞 L)) w.asIdeal)⟩`. Establish `hv : IsPlaceOver A v`.

Introduce `x`. Establish `h1` using `hA (algebraMap (𝓞 (Lp L)) (𝓞 L) x)`. Use `show _ ↔ algebraMap (𝓞 (Lp L)) (𝓞 L) x ∈ w.asIdeal`. Rewrite using `[← h1, IsScalarTower.algebraMap_apply (Lp L) L Ω]`. Both sides reduce to the same expression.

Establish `hle` using `h A v hv`. Establish `hbot : Ideal.inertia Gal(L/(Lp L)) w.asIdeal = ⊥`. Rewrite using `[← UpperTheory.V.CF.ineAbs (Lp L) L Ω A w hA, eq_bot_iff]`. Introduce and unpack `_ ⟨σ, hσ, rfl⟩`. Take `⟨τ, rfl⟩` from `hle hσ`.

Rewrite using `[Subgroup.mem_bot]`. Use extensionality with `x`. Apply `(algebraMap L Ω).injective` to reduce the goal to its premises. Rewrite using `[AlgEquiv.one_apply]`. Use `show algebraMap L Ω ((AlgEquiv.restrictScalars (Lp L) τ).restrictNormal L x) = _`.

Rewrite using `[AlgEquiv.restrictNormal_commutes]`. Conclude with `τ.commutes x`. Use `Ideal.ramificationIdx_eq_one_iff.mp ?_` and prove the remaining obligations. Rewrite using `[← (UpperTheory.V.CF.ineCard).1 (Lp L) L w, hbot]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.isUnramifiedAt_totallyReal_of_inertia_le_restriction_range :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω], (∀ (A : ValuationSubring Ω) (v : Plc (Lp L)), IsPlaceOver A v → Ine (F := Lp L) A ≤ (resP L Ω).range) → ∀ w : Plc L, Algebra.IsUnramifiedAt (𝓞 (Lp L)) w.asIdeal := by
  intro L Ω _ _ _ _ _ _ h w
  obtain ⟨A, hA⟩ := exists_valuationSubring_over (Ω := Ω) w
  let v : Plc (Lp L) := ⟨w.asIdeal.comap (algebraMap (𝓞 (Lp L)) (𝓞 L)), inferInstance, by
    exact Ideal.IsMaximal.ne_bot_of_isIntegral_int (Ideal.comap (algebraMap (𝓞 (Lp L)) (𝓞 L)) w.asIdeal)⟩
  have hv : IsPlaceOver A v := by
    intro x
    have h1 := hA (algebraMap (𝓞 (Lp L)) (𝓞 L) x)
    show _ ↔ algebraMap (𝓞 (Lp L)) (𝓞 L) x ∈ w.asIdeal
    rw [← h1, IsScalarTower.algebraMap_apply (Lp L) L Ω]
    rfl
  have hle := h A v hv
  have hbot : Ideal.inertia Gal(L/(Lp L)) w.asIdeal = ⊥ := by
    rw [← UpperTheory.V.CF.ineAbs (Lp L) L Ω A w hA, eq_bot_iff]
    rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨τ, rfl⟩ := hle hσ
    rw [Subgroup.mem_bot]
    ext x
    apply (algebraMap L Ω).injective
    rw [AlgEquiv.one_apply]
    show algebraMap L Ω ((AlgEquiv.restrictScalars (Lp L) τ).restrictNormal L x) = _
    rw [AlgEquiv.restrictNormal_commutes]
    exact τ.commutes x
  refine Ideal.ramificationIdx_eq_one_iff.mp ?_
  rw [← (UpperTheory.V.CF.ineCard).1 (Lp L) L w, hbot]
  simp
