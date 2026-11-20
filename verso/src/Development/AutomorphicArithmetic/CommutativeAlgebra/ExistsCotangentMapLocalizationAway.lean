import Mathlib

open KaehlerDifferential

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Introduce a local definition for the expression.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Chain the equalities or inequalities of the calculation.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.exists_cotangent_map_localization_away :
    ∀ {R S : Type} [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S] [Algebra R S] [IsScalarTower ℂ R S] (f : R) [IsLocalization.Away f S] (ev : S →+* ℂ) {d : ℕ} (ψ : Ω[R⁄ℂ] →ₗ[ℂ] (Fin d → ℂ)), (∀ (b : R) (ω : Ω[R⁄ℂ]), ψ (b • ω) = ev (algebraMap R S b) • ψ ω) → (∀ ω : Ω[R⁄ℂ], ψ ω = 0 → ∃ (m : ℕ) (b : Fin m → R) (ω' : Fin m → Ω[R⁄ℂ]), (∀ i, ev (algebraMap R S (b i)) = 0) ∧ ω = ∑ i, b i • ω' i) → ∃ ψ' : Ω[S⁄ℂ] →ₗ[ℂ] (Fin d → ℂ), (∀ (b : S) (ω : Ω[S⁄ℂ]), ψ' (b • ω) = ev b • ψ' ω) ∧ (∀ ω : Ω[R⁄ℂ], ψ' (KaehlerDifferential.map ℂ ℂ R S ω) = ψ ω) ∧ (∀ ω : Ω[S⁄ℂ], ψ' ω = 0 → ∃ (m : ℕ) (b : Fin m → S) (ω' : Fin m → Ω[S⁄ℂ]), (∀ i, ev (b i) = 0) ∧ ω = ∑ i, b i • ω' i) := by
  intro R S _ _ _ _ _ _ f _ ev d ψ h1 h2
  letI : Module R (Fin d → ℂ) := Module.compHom (Fin d → ℂ) (ev.comp (algebraMap R S))
  have hu : ∀ x : Submonoid.powers f, ev (algebraMap R S x) ≠ 0 := fun x =>
    ((IsLocalization.map_units S x).map ev).ne_zero
  have hunit : ∀ x : Submonoid.powers f,
      IsUnit ((algebraMap R (Module.End R (Fin d → ℂ))) x) := by
    intro x
    rw [Module.End.isUnit_iff]
    refine ⟨fun v w hvw => smul_right_injective (Fin d → ℂ) (hu x) hvw,
      fun v => ⟨(ev (algebraMap R S x))⁻¹ • v, ?_⟩⟩
    show ev (algebraMap R S x) • ((ev (algebraMap R S x))⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ (hu x), one_smul]
  let g : Ω[R⁄ℂ] →ₗ[R] (Fin d → ℂ) :=
    { toFun := ψ, map_add' := ψ.map_add, map_smul' := fun b ω => h1 b ω }
  let L := IsLocalizedModule.lift (Submonoid.powers f) (KaehlerDifferential.map ℂ ℂ R S) g hunit
  have hL : ∀ η, L (KaehlerDifferential.map ℂ ℂ R S η) = ψ η := fun η =>
    IsLocalizedModule.lift_apply _ _ _ _ η
  have hLs : ∀ (r : R) (ω : Ω[S⁄ℂ]), L (r • ω) = ev (algebraMap R S r) • L ω :=
    fun r ω => L.map_smul r ω
  have hLS : ∀ (b : S) (ω : Ω[S⁄ℂ]), L (b • ω) = ev b • L ω := by
    intro b ω
    obtain ⟨⟨r, t⟩, ht⟩ := IsLocalization.surj (Submonoid.powers f) b
    have h := hLs (t : R) (b • ω)
    rw [← algebraMap_smul S (t : R) (b • ω), smul_smul, mul_comm, ht, algebraMap_smul, hLs] at h
    apply smul_right_injective (Fin d → ℂ) (hu t)
    show ev (algebraMap R S t) • L (b • ω) = ev (algebraMap R S t) • ev b • L ω
    rw [← h, ← ht, map_mul, mul_comm, mul_smul]
  have hLC : ∀ (c : ℂ) (ω : Ω[S⁄ℂ]), L (c • ω) = c • L ω := by
    intro c ω
    obtain ⟨⟨η, s⟩, hs⟩ :=
      IsLocalizedModule.surj (Submonoid.powers f) (KaehlerDifferential.map ℂ ℂ R S) ω
    have hs' : (s : R) • ω = KaehlerDifferential.map ℂ ℂ R S η := hs
    have e1 : ev (algebraMap R S s) • L ω = ψ η := by rw [← hLs, hs', hL]
    have e2 : ev (algebraMap ℂ S c) • ψ η = c • ψ η := by
      rw [show c • ψ η = ψ (c • η) from (ψ.map_smul c η).symm, ← algebraMap_smul R c η, h1,
        ← IsScalarTower.algebraMap_apply]
    rw [← algebraMap_smul S c ω, hLS]
    apply smul_right_injective (Fin d → ℂ) (hu s)
    show ev (algebraMap R S s) • ev (algebraMap ℂ S c) • L ω = ev (algebraMap R S s) • c • L ω
    rw [smul_comm (ev (algebraMap R S s)) (ev (algebraMap ℂ S c)), e1, e2,
      smul_comm (ev (algebraMap R S s)) c, e1]
  refine ⟨{ toFun := L, map_add' := L.map_add, map_smul' := hLC }, hLS, hL, ?_⟩
  intro ω hω
  change L ω = 0 at hω
  obtain ⟨⟨η, s⟩, hs⟩ :=
    IsLocalizedModule.surj (Submonoid.powers f) (KaehlerDifferential.map ℂ ℂ R S) ω
  have hs' : (s : R) • ω = KaehlerDifferential.map ℂ ℂ R S η := hs
  have hη : ψ η = 0 := by rw [← hL, ← hs', hLs, hω, smul_zero]
  obtain ⟨m, b, ω', hb, hηeq⟩ := h2 η hη
  let u : S := IsLocalization.mk' S (1 : R) s
  have hu1 : u * algebraMap R S s = 1 := by rw [IsLocalization.mk'_spec, map_one]
  refine ⟨m, fun i => algebraMap R S (b i),
    fun i => u • KaehlerDifferential.map ℂ ℂ R S (ω' i), hb, ?_⟩
  calc ω = u • ((s : R) • ω) := by
        rw [← algebraMap_smul S (s : R) ω, smul_smul, hu1, one_smul]
    _ = u • KaehlerDifferential.map ℂ ℂ R S (∑ i, b i • ω' i) := by rw [hs', hηeq]
    _ = ∑ i, algebraMap R S (b i) • u • KaehlerDifferential.map ℂ ℂ R S (ω' i) := by
        rw [map_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, ← algebraMap_smul S (b i), smul_comm]
