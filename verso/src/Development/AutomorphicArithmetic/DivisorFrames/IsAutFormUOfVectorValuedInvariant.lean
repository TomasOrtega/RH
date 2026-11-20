import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearActionDualWeylTensor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.BasicNotions GlobalTheory.DefU GlobalTheory.FrameAut Formalism.CohomologicalDescent.DepthNonnegative

/- English proof (translation)
Introduce `E _ _ _ n M _ _ _ R hfin hcont F1 hrat hinf hev ℓ`. Establish `hRU : ∀ (x : UA E n) (φ : UA E n → ℂ) (g : UA E n), RU E n x φ g = φ (g * x)` using `fun _ _ _ => rfl`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[continuous_iff_continuousAt]`. Introduce `g₀`.

Establish `h1 : Continuous fun g : UA E n => ℓ (R g⁻¹ (F1 g₀))` using `(hcont ℓ (F1 g₀)).comp continuous_inv`. Use `h1.continuousAt.congr ?_` and prove the remaining obligations. Establish `ht : Filter.Tendsto (fun g : UA E n => g₀⁻¹ * g) (nhds g₀) (nhds 1)`. Establish `: Continuous fun g : UA E n => g₀⁻¹ * g` using `continuous_const.mul continuous_id`. Establish `h2` using `this.tendsto g₀`.

Rewrite `h2` using `[inv_mul_cancel]`. Then use the resulting hypothesis. Use `filter_upwards [ht.eventually hev] with g hg`. Use `hg g₀` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_left]`. Rewrite using `[this]`.

Introduce `γ hγ g`. Rewrite using `[hrat γ hγ g, ← Module.End.mul_apply, ← map_mul, mul_inv_rev, inv_mul_cancel_right]`. Use `set φ : UA E n → ℂ := fun g => ℓ (R g⁻¹ (F1 g)) with hφ`. Set `S : Subgroup (finU E n)` to `{ carrier := {k : finU E n | RU E n k φ = φ} one_mem' := by simp mul_mem' := by`. Introduce `a b ha hb`.

Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`. Rewrite using `[Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb, ha]`. Use the proof step `inv_mem' := by`. Introduce `a ha`. Simplify using `only [Set.mem_setOf_eq] at ha ⊢`.

Use `conv_lhs => rw [← ha]`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Simplify using `}`. Use `S.isOpen_of_mem_nhds (g := 1) ?_` and prove the remaining obligations. Establish `ht : Filter.Tendsto (fun k : finU E n => (k : UA E n)) (nhds 1) (nhds 1)` using `continuous_subtype_val.tendsto (1 : finU E n)`.

Use `filter_upwards [ht.eventually hev] with k hk`. Use `show RU E n k φ = φ`. Use function extensionality and compare the values at `g`. Rewrite using `[hRU]`. Simplify using `only [hφ]`.

Rewrite using `[hk g, mul_inv_rev, map_mul, hfin _ ((finU E n).inv_mem k.2), one_mul]`. Set `L : (M →ₗ[ℂ] ℂ) →ₗ[ℂ] (UA E n → ℂ)` to `{ toFun := fun ℓ' g => ℓ' (R g⁻¹ (F1 g)) map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Use `Submodule.finiteDimensional_of_le (S₂ := LinearMap.range L) ?_` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`.

Use `⟨ℓ ∘ₗ R (k : UA E n)⁻¹, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Use `show ℓ (R (k : UA E n)⁻¹ (R g⁻¹ (F1 g))) = RU E n k _ g`. Rewrite using `[hRU, hinf _ k.2 g, mul_inv_rev, map_mul, Module.End.mul_apply]`.
-/
theorem UpperTheory.isAutFormU_of_vectorValued_invariant :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (R : UA E n →* Module.End ℂ M),
        (∀ k ∈ finU E n, R k = 1) → (∀ (ℓ : M →ₗ[ℂ] ℂ) (u : M), Continuous fun g => ℓ (R g u)) →
        ∀ F1 : UA E n → M, (∀ γ ∈ ratU E n, ∀ g, F1 (γ * g) = R γ (F1 g)) → (∀ x ∈ infU E n, ∀ g, F1 (g * x) = F1 g) →
        (∀ᶠ y in nhds (1 : UA E n), ∀ g, F1 (g * y) = F1 g) → ∀ ℓ : M →ₗ[ℂ] ℂ, IsAutFormU fun g => ℓ (R g⁻¹ (F1 g)) := by
  intro E _ _ _ n M _ _ _ R hfin hcont F1 hrat hinf hev ℓ
  have hRU : ∀ (x : UA E n) (φ : UA E n → ℂ) (g : UA E n), RU E n x φ g = φ (g * x) := fun _ _ _ => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro g₀
    have h1 : Continuous fun g : UA E n => ℓ (R g⁻¹ (F1 g₀)) := (hcont ℓ (F1 g₀)).comp continuous_inv
    refine h1.continuousAt.congr ?_
    have ht : Filter.Tendsto (fun g : UA E n => g₀⁻¹ * g) (nhds g₀) (nhds 1) := by
      have : Continuous fun g : UA E n => g₀⁻¹ * g := continuous_const.mul continuous_id
      have h2 := this.tendsto g₀
      rwa [inv_mul_cancel] at h2
    filter_upwards [ht.eventually hev] with g hg
    have := hg g₀
    rw [mul_inv_cancel_left] at this
    rw [this]
  · intro γ hγ g
    rw [hrat γ hγ g, ← Module.End.mul_apply, ← map_mul, mul_inv_rev, inv_mul_cancel_right]
  · set φ : UA E n → ℂ := fun g => ℓ (R g⁻¹ (F1 g)) with hφ
    let S : Subgroup (finU E n) :=
      { carrier := {k : finU E n | RU E n k φ = φ}
        one_mem' := by simp
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb, ha]
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at ha ⊢
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul]
          simp }
    refine S.isOpen_of_mem_nhds (g := 1) ?_
    have ht : Filter.Tendsto (fun k : finU E n => (k : UA E n)) (nhds 1) (nhds 1) :=
      continuous_subtype_val.tendsto (1 : finU E n)
    filter_upwards [ht.eventually hev] with k hk
    show RU E n k φ = φ
    funext g
    rw [hRU]
    simp only [hφ]
    rw [hk g, mul_inv_rev, map_mul, hfin _ ((finU E n).inv_mem k.2), one_mul]
  · let L : (M →ₗ[ℂ] ℂ) →ₗ[ℂ] (UA E n → ℂ) :=
      { toFun := fun ℓ' g => ℓ' (R g⁻¹ (F1 g))
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range L) ?_
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine ⟨ℓ ∘ₗ R (k : UA E n)⁻¹, ?_⟩
    funext g
    show ℓ (R (k : UA E n)⁻¹ (R g⁻¹ (F1 g))) = RU E n k _ g
    rw [hRU, hinf _ k.2 g, mul_inv_rev, map_mul, Module.End.mul_apply]
