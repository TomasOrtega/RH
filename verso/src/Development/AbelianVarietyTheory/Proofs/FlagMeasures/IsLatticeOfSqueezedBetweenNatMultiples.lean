import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemSpanSingleIff
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

/- English proof (translation)
Establish `hNE : (N : E) ≠ 0` using `Nat.cast_ne_zero.mpr hN`. Set `f : (Fin n → 𝓞 E) →ₗ[𝓞 E] (Fin n → E)` to `((N : E)⁻¹ • (LinearMap.pi fun i => (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj i)))`. Establish `hle : Γ ≤ LinearMap.range f`. Introduce `x hx`. Use `⟨fun i => ⟨(N : E) * x i, hup x hx i⟩, ?_⟩` and prove the remaining obligations.

Use extensionality with `i`. Express the relevant statement in the definitionally equal form `(N : E)⁻¹ * ((N : E) * x i) = x i`. Rewrite using `[← mul_assoc, inv_mul_cancel₀ hNE, one_mul]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Submodule.map_comap_eq_self hle]`.

Conclude with `(IsNoetherian.noetherian _).map f`. Rewrite using `[eq_top_iff]`. Introduce `y _`. Rewrite using `[pi_eq_sum_univ y]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations.

Establish `hmem : (N : E) • (fun j => if i = j then (1 : E) else 0) ∈ Γ`. Apply `hlow` to reduce the goal to its premises. Introduce `j`. Use `split_ifs`. Conclude with `isIntegral_one`.

Conclude with `isIntegral_zero`. Establish `: (fun j => if i = j then (1 : E) else 0) = (N : E)⁻¹ • ((N : E) • (fun j => if i = j then (1 : E) else 0))`. Rewrite using `[smul_smul, inv_mul_cancel₀ hNE, one_smul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hmem)`.
-/
theorem GlobalTheory.glue_latt_isLattice {E : Type} [Field E] [NumberField E] (n : ℕ) (Γ : Submodule (𝓞 E) (Fin n → E)) (N : ℕ) (hN : N ≠ 0)
    (hlow : ∀ x : Fin n → E, (∀ i, IsIntegral ℤ (x i)) → (N : E) • x ∈ Γ)
    (hup : ∀ x ∈ Γ, ∀ i, IsIntegral ℤ ((N : E) * x i)) : Submodule.IsLattice E Γ := by
  have hNE : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN
  let f : (Fin n → 𝓞 E) →ₗ[𝓞 E] (Fin n → E) :=
    ((N : E)⁻¹ • (LinearMap.pi fun i => (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj i)))
  have hle : Γ ≤ LinearMap.range f := by
    intro x hx
    refine ⟨fun i => ⟨(N : E) * x i, hup x hx i⟩, ?_⟩
    ext i
    change (N : E)⁻¹ * ((N : E) * x i) = x i
    rw [← mul_assoc, inv_mul_cancel₀ hNE, one_mul]
  refine ⟨?_, ?_⟩
  · rw [← Submodule.map_comap_eq_self hle]
    exact (IsNoetherian.noetherian _).map f
  · rw [eq_top_iff]
    intro y _
    rw [pi_eq_sum_univ y]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have hmem : (N : E) • (fun j => if i = j then (1 : E) else 0) ∈ Γ := by
      apply hlow
      intro j
      split_ifs
      · exact isIntegral_one
      · exact isIntegral_zero
    have : (fun j => if i = j then (1 : E) else 0) = (N : E)⁻¹ • ((N : E) • (fun j => if i = j then (1 : E) else 0)) := by
      rw [smul_smul, inv_mul_cancel₀ hNE, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
