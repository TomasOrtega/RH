import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.JugendtraumUniformization
import GroundTheory.GlobalFields.ComplexMultiplication.MainTheoremIdeles
import GroundTheory.GlobalFields.ComplexMultiplication.HilbertClassField
import GroundTheory.GlobalFields.ComplexMultiplication.AutCFixed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global
namespace Elliptic

noncomputable section

open NumberField Module IsDedekindDomain IntermediateField IdeleGroup WeierstrassCurve GroundTheory.Arith.Abelian
open GroundTheory.LocalField (restrictAb le_maximalAbelianExtension maximalAbelianExtension)
open scoped nonZeroDivisors

section Fixed

variable {K : Type*} [Field K] [Algebra K ℂ]

/- English proof (translation)
Establish `hle : IntermediateField.adjoin K S ≤ fixedField (Subgroup.zpowers σ)`. Rewrite using `[adjoin_le_iff]`. Introduce `x hx`. Rewrite using `[SetLike.mem_coe, mem_fixedField_iff]`. Establish `hst : σ ∈ MulAction.stabilizer (ℂ ≃ₐ[K] ℂ) x` using `h x hx`.

Introduce `f hf`. Conclude with `(Subgroup.zpowers_le.2 hst) hf`. Introduce `x hx`. Conclude with `(mem_fixedField_iff _ _).1 (hle hx) σ (Subgroup.mem_zpowers σ)`.
-/
theorem forall_adjoin_apply_eq (σ : ℂ ≃ₐ[K] ℂ) {S : Set ℂ} (h : ∀ x ∈ S, σ x = x) :
    ∀ x ∈ IntermediateField.adjoin K S, σ x = x := by
  have hle : IntermediateField.adjoin K S ≤ fixedField (Subgroup.zpowers σ) := by
    rw [adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, mem_fixedField_iff]
    have hst : σ ∈ MulAction.stabilizer (ℂ ≃ₐ[K] ℂ) x := h x hx
    intro f hf
    exact (Subgroup.zpowers_le.2 hst) hf
  intro x hx
  exact (mem_fixedField_iff _ _).1 (hle hx) σ (Subgroup.mem_zpowers σ)

/- English proof (translation)
Introduce `x hx`. Establish `hx' : x ∈ (⊥ : IntermediateField F₂ ℂ)`. Rewrite using `[mem_bot_iff_forall_algEquiv_apply_eq]`. Introduce `τ`. Conclude with `h (τ.restrictScalars K) (fun y hy ↦ τ.commutes ⟨y, hy⟩) x hx`.

Take `⟨a, rfl⟩` from `IntermediateField.mem_bot.1 hx'`. Conclude with `a.2`.
-/
theorem le_of_forall_algEquiv {F₁ F₂ : IntermediateField K ℂ}
    (h : ∀ σ : ℂ ≃ₐ[K] ℂ, (∀ x ∈ F₂, σ x = x) → ∀ x ∈ F₁, σ x = x) : F₁ ≤ F₂ := by
  intro x hx
  have hx' : x ∈ (⊥ : IntermediateField F₂ ℂ) := by
    rw [mem_bot_iff_forall_algEquiv_apply_eq]
    intro τ
    exact h (τ.restrictScalars K) (fun y hy ↦ τ.commutes ⟨y, hy⟩) x hx
  obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.1 hx'
  exact a.2

/- English proof (translation)
The claim follows from `le_antisymm (le_of_forall_algEquiv fun σ hσ ↦ (h σ).2 hσ) (le_of_forall_algEquiv fun σ hσ ↦ (h σ).1 hσ)`.
-/
theorem eq_of_forall_algEquiv {F₁ F₂ : IntermediateField K ℂ}
    (h : ∀ σ : ℂ ≃ₐ[K] ℂ, (∀ x ∈ F₁, σ x = x) ↔ (∀ x ∈ F₂, σ x = x)) : F₁ = F₂ :=
  le_antisymm (le_of_forall_algEquiv fun σ hσ ↦ (h σ).2 hσ)
    (le_of_forall_algEquiv fun σ hσ ↦ (h σ).1 hσ)

end Fixed

section Artin

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]

/- English proof (translation)
Use `set Ω := algebraicClosure K ℂ`. Use `set M := maximalAbelianExtension K Ω`. Set `σΩ : Ω ≃ₐ[K] Ω` to `σ.restrictNormal Ω`. Take `⟨c, hc⟩` from `artinMap_surjective (K := K) (Ω := Ω) (σΩ.restrictNormal M)`. Take `⟨s, rfl⟩` from `IdeleClassGroup.mk_surjective K c`.

Use `⟨s, fun x ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[hc]`. Establish `h1 : ((σΩ.restrictNormal M x : M) : Ω) = σΩ (x : Ω)` using `AlgEquiv.restrictNormal_commutes σΩ M x`. Rewrite using `[h1]`. Conclude with `AlgEquiv.restrictNormal_commutes σ Ω (x : Ω)`.
-/
theorem exists_idele_artinMap_eq (σ : ℂ ≃ₐ[K] ℂ) :
    ∃ s : IdeleGroup K, ∀ x : maximalAbelianExtension K (algebraicClosure K ℂ),
      ((artinMap K (algebraicClosure K ℂ) (IdeleClassGroup.mk K s) x : algebraicClosure K ℂ) : ℂ) =
        σ ((x : algebraicClosure K ℂ) : ℂ) := by
  set Ω := algebraicClosure K ℂ
  set M := maximalAbelianExtension K Ω
  let σΩ : Ω ≃ₐ[K] Ω := σ.restrictNormal Ω
  obtain ⟨c, hc⟩ := artinMap_surjective (K := K) (Ω := Ω) (σΩ.restrictNormal M)
  obtain ⟨s, rfl⟩ := IdeleClassGroup.mk_surjective K c
  refine ⟨s, fun x ↦ ?_⟩
  rw [hc]
  have h1 : ((σΩ.restrictNormal M x : M) : Ω) = σΩ (x : Ω) :=
    AlgEquiv.restrictNormal_commutes σΩ M x
  rw [h1]
  exact AlgEquiv.restrictNormal_commutes σ Ω (x : Ω)

/- English proof (translation)
Use `set M := 𝔪.rayClassField ℂ`. Rewrite using `[← 𝔪.range_ideleClassNorm_rayClassField ℂ, ← ker_reciprocityMap, MonoidHom.mem_ker, reciprocityMap_mk]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `AlgEquiv.ext fun z ↦ Subtype.ext ?_` and prove the remaining obligations.

Rewrite using `[ideleSymbol_apply_eq_of_artinMap σ s hs M z]`. Conclude with `h z z.2`. Introduce `h x hx`. Establish `e` using `ideleSymbol_apply_eq_of_artinMap σ s hs M ⟨x, hx⟩`. Rewrite `e` using `[h]`.

Conclude with `e.symm`.
-/
theorem forall_rayClassField_apply_eq_iff (σ : ℂ ≃ₐ[K] ℂ) (s : IdeleGroup K)
    (hs : ∀ x : maximalAbelianExtension K (algebraicClosure K ℂ),
      ((artinMap K (algebraicClosure K ℂ) (IdeleClassGroup.mk K s) x : algebraicClosure K ℂ) : ℂ) =
        σ ((x : algebraicClosure K ℂ) : ℂ))
    (𝔪 : Modulus K) :
    (∀ x ∈ 𝔪.rayClassField ℂ, σ x = x) ↔
      IdeleClassGroup.mk K s ∈ 𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K) := by
  set M := 𝔪.rayClassField ℂ
  rw [← 𝔪.range_ideleClassNorm_rayClassField ℂ, ← ker_reciprocityMap, MonoidHom.mem_ker,
    reciprocityMap_mk]
  constructor
  · intro h
    refine AlgEquiv.ext fun z ↦ Subtype.ext ?_
    rw [ideleSymbol_apply_eq_of_artinMap σ s hs M z]
    exact h z z.2
  · intro h x hx
    have e := ideleSymbol_apply_eq_of_artinMap σ s hs M ⟨x, hx⟩
    rw [h] at e
    exact e.symm

end Artin

section Hilbert

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [IsTotallyComplex K]

include hK in

/- English proof (translation)
Rewrite `hf` using `[← lattice_idealPeriodPair (algebraMap K ℂ) hK 𝔞]`. Conclude with `j_eq_of_isAnalyticUniformization hf (isAnalyticUniformization_toPointHom (idealPeriodPair (algebraMap K ℂ) hK 𝔞))`.
-/
theorem j_weierstrassCurve_idealPeriodPair_eq (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {E : WeierstrassCurve ℂ} [E.IsElliptic] {f : ℂ →+ E.toAffine.Point}
    (hf : IsAnalyticUniformization (idealLattice (algebraMap K ℂ) 𝔞) f) :
    (weierstrassCurve (idealPeriodPair (algebraMap K ℂ) hK 𝔞)).j = E.j := by
  rw [← lattice_idealPeriodPair (algebraMap K ℂ) hK 𝔞] at hf
  exact j_eq_of_isAnalyticUniformization hf
    (isAnalyticUniformization_toPointHom (idealPeriodPair (algebraMap K ℂ) hK 𝔞))

include hK in

/- English proof (translation)
Rewrite using `[← j_weierstrassCurve_idealPeriodPair_eq hK 𝔞 hf]`. Conclude with `adjoin_j_eq_hilbertClassField hK (ellOf (algebraMap K ℂ) _ (latticeEnd_idealPeriodPair (algebraMap K ℂ) hK 𝔞))`.
-/
theorem adjoin_j_eq_hilbertClassField_of_isAnalyticUniformization (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {E : WeierstrassCurve ℂ} [E.IsElliptic] {f : ℂ →+ E.toAffine.Point}
    (hf : IsAnalyticUniformization (idealLattice (algebraMap K ℂ) 𝔞) f) :
    K⟮E.j⟯ = hilbertClassField K ℂ := by
  rw [← j_weierstrassCurve_idealPeriodPair_eq hK 𝔞 hf]
  exact adjoin_j_eq_hilbertClassField hK
    (ellOf (algebraMap K ℂ) _ (latticeEnd_idealPeriodPair (algebraMap K ℂ) hK 𝔞))

include hK in

/- English proof (translation)
Establish `hfix : ∀ x ∈ (Modulus.one : Modulus K).rayClassField ℂ, σ x = x`. Introduce `x hx`. Establish `hx' : x ∈ K⟮E.j⟯`. Rewrite using `[adjoin_j_eq_hilbertClassField_of_isAnalyticUniformization hK 𝔞 hf]`. Conclude with `hx`.

Conclude with `forall_adjoin_apply_eq σ (fun y hy ↦ by rw [Set.mem_singleton_iff.1 hy]; exact hj) x hx'`. Rewrite using `[← Modulus.congruenceSubgroup_one]`. Conclude with `(forall_rayClassField_apply_eq_iff σ s hs Modulus.one).1 hfix`.
-/
theorem mk_mem_map_standardOpenSubgroup_of_apply_j_eq (σ : ℂ ≃ₐ[K] ℂ) (s : IdeleGroup K)
    (hs : ∀ x : maximalAbelianExtension K (algebraicClosure K ℂ),
      ((artinMap K (algebraicClosure K ℂ) (IdeleClassGroup.mk K s) x : algebraicClosure K ℂ) : ℂ) =
        σ ((x : algebraicClosure K ℂ) : ℂ))
    (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {E : WeierstrassCurve ℂ} [E.IsElliptic]
    {f : ℂ →+ E.toAffine.Point} (hf : IsAnalyticUniformization (idealLattice (algebraMap K ℂ) 𝔞) f)
    (hj : σ E.j = E.j) :
    IdeleClassGroup.mk K s ∈ (standardOpenSubgroup K).map (IdeleClassGroup.mk K) := by
  have hfix : ∀ x ∈ (Modulus.one : Modulus K).rayClassField ℂ, σ x = x := by
    intro x hx
    have hx' : x ∈ K⟮E.j⟯ := by
      rw [adjoin_j_eq_hilbertClassField_of_isAnalyticUniformization hK 𝔞 hf]
      exact hx
    exact forall_adjoin_apply_eq σ (fun y hy ↦ by rw [Set.mem_singleton_iff.1 hy]; exact hj) x hx'
  rw [← Modulus.congruenceSubgroup_one]
  exact (forall_rayClassField_apply_eq_iff σ s hs Modulus.one).1 hfix

end Hilbert

end

end Elliptic
end GroundTheory.Global
