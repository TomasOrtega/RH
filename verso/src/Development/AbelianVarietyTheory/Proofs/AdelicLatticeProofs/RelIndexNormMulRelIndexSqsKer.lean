import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

/- English proof (translation)
Introduce `A _ σ hσ h90`. Use `set N : A →* A := MonoidHom.id A * σ with hN`. Use `set B : Subgroup A := σ.eqLocus (MonoidHom.id A) with hB`. Set `f : A →* A` to `MonoidHom.id A / σ`. Establish `hNa : ∀ a, N a = a * σ a` using `fun a => rfl`.

Establish `hfa : ∀ a, f a = a / σ a` using `fun a => rfl`. Establish `hBa : ∀ a, a ∈ B ↔ σ a = a` using `fun a => Iff.rfl`. Establish `hK : ∀ a, a ∈ N.ker ↔ a * σ a = 1` using `fun a => Iff.rfl`. Establish `hsq : ∀ (U : Subgroup A) (a : A), a ∈ sqs U ↔ ∃ b ∈ U, b ^ 2 = a` using `fun U a => Iff.rfl`. Establish `h1 : sqs B ≤ N.range`.

Introduce `a ha`. Take `⟨b, hb, rfl⟩` from `(hsq _ _).1 ha`. Conclude with `⟨b, by rw [hNa, (hBa b).1 hb, sq]⟩`. Establish `h2 : N.range ≤ B`. Introduce and unpack `_ ⟨a, rfl⟩`.

Rewrite using `[hBa, hNa, map_mul, hσ, mul_comm]`. Establish `h3 : f.range = N.ker`. Use extensionality with `a`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, rfl⟩`.

Rewrite using `[hK, hfa, map_div, hσ]`. Simplify using the standard rewrite rules. Introduce `ha`. Take `⟨b, hb⟩` from `h90 a ((hK a).1 ha)`. Conclude with `⟨b, hb.symm⟩`.

Establish `h4 : (sqs B).comap N = (sqs N.ker).comap f`. Use extensionality with `a`. Rewrite using `[Subgroup.mem_comap, Subgroup.mem_comap, hsq, hsq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb, hab⟩`.

Rewrite `hb` using `[hBa]`. Rewrite `hab` using `[hNa]`. Use `⟨a / b, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hK, map_div, hb, div_mul_div_comm, ← hab, sq, div_self']`. Rewrite using `[hfa, div_pow, hab, sq, mul_div_mul_left_eq_div]`.

Introduce and unpack `⟨c, hc, hac⟩`. Rewrite `hc` using `[hK]`. Rewrite `hac` using `[hfa]`. Establish `hc' : σ c = c⁻¹` using `eq_inv_of_mul_eq_one_right hc`. Establish `ha' : σ a = a / c ^ 2` using `by rw [hac]; simp`.

Use `⟨a / c, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hBa, map_div, hc', ha', sq, div_inv_eq_mul, div_mul_eq_div_div, div_mul_cancel]`. Rewrite using `[hNa, ha', div_pow, sq a, mul_div_assoc]`. Establish `h5 : (sqs B).relIndex N.range = (sqs N.ker).relIndex N.ker`. Rewrite using `[← Subgroup.index_comap, h4, Subgroup.index_comap, h3]`.

Rewrite using `[← h5, mul_comm]`. Conclude with `Subgroup.relIndex_mul_relIndex _ _ _ h1 h2`.
-/
theorem relIndex_norm_mul_relIndex_sqs_ker :
    ∀ (A : Type) [CommGroup A] (σ : A →* A), (∀ a, σ (σ a) = a) → (∀ a, a * σ a = 1 → ∃ b, a = b / σ b) → (MonoidHom.id A * σ).range.relIndex (σ.eqLocus (MonoidHom.id A)) * (sqs (MonoidHom.id A * σ).ker).relIndex (MonoidHom.id A * σ).ker = (sqs (σ.eqLocus (MonoidHom.id A))).relIndex (σ.eqLocus (MonoidHom.id A)) := by
  intro A _ σ hσ h90
  set N : A →* A := MonoidHom.id A * σ with hN
  set B : Subgroup A := σ.eqLocus (MonoidHom.id A) with hB
  let f : A →* A := MonoidHom.id A / σ
  have hNa : ∀ a, N a = a * σ a := fun a => rfl
  have hfa : ∀ a, f a = a / σ a := fun a => rfl
  have hBa : ∀ a, a ∈ B ↔ σ a = a := fun a => Iff.rfl
  have hK : ∀ a, a ∈ N.ker ↔ a * σ a = 1 := fun a => Iff.rfl
  have hsq : ∀ (U : Subgroup A) (a : A), a ∈ sqs U ↔ ∃ b ∈ U, b ^ 2 = a := fun U a => Iff.rfl
  have h1 : sqs B ≤ N.range := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := (hsq _ _).1 ha
    exact ⟨b, by rw [hNa, (hBa b).1 hb, sq]⟩
  have h2 : N.range ≤ B := by
    rintro _ ⟨a, rfl⟩
    rw [hBa, hNa, map_mul, hσ, mul_comm]
  have h3 : f.range = N.ker := by
    ext a
    constructor
    · rintro ⟨b, rfl⟩
      rw [hK, hfa, map_div, hσ]
      simp
    · intro ha
      obtain ⟨b, hb⟩ := h90 a ((hK a).1 ha)
      exact ⟨b, hb.symm⟩
  have h4 : (sqs B).comap N = (sqs N.ker).comap f := by
    ext a
    rw [Subgroup.mem_comap, Subgroup.mem_comap, hsq, hsq]
    constructor
    · rintro ⟨b, hb, hab⟩
      rw [hBa] at hb
      rw [hNa] at hab
      refine ⟨a / b, ?_, ?_⟩
      · rw [hK, map_div, hb, div_mul_div_comm, ← hab, sq, div_self']
      · rw [hfa, div_pow, hab, sq, mul_div_mul_left_eq_div]
    · rintro ⟨c, hc, hac⟩
      rw [hK] at hc
      rw [hfa] at hac
      have hc' : σ c = c⁻¹ := eq_inv_of_mul_eq_one_right hc
      have ha' : σ a = a / c ^ 2 := by rw [hac]; simp
      refine ⟨a / c, ?_, ?_⟩
      · rw [hBa, map_div, hc', ha', sq, div_inv_eq_mul, div_mul_eq_div_div, div_mul_cancel]
      · rw [hNa, ha', div_pow, sq a, mul_div_assoc]
  have h5 : (sqs B).relIndex N.range = (sqs N.ker).relIndex N.ker := by
    rw [← Subgroup.index_comap, h4, Subgroup.index_comap, h3]
  rw [← h5, mul_comm]
  exact Subgroup.relIndex_mul_relIndex _ _ _ h1 h2

end GlobalTheory.QNorm
