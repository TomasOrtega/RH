import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MapWopWmap

open Module
universe u v

namespace UpperTheory.Gal.CertificateRingHomMap

open GlobalTheory.LKDef.HeckeTraceForms

section
variable {Γ H A V : Type} [Group Γ] [Group H] [Group A] [AddCommGroup V] [Module ℂ V]
  {ι : Γ →* H} {K : Subgroup H} {ξ : Representation ℂ Γ V} {c : H →* A} {φ : H → V}

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hφ`. Use `set δ := γ'⁻¹ * γ with hδ`. Establish `hκ : k * k'⁻¹ ∈ K` using `K.mul_mem hk (K.inv_mem hk')`. Establish `hu'eq : u' = ι δ * u * (k * k'⁻¹)`. Establish `e1 : ι γ' * u' = ι γ * u * k * k'⁻¹`.

Rewrite using `[h]`. Use `group`. Rewrite using `[hδ, map_mul, map_inv]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e1]`.

Use `group`. Establish `hc : c (ι δ) * c (k * k'⁻¹) = 1`. Establish `e2` using `congrArg c hu'eq`. Rewrite `e2` using `[map_mul, map_mul, hu, hu', mul_one]`. Conclude with `e2.symm`.

Establish `hcκ : c (k * k'⁻¹) = 1`. Apply `h1 δ⁻¹ _ hκ` to reduce the goal to its premises. Rewrite using `[map_inv, map_inv, eq_inv_of_mul_eq_one_right hc]`. Establish `hcδ : c (ι δ) = 1`. Rewrite `hc` using `[hcκ, mul_one]`.

Conclude with `hc`. Rewrite using `[hu'eq, h3 _ hκ _ hcκ (by rw [map_mul, hcδ, hu, one_mul]), h2 δ u hcδ hu]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, hδ, mul_inv_cancel_left]`.
-/
private theorem key (hφ : KerForm ι K ξ c φ) {γ γ' : Γ} {u u' k k' : H} (hu : c u = 1) (hu' : c u' = 1)
    (hk : k ∈ K) (hk' : k' ∈ K) (h : ι γ * u * k = ι γ' * u' * k') : ξ γ (φ u) = ξ γ' (φ u') := by
  obtain ⟨h1, h2, h3⟩ := hφ
  set δ := γ'⁻¹ * γ with hδ
  have hκ : k * k'⁻¹ ∈ K := K.mul_mem hk (K.inv_mem hk')
  have hu'eq : u' = ι δ * u * (k * k'⁻¹) := by
    have e1 : ι γ' * u' = ι γ * u * k * k'⁻¹ := by
      rw [h]
      group
    rw [hδ, map_mul, map_inv]
    calc u' = (ι γ')⁻¹ * (ι γ' * u') := by group
      _ = (ι γ')⁻¹ * ι γ * u * (k * k'⁻¹) := by
        rw [e1]
        group
  have hc : c (ι δ) * c (k * k'⁻¹) = 1 := by
    have e2 := congrArg c hu'eq
    rw [map_mul, map_mul, hu, hu', mul_one] at e2
    exact e2.symm
  have hcκ : c (k * k'⁻¹) = 1 := by
    apply h1 δ⁻¹ _ hκ
    rw [map_inv, map_inv, eq_inv_of_mul_eq_one_right hc]
  have hcδ : c (ι δ) = 1 := by
    rw [hcκ, mul_one] at hc
    exact hc
  rw [hu'eq, h3 _ hκ _ hcκ (by rw [map_mul, hcδ, hu, one_mul]), h2 δ u hcδ hu]
  rw [← Module.End.mul_apply, ← map_mul, hδ, mul_inv_cancel_left]

open Classical in
private noncomputable def ext0 (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V) (c : H →* A) (φ : H → V) (g : H) : V :=
  if h : ∃ x : Γ × H × H, c x.2.1 = 1 ∧ x.2.2 ∈ K ∧ g = ι x.1 * x.2.1 * x.2.2 then
    ξ h.choose.1 (φ h.choose.2.1) else 0

/- English proof (translation)
Establish `h : ∃ x : Γ × H × H, c x.2.1 = 1 ∧ x.2.2 ∈ K ∧ ι γ * u * k = ι x.1 * x.2.1 * x.2.2` using `⟨(γ, u, k), hu, hk, rfl⟩`. Unfold `ext0`. Rewrite using `[dif_pos h]`. Take `⟨s1, s2, s3⟩` from `h.choose_spec`. Conclude with `key hφ s1 hu s2 hk s3.symm`.
-/
private theorem extension_by_zero_double_coset (hφ : KerForm ι K ξ c φ) {γ : Γ} {u k : H} (hu : c u = 1) (hk : k ∈ K) :
    ext0 ι K ξ c φ (ι γ * u * k) = ξ γ (φ u) := by
  have h : ∃ x : Γ × H × H, c x.2.1 = 1 ∧ x.2.2 ∈ K ∧ ι γ * u * k = ι x.1 * x.2.1 * x.2.2 :=
    ⟨(γ, u, k), hu, hk, rfl⟩
  unfold ext0
  rw [dif_pos h]
  obtain ⟨s1, s2, s3⟩ := h.choose_spec
  exact key hφ s1 hu s2 hk s3.symm

/- English proof (translation)
Unfold `ext0`. Rewrite using `[dif_neg]`. Introduce and unpack `⟨x, hx1, hx2, hx3⟩`. Conclude with `h ⟨x.1, x.2.1, x.2.2, hx1, hx2, hx3⟩`.
-/
private theorem extension_by_zero_outside_support {g : H} (h : ¬ ∃ γ u k, c u = 1 ∧ k ∈ K ∧ g = ι γ * u * k) :
    ext0 ι K ξ c φ g = 0 := by
  unfold ext0
  rw [dif_neg]
  rintro ⟨x, hx1, hx2, hx3⟩
  exact h ⟨x.1, x.2.1, x.2.2, hx1, hx2, hx3⟩

end

/- English proof (translation)
Introduce `Γ H A V _ _ _ _ _ ι K ξ c φ hφ`. Use `⟨ext0 ι K ξ c φ, ⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `γ g`. Distinguish the cases in `hg : ∃ γ₀ u k, c u = 1 ∧ k ∈ K ∧ g = ι γ₀ * u * k`. Take `⟨γ₀, u, k, hu, hk, rfl⟩` from `hg`.

Establish `e : ι γ * (ι γ₀ * u * k) = ι (γ * γ₀) * u * k` using `by rw [map_mul]; group`. Rewrite using `[e, extension_by_zero_double_coset hφ hu hk, extension_by_zero_double_coset hφ hu hk, map_mul]`. Both sides reduce to the same expression. Establish `hg' : ¬ ∃ γ₀ u k, c u = 1 ∧ k ∈ K ∧ ι γ * g = ι γ₀ * u * k`. Introduce and unpack `⟨γ₀, u, k, hu, hk, e⟩`.

Use `hg ⟨γ⁻¹ * γ₀, u, k, hu, hk, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_inv]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[extension_by_zero_outside_support hg, extension_by_zero_outside_support hg', map_zero]`. Introduce `k₁ hk₁ g`.

Distinguish the cases in `hg : ∃ γ₀ u k, c u = 1 ∧ k ∈ K ∧ g = ι γ₀ * u * k`. Take `⟨γ₀, u, k, hu, hk, rfl⟩` from `hg`. Establish `e : ι γ₀ * u * k * k₁ = ι γ₀ * u * (k * k₁)` using `by group`. Rewrite using `[e, extension_by_zero_double_coset hφ hu (K.mul_mem hk hk₁), extension_by_zero_double_coset hφ hu hk]`. Establish `hg' : ¬ ∃ γ₀ u k, c u = 1 ∧ k ∈ K ∧ g * k₁ = ι γ₀ * u * k`.

Introduce and unpack `⟨γ₀, u, k, hu, hk, e⟩`. Use `hg ⟨γ₀, u, k * k₁⁻¹, hu, K.mul_mem hk (K.inv_mem hk₁), ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[extension_by_zero_outside_support hg, extension_by_zero_outside_support hg']`. Introduce `u hu`.

Use `extension_by_zero_double_coset (γ := 1) hφ hu K.one_mem` as an intermediate fact. Simplify using `using this`. Introduce `g hg`. Assume the negation of the conclusion as `h`. Conclude with `hg (extension_by_zero_outside_support h)`.
-/
theorem pExtZero_holds : ExtZero := by
  intro Γ H A V _ _ _ _ _ ι K ξ c φ hφ
  refine ⟨ext0 ι K ξ c φ, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro γ g
    by_cases hg : ∃ γ₀ u k, c u = 1 ∧ k ∈ K ∧ g = ι γ₀ * u * k
    · obtain ⟨γ₀, u, k, hu, hk, rfl⟩ := hg
      have e : ι γ * (ι γ₀ * u * k) = ι (γ * γ₀) * u * k := by rw [map_mul]; group
      rw [e, extension_by_zero_double_coset hφ hu hk, extension_by_zero_double_coset hφ hu hk, map_mul]; rfl
    · have hg' : ¬ ∃ γ₀ u k, c u = 1 ∧ k ∈ K ∧ ι γ * g = ι γ₀ * u * k := by
        rintro ⟨γ₀, u, k, hu, hk, e⟩
        refine hg ⟨γ⁻¹ * γ₀, u, k, hu, hk, ?_⟩
        rw [map_mul, map_inv]
        calc g = (ι γ)⁻¹ * (ι γ * g) := by group
          _ = (ι γ)⁻¹ * ι γ₀ * u * k := by rw [e]; group
      rw [extension_by_zero_outside_support hg, extension_by_zero_outside_support hg', map_zero]
  · intro k₁ hk₁ g
    by_cases hg : ∃ γ₀ u k, c u = 1 ∧ k ∈ K ∧ g = ι γ₀ * u * k
    · obtain ⟨γ₀, u, k, hu, hk, rfl⟩ := hg
      have e : ι γ₀ * u * k * k₁ = ι γ₀ * u * (k * k₁) := by group
      rw [e, extension_by_zero_double_coset hφ hu (K.mul_mem hk hk₁), extension_by_zero_double_coset hφ hu hk]
    · have hg' : ¬ ∃ γ₀ u k, c u = 1 ∧ k ∈ K ∧ g * k₁ = ι γ₀ * u * k := by
        rintro ⟨γ₀, u, k, hu, hk, e⟩
        refine hg ⟨γ₀, u, k * k₁⁻¹, hu, K.mul_mem hk (K.inv_mem hk₁), ?_⟩
        calc g = g * k₁ * k₁⁻¹ := by group
          _ = ι γ₀ * u * (k * k₁⁻¹) := by rw [e]; group
      rw [extension_by_zero_outside_support hg, extension_by_zero_outside_support hg']
  · intro u hu
    have := extension_by_zero_double_coset (γ := 1) hφ hu K.one_mem
    simpa using this
  · intro g hg
    by_contra h
    exact hg (extension_by_zero_outside_support h)

end UpperTheory.Gal.CertificateRingHomMap
