import Mathlib

noncomputable section

open NumberField

namespace PI.VolStabS

def ChInf : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Λ : Submodule (𝓞 F) F), (∃ c : F, c ≠ 0 ∧ c ∈ Λ) →
    (∀ c : F, c ≠ 0 → ¬ ∀ a ∈ Λ, ∃ r : 𝓞 F, a = c * r) →
    ∀ χ : AddChar (InfiniteAdeleRing F) ℂ, Continuous χ →
    (∀ a ∈ Λ, χ (algebraMap F (InfiniteAdeleRing F) a) = 1) → ∀ x, χ x = 1

def ChLift : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : AddChar (InfiniteAdeleRing F) ℂ), Continuous χ →
    ∃ ℓ : InfiniteAdeleRing F →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = Complex.exp (ℓ x)

def AddIntF : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Λ : Submodule (𝓞 F) F), (∃ c : F, c ≠ 0 ∧ c ∈ Λ) →
    (∀ c : F, c ≠ 0 → ¬ ∀ a ∈ Λ, ∃ r : 𝓞 F, a = c * r) →
    ∀ g : F →+ ℂ, (∀ a ∈ Λ, ∃ n : ℤ, g a = n) → ∀ a, g a = 0

/- English proof (translation)
Introduce `F _ _ Λ hne hnot χ hχ hΛ x`. Take `⟨ℓ, hℓc, hℓ⟩` from `hL F χ hχ`. Establish `h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0`. Simplify using `[Real.pi_ne_zero, Complex.I_ne_zero]`. Set `g : F →+ ℂ` to `(AddMonoidHom.mulLeft (2 * (Real.pi : ℂ) * Complex.I)⁻¹).comp (ℓ.comp (algebraMap F (InfiniteAdeleRing F)).toAddMonoidHom)`.

Establish `hgv : ∀ a, g a = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ℓ (algebraMap F _ a)` using `fun a => rfl`. Establish `hgint : ∀ a ∈ Λ, ∃ n : ℤ, g a = n`. Introduce `a ha`. Establish `h1` using `hΛ a ha`. Rewrite `h1` using `[hℓ, Complex.exp_eq_one_iff]`.

Take `⟨n, hn⟩` from `h1`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[hgv, hn, inv_mul_eq_iff_eq_mul₀ h2, mul_comm]`. Establish `hg0` using `hA F Λ hne hnot g hgint`. Establish `hℓ0 : ∀ a : F, ℓ (algebraMap F (InfiniteAdeleRing F) a) = 0`.

Introduce `a`. Establish `h3` using `hg0 a`. Rewrite `h3` using `[hgv]`. Conclude with `(mul_eq_zero.mp h3).resolve_left (inv_ne_zero h2)`. Establish `hfun : (ℓ : InfiniteAdeleRing F → ℂ) = fun _ => 0` using `(InfiniteAdeleRing.denseRange_algebraMap F).equalizer hℓc continuous_const (funext fun a => hℓ0 a)`.

Rewrite using `[hℓ, congrFun hfun x, Complex.exp_zero]`.
-/
theorem chInf_of (hL : ChLift) (hA : AddIntF) : ChInf := by
  intro F _ _ Λ hne hnot χ hχ hΛ x
  obtain ⟨ℓ, hℓc, hℓ⟩ := hL F χ hχ
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]

  let g : F →+ ℂ := (AddMonoidHom.mulLeft (2 * (Real.pi : ℂ) * Complex.I)⁻¹).comp
    (ℓ.comp (algebraMap F (InfiniteAdeleRing F)).toAddMonoidHom)
  have hgv : ∀ a, g a = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ℓ (algebraMap F _ a) := fun a => rfl
  have hgint : ∀ a ∈ Λ, ∃ n : ℤ, g a = n := by
    intro a ha
    have h1 := hΛ a ha
    rw [hℓ, Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    refine ⟨n, ?_⟩
    rw [hgv, hn, inv_mul_eq_iff_eq_mul₀ h2, mul_comm]
  have hg0 := hA F Λ hne hnot g hgint
  have hℓ0 : ∀ a : F, ℓ (algebraMap F (InfiniteAdeleRing F) a) = 0 := by
    intro a
    have h3 := hg0 a
    rw [hgv] at h3
    exact (mul_eq_zero.mp h3).resolve_left (inv_ne_zero h2)

  have hfun : (ℓ : InfiniteAdeleRing F → ℂ) = fun _ => 0 :=
    (InfiniteAdeleRing.denseRange_algebraMap F).equalizer hℓc continuous_const
      (funext fun a => hℓ0 a)
  rw [hℓ, congrFun hfun x, Complex.exp_zero]

end PI.VolStabS
