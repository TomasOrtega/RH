import Mathlib

open NumberField IsDedekindDomain

namespace Bl.SecondBlockLemmaE

variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

/- English proof (translation)
Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Λ.zero_mem⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨d₁, hd₁, h₁⟩` from `hx`.

Take `⟨d₂, hd₂, h₂⟩` from `hy`. Use `⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩` and prove the remaining obligations. Establish `e1 : (d₁ * d₂) • x = d₂ • (d₁ • x)` using `by rw [mul_comm, mul_smul]`. Establish `e2 : (d₁ * d₂) • y = d₁ • (d₂ • y)` using `by rw [mul_smul]`. Rewrite using `[smul_add, e1, e2]`.

Conclude with `Λ.add_mem (Λ.smul_mem _ h₁) (Λ.smul_mem _ h₂)`. Consider the case `smul a x _ hx`. Take `⟨d, hd, h⟩` from `hx`. Take `⟨⟨n, m⟩, hnm⟩` from `IsLocalization.surj (nonZeroDivisors (𝓞 E)) a`. Use `⟨(m : 𝓞 E) * d, mul_ne_zero (nonZeroDivisors.ne_zero m.2) hd, ?_⟩` and prove the remaining obligations.

Establish `key : (m : 𝓞 E) • (a • x) = n • x`. Rewrite using `[← smul_assoc, Algebra.smul_def, mul_comm]`. Rewrite using `[hnm, algebraMap_smul]`. Rewrite using `[mul_comm, mul_smul, key, smul_comm d n x]`. Conclude with `Λ.smul_mem _ h`.
-/
theorem goal1 {Λ : Submodule (𝓞 E) V} {v : V}
    (hv : v ∈ Submodule.span E (Λ : Set V)) : ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ Λ := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Λ.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    have e1 : (d₁ * d₂) • x = d₂ • (d₁ • x) := by rw [mul_comm, mul_smul]
    have e2 : (d₁ * d₂) • y = d₁ • (d₂ • y) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact Λ.add_mem (Λ.smul_mem _ h₁) (Λ.smul_mem _ h₂)
  | smul a x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨⟨n, m⟩, hnm⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 E)) a
    refine ⟨(m : 𝓞 E) * d, mul_ne_zero (nonZeroDivisors.ne_zero m.2) hd, ?_⟩
    have key : (m : 𝓞 E) • (a • x) = n • x := by
      rw [← smul_assoc, Algebra.smul_def, mul_comm]
      rw [hnm, algebraMap_smul]
    rw [mul_comm, mul_smul, key, smul_comm d n x]
    exact Λ.smul_mem _ h

end Bl.SecondBlockLemmaE
