import Mathlib

universe u_1 u_2

namespace GlobalTheory.TranslateSum

/- English proof (translation)
Introduce `h hh`. Establish `hex : ∀ s ∈ S, ∃ t : G, t ∈ S ∧ t⁻¹ * (h * s) ∈ V` using `fun s hs => (huniq (h * s) (H.mul_mem hh (hS s hs))).exists`. Use `choose φ hφS hφV using hex`. Use `Finset.sum_bij φ hφS ?_ ?_ ?_` and prove the remaining obligations. Introduce `s hs t ht hst`.

Establish `h1 : s⁻¹ * t ∈ V`. Use `V.mul_mem (V.inv_mem (hφV s hs)) (hφV t ht)` as an intermediate fact. Rewrite `this` using `[hst]`. Establish `e : ((φ t ht)⁻¹ * (h * s))⁻¹ * ((φ t ht)⁻¹ * (h * t)) = s⁻¹ * t` using `by group`. Rewrite `this` using `[e]`. Then use the resulting hypothesis.

Establish `h2 : t⁻¹ * t ∈ V`. Rewrite using `[inv_mul_cancel]`. Conclude with `V.one_mem`. Conclude with `(huniq t (hS t ht)).unique ⟨hs, h1⟩ ⟨ht, h2⟩`. Introduce `u hu`.

Take `⟨s, hs, hsV⟩` from `(huniq (h⁻¹ * u) (H.mul_mem (H.inv_mem hh) (hS u hu))).exists`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Establish `h1 : u⁻¹ * (h * s) ∈ V`. Use `V.inv_mem hsV` as an intermediate fact. Establish `e : (s⁻¹ * (h⁻¹ * u))⁻¹ = u⁻¹ * (h * s)` using `by group`.

Rewrite `this` using `[e]`. Then use the resulting hypothesis. Conclude with `(huniq (h * s) (H.mul_mem hh (hS s hs))).unique ⟨hφS s hs, hφV s hs⟩ ⟨hu, h1⟩`. Introduce `s hs`. Establish `hm : (φ s hs)⁻¹ * (h * s) ∈ H` using `H.mul_mem (H.inv_mem (hS _ (hφS s hs))) (H.mul_mem hh (hS s hs))`. Use `hf (φ s hs) _ hm (hφV s hs)` as an intermediate fact.

Rewrite `this` using `[mul_inv_cancel_left]`. Then use the resulting hypothesis.
-/
theorem sum_translate_eq {G : Type u_1} {M : Type u_2} [Group G] [AddCommMonoid M]
    (H V : Subgroup G) (S : Finset G) (hS : ∀ s ∈ S, s ∈ H)
    (huniq : ∀ h ∈ H, ∃! s : G, s ∈ S ∧ s⁻¹ * h ∈ V) (f : G → M)
    (hf : ∀ (g v : G), v ∈ H → v ∈ V → f (g * v) = f g) :
    ∀ h ∈ H, ∑ s ∈ S, f (h * s) = ∑ s ∈ S, f s := by
  intro h hh
  have hex : ∀ s ∈ S, ∃ t : G, t ∈ S ∧ t⁻¹ * (h * s) ∈ V := fun s hs =>
    (huniq (h * s) (H.mul_mem hh (hS s hs))).exists
  choose φ hφS hφV using hex
  refine Finset.sum_bij φ hφS ?_ ?_ ?_
  · intro s hs t ht hst
    have h1 : s⁻¹ * t ∈ V := by
      have := V.mul_mem (V.inv_mem (hφV s hs)) (hφV t ht)
      rw [hst] at this
      have e : ((φ t ht)⁻¹ * (h * s))⁻¹ * ((φ t ht)⁻¹ * (h * t)) = s⁻¹ * t := by group
      rwa [e] at this
    have h2 : t⁻¹ * t ∈ V := by
      rw [inv_mul_cancel]; exact V.one_mem
    exact (huniq t (hS t ht)).unique ⟨hs, h1⟩ ⟨ht, h2⟩
  · intro u hu
    obtain ⟨s, hs, hsV⟩ := (huniq (h⁻¹ * u) (H.mul_mem (H.inv_mem hh) (hS u hu))).exists
    refine ⟨s, hs, ?_⟩
    have h1 : u⁻¹ * (h * s) ∈ V := by
      have := V.inv_mem hsV
      have e : (s⁻¹ * (h⁻¹ * u))⁻¹ = u⁻¹ * (h * s) := by group
      rwa [e] at this
    exact (huniq (h * s) (H.mul_mem hh (hS s hs))).unique ⟨hφS s hs, hφV s hs⟩ ⟨hu, h1⟩
  · intro s hs
    have hm : (φ s hs)⁻¹ * (h * s) ∈ H :=
      H.mul_mem (H.inv_mem (hS _ (hφS s hs))) (H.mul_mem hh (hS s hs))
    have := hf (φ s hs) _ hm (hφV s hs)
    rwa [mul_inv_cancel_left] at this

end GlobalTheory.TranslateSum
