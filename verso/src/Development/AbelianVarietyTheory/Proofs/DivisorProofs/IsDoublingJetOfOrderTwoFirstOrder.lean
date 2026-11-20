import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivCompM

open GlobalTheory.Nef

namespace GlobalTheory.Nef.PathJet

open PowerSeries

/- English proof (translation)
Introduce `A B R _ _ _ π ε m β δ hεπ hmπ hεm hm2 hδ hδπ`. Establish `hεπ' : ∀ b, ε (π b) = b` using `fun b => by rw [← RingHom.comp_apply, hεπ, RingHom.id_apply]`. Establish `hεm' : ∀ f, ε (m f) = ε f` using `fun f => by rw [← RingHom.comp_apply, hεm]`. Establish `hδ1 : δ 1 = 0`. Establish `h` using `hδ 1 1`.

Simplify using `only [mul_one, map_one, one_mul] at h`. Establish `: δ 1 + δ 1 = δ 1 + 0` using `by rw [add_zero]; exact h.symm`. Conclude with `add_left_cancel this`. Establish `hdm : ∀ f, δ (m f) = 2 * δ f` using `deriv_comp_m π ε m β δ hεπ hmπ hm2 hδ hδπ`. Use `⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `f g`. Use `⟨C (-(δ f * δ g)), ?_⟩` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[hδ, map_mul, map_mul]`. Simplify using `only [map_add, map_mul, map_neg]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `f g`. Simplify using `[map_add]`. Conclude with `⟨0, by ring⟩`. Simplify using `[hδ1]`.

Introduce `b`. Simplify using `[hεπ', hδπ]`. Introduce `f`. Use `⟨0, ?_⟩` and prove the remaining obligations. Use `beta_reduce`.

Rewrite using `[hεm', hdm]`. Establish `hrC : ∀ x : R, rescale (2 : R) (C x) = C x`. Apply the tactic sequence `intro x; ext n; rw [coeff_rescale, coeff_C]; split_ifs with h <;> simp [h]`. Simplify using `only [map_add, map_mul, rescale_X, hrC]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `f`. Simplify using the standard rewrite rules. Introduce `f`. Simplify using `[coeff_C, coeff_C_mul, coeff_X]`.
-/
theorem firstOrder_isJet : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R), ε.comp π = RingHom.id B → m.comp π = π → ε.comp m = ε → (∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2) → (∀ f g, δ (f * g) = β (ε f) * δ g + β (ε g) * δ f) → (∀ a, δ (π a) = 0) → GlobalTheory.Nef.PathJet.IsJet π ε m β δ 2 (fun f => PowerSeries.C (β (ε f)) + PowerSeries.C (δ f) * PowerSeries.X) := by
  intro A B R _ _ _ π ε m β δ hεπ hmπ hεm hm2 hδ hδπ
  have hεπ' : ∀ b, ε (π b) = b := fun b => by rw [← RingHom.comp_apply, hεπ, RingHom.id_apply]
  have hεm' : ∀ f, ε (m f) = ε f := fun f => by rw [← RingHom.comp_apply, hεm]
  have hδ1 : δ 1 = 0 := by
    have h := hδ 1 1
    simp only [mul_one, map_one, one_mul] at h
    have : δ 1 + δ 1 = δ 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel this
  have hdm : ∀ f, δ (m f) = 2 * δ f :=
    deriv_comp_m π ε m β δ hεπ hmπ hm2 hδ hδπ
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro f g
    refine ⟨C (-(δ f * δ g)), ?_⟩
    beta_reduce
    rw [hδ, map_mul, map_mul]
    simp only [map_add, map_mul, map_neg]
    ring
  · intro f g
    simp [map_add]
    exact ⟨0, by ring⟩
  · simp [hδ1]
  · intro b
    simp [hεπ', hδπ]
  · intro f
    refine ⟨0, ?_⟩
    beta_reduce
    rw [hεm', hdm]
    have hrC : ∀ x : R, rescale (2 : R) (C x) = C x := by
      intro x; ext n; rw [coeff_rescale, coeff_C]; split_ifs with h <;> simp [h]
    simp only [map_add, map_mul, rescale_X, hrC]
    ring
  · intro f
    simp
  · intro f
    simp [coeff_C, coeff_C_mul, coeff_X]

end GlobalTheory.Nef.PathJet
