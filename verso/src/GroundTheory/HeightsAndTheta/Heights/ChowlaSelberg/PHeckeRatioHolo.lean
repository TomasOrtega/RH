import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.HeckeRatioHolo
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm
open scoped Manifold

noncomputable section

namespace HeckeRatioHolo

/- English proof (translation)
Rewrite `hf`, the goal using `[UpperHalfPlane.mdifferentiable_iff]`. Establish `hmaps : Set.MapsTo (fun z : ℂ ↦ α * z + β) {z | 0 < z.im} {z | 0 < z.im}`. Introduce `z hz`. Establish `h` using `(m ⟨z, hz⟩).im_pos`. Rewrite `h` using `[UpperHalfPlane.im, hm]`.

Conclude with `h`. Use `(hf.comp (by fun_prop : DifferentiableOn ℂ (fun z : ℂ ↦ α * z + β) _) hmaps).congr ?_` and prove the remaining obligations. Introduce `z hz`. Establish `hmz : m (ofComplex z) = ofComplex (α * z + β)`. Apply `UpperHalfPlane.ext` to reduce the goal to its premises.

Rewrite using `[hm, ofComplex_apply_of_im_pos hz, ofComplex_apply_of_im_pos (hmaps hz)]`. Simplify using `only [Function.comp_apply, hmz]`.
-/
theorem mdifferentiable_comp_affine {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (m : ℍ → ℍ)
    (α β : ℂ) (hm : ∀ τ : ℍ, (m τ : ℂ) = α * τ + β) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f ∘ m) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf ⊢
  have hmaps : Set.MapsTo (fun z : ℂ ↦ α * z + β) {z | 0 < z.im} {z | 0 < z.im} := by
    intro z hz
    have h := (m ⟨z, hz⟩).im_pos
    rw [UpperHalfPlane.im, hm] at h
    exact h
  refine (hf.comp (by fun_prop : DifferentiableOn ℂ (fun z : ℂ ↦ α * z + β) _) hmaps).congr ?_
  intro z hz
  have hmz : m (ofComplex z) = ofComplex (α * z + β) := by
    apply UpperHalfPlane.ext
    rw [hm, ofComplex_apply_of_im_pos hz, ofComplex_apply_of_im_pos (hmaps hz)]
  simp only [Function.comp_apply, hmz]

/- English proof (translation)
Simplify using `[Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Multiset.prod_cons, Multiset.sum_map_mul_left]`.
-/
theorem esymm_cons_succ {R : Type*} [CommSemiring R] (a : R) (s : Multiset R) (k : ℕ) :
    (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Multiset.prod_cons,
    Multiset.sum_map_mul_left]

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on generalizing k with`. Consider the case `empty`. Break down `k with _ | k` into its components or cases. Simplify `mdifferentiable_const` using `[Multiset.esymm]`. Simplify `mdifferentiable_const` using `[Multiset.esymm]`.

Consider the case `cons f s ih`. Break down `k with _ | k` into its components or cases. Simplify `mdifferentiable_const` using `[Multiset.esymm]`. Simplify using `only [Multiset.map_cons, esymm_cons_succ]`. Establish `hs' : ∀ g ∈ s, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g` using `fun g hg ↦ hs g (Multiset.mem_cons_of_mem hg)`.

Conclude with `(ih hs' (k + 1)).add ((hs f (Multiset.mem_cons_self _ _)).mul (ih hs' k))`.
-/
theorem mdifferentiable_esymm (s : Multiset (ℍ → ℂ))
    (hs : ∀ f ∈ s, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (k : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ ↦ (s.map fun f ↦ f τ).esymm k) := by
  induction s using Multiset.induction_on generalizing k with
  | empty =>
    rcases k with _ | k
    · simpa [Multiset.esymm] using mdifferentiable_const
    · simpa [Multiset.esymm] using mdifferentiable_const
  | cons f s ih =>
    rcases k with _ | k
    · simpa [Multiset.esymm] using mdifferentiable_const
    · simp only [Multiset.map_cons, esymm_cons_succ]
      have hs' : ∀ g ∈ s, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g := fun g hg ↦
        hs g (Multiset.mem_cons_of_mem hg)
      exact (ih hs' (k + 1)).add ((hs f (Multiset.mem_cons_self _ _)).mul (ih hs' k))

/- English proof (translation)
Introduce `n k`. Establish `hΔ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) discriminant`. Simplify using `using ModularFormClass.holo CuspForm.discriminant`. Set `fs : Multiset (ℍ → ℂ)` to `(fun τ ↦ (n : ℂ) ^ 12 * discriminant (mulPoint n τ) / discriminant τ) ::ₘ (Multiset.range n).map fun a τ ↦ discriminant (divPoint n a τ) / discriminant τ`. Establish `hfs : (fun τ ↦ (heckeRatios n τ).esymm k) = fun τ ↦ (fs.map fun f ↦ f τ).esymm k`.

Use function extensionality and compare the values at `τ`. Simplify using `[heckeRatios, fs, Multiset.map_map]`. Rewrite using `[hfs]`. Apply `mdifferentiable_esymm` to reduce the goal to its premises. Introduce `f hf`.

Simplify using `only [fs, Multiset.mem_cons, Multiset.mem_map, Multiset.mem_range] at hf`. Break down `hf with rfl | ⟨a, -, rfl⟩` into its components or cases. Establish `h` using `mdifferentiable_comp_affine hΔ (mulPoint n) n 0 (fun τ ↦ by simp [coe_mulPoint])`. Conclude with `(mdifferentiable_const.mul h).div hΔ discriminant_ne_zero`. Establish `h` using `mdifferentiable_comp_affine hΔ (divPoint n a) (1 / n) (a / n) (fun τ ↦ by rw [coe_divPoint]; ring)`.

Conclude with `h.div hΔ discriminant_ne_zero`.
-/
theorem proof : HeckeRatioHolo.Statement := by
  intro n k
  have hΔ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) discriminant := by
    simpa using ModularFormClass.holo CuspForm.discriminant
  let fs : Multiset (ℍ → ℂ) :=
    (fun τ ↦ (n : ℂ) ^ 12 * discriminant (mulPoint n τ) / discriminant τ) ::ₘ
      (Multiset.range n).map fun a τ ↦ discriminant (divPoint n a τ) / discriminant τ
  have hfs : (fun τ ↦ (heckeRatios n τ).esymm k) = fun τ ↦ (fs.map fun f ↦ f τ).esymm k := by
    funext τ
    simp [heckeRatios, fs, Multiset.map_map]
  rw [hfs]
  apply mdifferentiable_esymm
  intro f hf
  simp only [fs, Multiset.mem_cons, Multiset.mem_map, Multiset.mem_range] at hf
  rcases hf with rfl | ⟨a, -, rfl⟩
  · have h := mdifferentiable_comp_affine hΔ (mulPoint n) n 0 (fun τ ↦ by simp [coe_mulPoint])
    exact (mdifferentiable_const.mul h).div hΔ discriminant_ne_zero
  · have h := mdifferentiable_comp_affine hΔ (divPoint n a) (1 / n) (a / n)
      (fun τ ↦ by rw [coe_divPoint]; ring)
    exact h.div hΔ discriminant_ne_zero

end HeckeRatioHolo

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
