import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.HeckeRatioHolo
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm
open scoped Manifold

noncomputable section

namespace HeckeRatioHolo

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
Simplify using the standard rewrite rules.
-/
theorem esymm_cons_succ {R : Type*} [CommSemiring R] (a : R) (s : Multiset R) (k : ℕ) :
    (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Multiset.prod_cons,
    Multiset.sum_map_mul_left]

/- English proof (translation)
Proceed by induction. Treat this case separately. Separate the alternatives or extract the components of the hypothesis. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts.

Treat this case separately. Separate the alternatives or extract the components of the hypothesis. Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules. Establish an intermediate fact.

A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Introduce a local definition for the expression. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
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
