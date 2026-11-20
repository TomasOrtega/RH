import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot

noncomputable section

namespace GlobalTheory.TwV

open NumberField
open scoped Matrix

/- English proof (translation)
Take `⟨u, hu'⟩` from `hs`. Establish `hmem : (fun k => ρ (((s : E) • z) k)) ∈ locSp W ρ L'` using `Submodule.subset_span ⟨_, hz, rfl⟩`. Establish `e : (fun k => ρ (z k)) = ((↑u⁻¹ : W)) • (fun k => ρ (((s : E) • z) k))`. Use function extensionality and compare the values at `k`. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, Algebra.smul_def]`.

Rewrite using `[← mul_assoc, ← map_natCast (algebraMap W K) s, ← hu', ← map_mul, Units.inv_mul, map_one, one_mul]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ hmem`.
-/
theorem mem_locSp_of_natCast_smul_mem {E : Type} [Field E] [NumberField E] (W K : Type) [CommRing W] [Field K] [Algebra W K]
    (ρ : E →+* K) {N' : ℕ} (L' : Submodule (𝓞 E) (Fin N' → E)) (z : Fin N' → E) (s : ℕ) (hs : IsUnit (s : W))
    (hz : (s : E) • z ∈ L') : (fun k => ρ (z k)) ∈ locSp W ρ L' := by
  obtain ⟨u, hu'⟩ := hs
  have hmem : (fun k => ρ (((s : E) • z) k)) ∈ locSp W ρ L' := Submodule.subset_span ⟨_, hz, rfl⟩
  have e : (fun k => ρ (z k)) = ((↑u⁻¹ : W)) • (fun k => ρ (((s : E) • z) k)) := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, Algebra.smul_def]
    rw [← mul_assoc, ← map_natCast (algebraMap W K) s, ← hu', ← map_mul, Units.inv_mul, map_one, one_mul]
  rw [e]
  exact Submodule.smul_mem _ _ hmem

/- English proof (translation)
Introduce `w hw`. Establish `h : locSp W ρ L ≤ (locSp W ρ L').comap (((A.map ρ).mulVecLin).restrictScalars W)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Use `show (A.map ρ) *ᵥ (fun k => ρ (x k)) ∈ locSp W ρ L'`.

Establish `e : (A.map ρ) *ᵥ (fun k => ρ (x k)) = fun k => ρ ((A *ᵥ x) k)`. Use function extensionality and compare the values at `k`. Conclude with `(RingHom.map_mulVec ρ A x k).symm`. Rewrite using `[e]`. Conclude with `mem_locSp_of_natCast_smul_mem W K ρ L' _ s hs (hA x hx)`.

Conclude with `h hw`.
-/
theorem locSp_maps_of_unit_smul {E : Type} [Field E] [NumberField E] (W K : Type) [CommRing W] [Field K] [Algebra W K]
    (ρ : E →+* K) {N N' : ℕ} (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E))
    (A : Matrix (Fin N') (Fin N) E) (s : ℕ) (hs : IsUnit (s : W)) (hA : ∀ x ∈ L, (s : E) • (A *ᵥ x) ∈ L') :
    ∀ z ∈ locSp W ρ L, (A.map ρ) *ᵥ z ∈ locSp W ρ L' := by
  intro w hw
  have h : locSp W ρ L ≤ (locSp W ρ L').comap (((A.map ρ).mulVecLin).restrictScalars W) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    show (A.map ρ) *ᵥ (fun k => ρ (x k)) ∈ locSp W ρ L'
    have e : (A.map ρ) *ᵥ (fun k => ρ (x k)) = fun k => ρ ((A *ᵥ x) k) := by
      funext k
      exact (RingHom.map_mulVec ρ A x k).symm
    rw [e]
    exact mem_locSp_of_natCast_smul_mem W K ρ L' _ s hs (hA x hx)
  exact h hw

end GlobalTheory.TwV

end
