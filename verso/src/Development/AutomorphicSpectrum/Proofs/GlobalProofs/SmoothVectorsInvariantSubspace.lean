import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

/- English proof (translation)
Establish `e : (fun z : Fin n → Fin n → ℂ => (fun i j => (Matrix.of z * g) i j : Fin n → Fin n → ℂ)) = fun z i j => ∑ k, z i k * g k j`. Use extensionality with `z i j`. Simplify using `[Matrix.mul_apply]`. Rewrite using `[e]`. Use `contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_` and prove the remaining obligations.

Use `ContDiff.sum fun k _ => ?_` and prove the remaining obligations. Conclude with `((contDiff_apply ℝ ℂ k).comp (contDiff_apply ℝ (Fin n → ℂ) i)).mul contDiff_const`.
-/
theorem contDiff_mulRight {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ (fun z : Fin n → Fin n → ℂ => (fun i j => (Matrix.of z * g) i j : Fin n → Fin n → ℂ)) := by
  have e : (fun z : Fin n → Fin n → ℂ => (fun i j => (Matrix.of z * g) i j : Fin n → Fin n → ℂ)) =
      fun z i j => ∑ k, z i k * g k j := by
    ext z i j
    simp [Matrix.mul_apply]
  rw [e]
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  refine ContDiff.sum fun k _ => ?_
  exact ((contDiff_apply ℝ ℂ k).comp (contDiff_apply ℝ (Fin n → ℂ) i)).mul contDiff_const

/- English proof (translation)
Introduce `n G H _ _ π hG hrep`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `u v ⟨Fu, hFu, hu⟩ ⟨Fv, hFv, hv⟩`. Use `⟨fun z => Fu z + Fv z, hFu.add hFv, fun z hz => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, hu z hz, hv z hz]`.

Introduce and unpack `c v ⟨Fv, hFv, hv⟩`. Use `⟨fun z => c • Fv z, hFv.const_smul c, fun z hz => ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, hv z hz]`. Introduce and unpack `g hg v ⟨Fv, hFv, hv⟩`. Use `⟨fun z => Fv (fun i j => (Matrix.of z * g) i j), hFv.comp (contDiff_mulRight g), fun z hz => ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hrep.2 _ hz _ hg, ContinuousLinearMap.comp_apply]`. Use `_ = Fv (fun i j => (Matrix.of z * g) i j) := hv _ (hG.mul_mem _ hz _ hg)`.
-/
theorem smooth_closed : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π),
    (∀ u v : H, IsSmoothVec G π u → IsSmoothVec G π v → IsSmoothVec G π (u + v)) ∧
    (∀ (c : ℂ) (v : H), IsSmoothVec G π v → IsSmoothVec G π (c • v)) ∧
    (∀ g ∈ G, ∀ v : H, IsSmoothVec G π v → IsSmoothVec G π (π g v)) := by
  intro n G H _ _ π hG hrep
  refine ⟨?_, ?_, ?_⟩
  · rintro u v ⟨Fu, hFu, hu⟩ ⟨Fv, hFv, hv⟩
    refine ⟨fun z => Fu z + Fv z, hFu.add hFv, fun z hz => ?_⟩
    rw [map_add, hu z hz, hv z hz]
  · rintro c v ⟨Fv, hFv, hv⟩
    refine ⟨fun z => c • Fv z, hFv.const_smul c, fun z hz => ?_⟩
    rw [map_smul, hv z hz]
  · rintro g hg v ⟨Fv, hFv, hv⟩
    refine ⟨fun z => Fv (fun i j => (Matrix.of z * g) i j), hFv.comp (contDiff_mulRight g),
      fun z hz => ?_⟩
    calc π (Matrix.of z) (π g v) = π (Matrix.of z * g) v := by
          rw [hrep.2 _ hz _ hg, ContinuousLinearMap.comp_apply]
      _ = Fv (fun i j => (Matrix.of z * g) i j) := hv _ (hG.mul_mem _ hz _ hg)

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA

end
