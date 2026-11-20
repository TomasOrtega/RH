import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSemisimple
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTraceMulEqZeroSemisimpleRepStatement
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.Cong

/- English proof (translation)
Introduce `l _ Γ _ a r C hss hC s hs`. Establish `htr : ∀ g, trc r (s * g) = trc r g`. Introduce `g`. Use `eq_of_forall_dist_le fun ε hε => ?_` and prove the remaining obligations. Take `⟨t, c, ht, hb⟩` from `hC (ε / 2) (by positivity)`.

Establish `hsum : ∑ ρ ∈ t, c ρ * trc ρ (s * g) = ∑ ρ ∈ t, c ρ * trc ρ g`. Use `Finset.sum_congr rfl fun ρ hρ => ?_` and prove the remaining obligations. Simplify using `[trc, map_mul, hs ρ (ht hρ)]`. Rewrite using `[dist_eq_norm]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hsum]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ ‖trc r (s * g) - ∑ ρ ∈ t, c ρ * trc ρ (s * g)‖ + ‖trc r g - ∑ ρ ∈ t, c ρ * trc ρ g‖ := norm_sub_le _ _`. Use `_ ≤ ε / 2 + ε / 2 := add_le_add (hb _) (hb _)`.

Use `_ = ε := by ring`. Use `set R : Γ → Matrix (Fin a) (Fin a) (PadicAlgCl l) := fun g => ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) with hR`. Establish `hM : R s - 1 ∈ Submodule.span (PadicAlgCl l) (Set.range R)`. Use `Submodule.sub_mem _ (Submodule.subset_span ⟨s, rfl⟩) ?_` and prove the remaining obligations. Establish `: R 1 = 1` using `by simp [hR]`.

Rewrite using `[← this]`. Conclude with `Submodule.subset_span ⟨1, rfl⟩`. Establish `h0` using `GlobalTheory.T.eq_zero_of_trace_mul_eq_zero_semisimple_rep (PadicAlgCl l) Γ a r hss (R s - 1) hM (fun g => by`. Use `htr g` as an intermediate fact. Simplify using `only [trc, map_mul, Units.val_mul] at this`.

Rewrite using `[sub_mul, one_mul, Matrix.trace_sub]`. Simplify `sub_eq_zero.2 this)` using `[hR]`. Use extensionality with `i j`. Use `congrFun (congrFun (sub_eq_zero.1 h0) i) j` as an intermediate fact. Simplify `this` using `[hR]`.
-/
theorem ker_of_linApprox : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) (PadicAlgCl l))
    (C : Set (Γ →* GL (Fin a) (PadicAlgCl l))), IsSSRep r → LinApprox r C → ∀ s : Γ, (∀ ρ ∈ C, ρ s = 1) → r s = 1 := by
  intro l _ Γ _ a r C hss hC s hs
  have htr : ∀ g, trc r (s * g) = trc r g := by
    intro g
    refine eq_of_forall_dist_le fun ε hε => ?_
    obtain ⟨t, c, ht, hb⟩ := hC (ε / 2) (by positivity)
    have hsum : ∑ ρ ∈ t, c ρ * trc ρ (s * g) = ∑ ρ ∈ t, c ρ * trc ρ g := by
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      simp [trc, map_mul, hs ρ (ht hρ)]
    rw [dist_eq_norm]
    calc ‖trc r (s * g) - trc r g‖
        = ‖(trc r (s * g) - ∑ ρ ∈ t, c ρ * trc ρ (s * g)) - (trc r g - ∑ ρ ∈ t, c ρ * trc ρ g)‖ := by
          rw [hsum]; congr 1; ring
      _ ≤ ‖trc r (s * g) - ∑ ρ ∈ t, c ρ * trc ρ (s * g)‖ + ‖trc r g - ∑ ρ ∈ t, c ρ * trc ρ g‖ := norm_sub_le _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add (hb _) (hb _)
      _ = ε := by ring
  set R : Γ → Matrix (Fin a) (Fin a) (PadicAlgCl l) := fun g => ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) with hR
  have hM : R s - 1 ∈ Submodule.span (PadicAlgCl l) (Set.range R) := by
    refine Submodule.sub_mem _ (Submodule.subset_span ⟨s, rfl⟩) ?_
    have : R 1 = 1 := by simp [hR]
    rw [← this]; exact Submodule.subset_span ⟨1, rfl⟩
  have h0 := GlobalTheory.T.eq_zero_of_trace_mul_eq_zero_semisimple_rep (PadicAlgCl l) Γ a r hss (R s - 1) hM (fun g => by
    have := htr g
    simp only [trc, map_mul, Units.val_mul] at this
    rw [sub_mul, one_mul, Matrix.trace_sub]
    simpa [hR] using sub_eq_zero.2 this)
  ext i j
  have := congrFun (congrFun (sub_eq_zero.1 h0) i) j
  simpa [hR] using this

end GlobalTheory.Cong
