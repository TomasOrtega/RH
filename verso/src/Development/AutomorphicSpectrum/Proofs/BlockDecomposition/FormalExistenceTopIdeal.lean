import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeIffAffineSections

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.Unit

/- English proof (translation)
Use `top_le_iff.mp ((GlobalTheory.CompanionTheory.GE.le_iff_secs_subset ⊤ S).mpr fun U x _ => ?_)` and prove the remaining obligations. Establish `hx` using `h U 1 (by simp [Scheme.IdealSheafData.ideal_top]) x`. Rewrite `hx` using `[one_smul]`. Then use the resulting hypothesis.
-/
theorem eq_top_of_killed_top {X : Scheme.{0}} {E : X.Modules} (S : Subobject E)
    (h : Killed (⊤ : X.IdealSheafData) S) : S = ⊤ := by
  refine top_le_iff.mp ((GlobalTheory.CompanionTheory.GE.le_iff_secs_subset ⊤ S).mpr fun U x _ => ?_)
  have hx := h U 1 (by simp [Scheme.IdealSheafData.ideal_top]) x
  rwa [one_smul] at hx

/- English proof (translation)
Introduce `E _ S hS hann hprop`. Establish `htop : ∀ e, S e = ⊤` using `fun e => GlobalTheory.CompanionTheory.GE.Unit.eq_top_of_killed_top (S e) (hann e)`. Take `⟨hqc, -, -⟩` from `hS`. Unfold `GlobalTheory.CompanionTheory.GE.Alg`. Use `⟨S 0, hqc 0, hprop, fun e => ?_⟩` and prove the remaining obligations.

Rewrite using `[htop 0, htop e, top_sup_eq]`.
-/
theorem statement_top {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] : Statement I (⊤ : X.IdealSheafData) := by
  intro E _ S hS hann hprop
  have htop : ∀ e, S e = ⊤ := fun e => GlobalTheory.CompanionTheory.GE.Unit.eq_top_of_killed_top (S e) (hann e)
  obtain ⟨hqc, -, -⟩ := hS
  unfold GlobalTheory.CompanionTheory.GE.Alg
  refine ⟨S 0, hqc 0, hprop, fun e => ?_⟩
  rw [htop 0, htop e, top_sup_eq]

end GlobalTheory.CompanionTheory.GE.Unit
