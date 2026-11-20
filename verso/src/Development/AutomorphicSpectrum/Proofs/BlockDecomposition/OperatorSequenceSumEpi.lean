import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerSCShortExact
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.KerSeq

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem epi_sumMap_of_opSeq {X : Scheme.{0}} {k : ℕ} {M : ℕ → X.Modules}
    {T : Fin k → ∀ e, M e ⟶ M (e + 1)} {d : ℕ} (h : OpSeq k M T d) (e : ℕ) :
    Epi (KerSeq.sumMap T d e) := by
  haveI : ∀ n, (M n).IsQuasicoherent := fun n => (h.coherent n).1
  haveI : (KerSeq.sumN M k d e).IsQuasicoherent := by
    unfold KerSeq.sumN
    exact GlobalTheory.QCoh.isQuasicoherent_biproduct _
  rw [GlobalTheory.QCoh.epi_iff_forall_affine]
  intro U hU
  have hg := h.gen (d + e) (Nat.le_add_right d e) ⟨U, hU⟩
  have hr : (GlobalTheory.QCoh.appLinear (KerSeq.sumMap T d e) U).range = ⊤ := by
    rw [eq_top_iff, ← hg, Submodule.span_le]
    intro y hy
    simp only [Set.mem_iUnion, Set.mem_range] at hy
    obtain ⟨i, x, rfl⟩ := hy
    refine ⟨(biproduct.ι (fun _ : Fin k => M (d + e)) i).app U x, ?_⟩
    rw [GlobalTheory.QCoh.appLinear_apply, GlobalTheory.QCoh.app_app]
    simp [KerSeq.sumMap]
  rw [← GlobalTheory.QCoh.coe_appLinear]
  exact LinearMap.range_eq_top.1 hr

end GlobalTheory.CompanionTheory.GE.KerSeq
