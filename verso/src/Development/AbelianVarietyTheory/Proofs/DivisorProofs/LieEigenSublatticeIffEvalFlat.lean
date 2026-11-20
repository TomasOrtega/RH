import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAddValuationIntegerRingNormalizedIff
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem lie_eigenSub_iff_flat : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ)) (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ) (F : Submodule w.valuationSubring (S → Fin N → C)) (τ : S), Function.Injective a → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration a F → Function.Injective (evalVec (liftA hv a) N) → (∀ y, y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N ↔ ∃ x, evalVec (liftA hv a) N x = y) → (∀ x, x ∈ filPre (liftA hv a) F ↔ evalVec (liftA hv a) N x ∈ F) → (∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N, (∀ s, x s ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F s) → x ∈ F) → ∀ z : (Fin N → C) ⧸ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F τ, z ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N) F) τ ↔ ∃ x : Fin N → RS (liftA hv a), proj (liftA hv a) (filPre (liftA hv a) F) x ∈ eigSub (liftA hv a) τ ((Fin N → RS (liftA hv a)) ⧸ filPre (liftA hv a) F) ∧ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.quotMap (w := w) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F τ) (fun i => ((comp (liftA hv a) N τ x i : Int0 v) : C)) = z := by
  intro C _ w v hv S _ _ a N F τ hinj _hfilt _hevinj hrange hmem hlast z
  have hev : ∀ x : Fin N → RS (liftA hv a), ∀ s i,
      evalVec (liftA hv a) N (lin (liftA hv a) τ • x) s i
        = ((a s : C) - a τ) * evalVec (liftA hv a) N x s i := by
    intro x s i
    simp only [evalVec, Pi.smul_apply, smul_eq_mul, map_mul, ev_lin]
    rfl
  have hevs : ∀ x : Fin N → RS (liftA hv a), ∀ s,
      evalVec (liftA hv a) N (lin (liftA hv a) τ • x) s
        = ((a s : C) - a τ) • evalVec (liftA hv a) N x s := by
    intro x s; funext i; rw [hev]; rfl
  have heig : ∀ x : Fin N → RS (liftA hv a),
      proj (liftA hv a) (filPre (liftA hv a) F) x ∈
          eigSub (liftA hv a) τ ((Fin N → RS (liftA hv a)) ⧸ filPre (liftA hv a) F) ↔
        evalVec (liftA hv a) N (lin (liftA hv a) τ • x) ∈ F := by
    intro x
    rw [← hmem]
    show lin (liftA hv a) τ • (filPre (liftA hv a) F).mkQ x = 0 ↔ _
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hlie : z ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub
        (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N) F) τ ↔
      ∃ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N, ∀ s,
        (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F s).mkQ (h s) =
          (Pi.single τ z : ∀ s, (Fin N → C) ⧸ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F s) s := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub, GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie, Submodule.mem_comap,
      Submodule.mem_map]
    constructor
    · rintro ⟨h, hh, he⟩
      exact ⟨h, hh, fun s => congrFun he s⟩
    · rintro ⟨h, hh, he⟩
      exact ⟨h, hh, funext he⟩
  rw [hlie]
  constructor
  · rintro ⟨h, hh, he⟩
    obtain ⟨x, rfl⟩ := (hrange h).1 hh
    refine ⟨x, (heig x).2 ?_, ?_⟩
    · apply hlast _ ((hrange _).2 ⟨_, rfl⟩)
      intro s
      rw [hevs]
      by_cases hs : s = τ
      · rw [hs, sub_self, zero_smul]; exact zero_mem _
      · have h1 : evalVec (liftA hv a) N x s ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F s := by
          have := he s
          rw [Pi.single_eq_of_ne hs, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
          exact this
        exact Submodule.smul_mem _ _ h1
    · have := he τ
      rw [Pi.single_eq_same] at this
      exact this
  · rintro ⟨x, hx, rfl⟩
    refine ⟨evalVec (liftA hv a) N x, (hrange _).2 ⟨x, rfl⟩, fun s => ?_⟩
    by_cases hs : s = τ
    · subst hs
      rw [Pi.single_eq_same]
      rfl
    · rw [Pi.single_eq_of_ne hs, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      have hy := (heig x).1 hx
      have hys : evalVec (liftA hv a) N (lin (liftA hv a) τ • x) s ∈
          GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F s :=
        Submodule.subset_span ⟨_, hy, rfl⟩
      have hne : (a s : C) - a τ ≠ 0 := sub_ne_zero.2 fun e => hs (hinj (Subtype.ext e))
      have : evalVec (liftA hv a) N x s =
          ((a s : C) - a τ)⁻¹ • evalVec (liftA hv a) N (lin (liftA hv a) τ • x) s := by
        rw [hevs, smul_smul, inv_mul_cancel₀ hne, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ hys

end GlobalTheory
