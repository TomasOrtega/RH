import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAddValuationIntegerRingNormalizedIff
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge

namespace GlobalTheory

/- English proof (translation)
Introduce `C _ w v hv S _ _ a N F τ hinj _hfilt _hevinj hrange hmem hlast z`. Establish `hev : ∀ x : Fin N → RS (liftA hv a), ∀ s i, evalVec (liftA hv a) N (lin (liftA hv a) τ • x) s i = ((a s : C) - a τ) * evalVec (liftA hv a) N x s i`. Introduce `x s i`. Simplify using `only [evalVec, Pi.smul_apply, smul_eq_mul, map_mul, ev_lin]`. Both sides reduce to the same expression.

Establish `hevs : ∀ x : Fin N → RS (liftA hv a), ∀ s, evalVec (liftA hv a) N (lin (liftA hv a) τ • x) s = ((a s : C) - a τ) • evalVec (liftA hv a) N x s`. Introduce `x s`. Use function extensionality and compare the values at `i`. Rewrite using `[hev]`. Both sides reduce to the same expression.

Establish `heig : ∀ x : Fin N → RS (liftA hv a), proj (liftA hv a) (filPre (liftA hv a) F) x ∈ eigSub (liftA hv a) τ ((Fin N → RS (liftA hv a)) ⧸ filPre (liftA hv a) F) ↔ evalVec (liftA hv a) N (lin (liftA hv a) τ • x) ∈ F`. Introduce `x`. Rewrite using `[← hmem]`. Use `show lin (liftA hv a) τ • (filPre (liftA hv a) F).mkQ x = 0 ↔ _`. Rewrite using `[← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`.

Establish `hlie : z ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N) F) τ ↔ ∃ h ∈ GlobalTheory.IndefiniteRowSideFu …`. Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub, GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie, Submodule.mem_comap, Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, hh, he⟩`. Conclude with `⟨h, hh, fun s => congrFun he s⟩`.

Introduce and unpack `⟨h, hh, he⟩`. Conclude with `⟨h, hh, funext he⟩`. Rewrite using `[hlie]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, hh, he⟩`.

Take `⟨x, rfl⟩` from `(hrange h).1 hh`. Use `⟨x, (heig x).2 ?_, ?_⟩` and prove the remaining obligations. Apply `hlast _ ((hrange _).2 ⟨_, rfl⟩)` to reduce the goal to its premises. Introduce `s`. Rewrite using `[hevs]`.

Distinguish the cases in `hs : s = τ`. Rewrite using `[hs, sub_self, zero_smul]`. Conclude with `zero_mem _`. Establish `h1 : evalVec (liftA hv a) N x s ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F s`. Use `he s` as an intermediate fact.

Rewrite `this` using `[Pi.single_eq_of_ne hs, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `this`. Conclude with `Submodule.smul_mem _ _ h1`. Use `he τ` as an intermediate fact. Rewrite `this` using `[Pi.single_eq_same]`.

Conclude with `this`. Introduce and unpack `⟨x, hx, rfl⟩`. Use `⟨evalVec (liftA hv a) N x, (hrange _).2 ⟨x, rfl⟩, fun s => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hs : s = τ`. Substitute `hs` using the available equality.

Rewrite using `[Pi.single_eq_same]`. Both sides reduce to the same expression. Rewrite using `[Pi.single_eq_of_ne hs, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Establish `hy` using `(heig x).1 hx`. Establish `hys : evalVec (liftA hv a) N (lin (liftA hv a) τ • x) s ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F s` using `Submodule.subset_span ⟨_, hy, rfl⟩`.

Establish `hne : (a s : C) - a τ ≠ 0` using `sub_ne_zero.2 fun e => hs (hinj (Subtype.ext e))`. Establish `: evalVec (liftA hv a) N x s = ((a s : C) - a τ)⁻¹ • evalVec (liftA hv a) N (lin (liftA hv a) τ • x) s`. Rewrite using `[hevs, smul_smul, inv_mul_cancel₀ hne, one_smul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hys`.
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
