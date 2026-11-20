import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnfSupportOfNeOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.FunObj.FiniteSupport

noncomputable section

namespace GlobalTheory.TopLevelInv

/- English proof (translation)
Substitute `hc` using the available equality. Rewrite using `[Equiv.symm_apply_eq]`. Use `ext`. Simplify using `only [frame, Equiv.trans_apply, finCongr_apply, Fin.val_cast]`. Both sides reduce to the same expression.
-/
theorem frame_symm_of_zero {a c b : ℕ} (h : a + c = b) (hc : c = 0) (p : Fin b) :
    (frame h).symm p = Sum.inl ⟨p.val, by omega⟩ := by
  subst hc
  rw [Equiv.symm_apply_eq]
  ext
  simp only [frame, Equiv.trans_apply, finCongr_apply, Fin.val_cast]
  rfl

/- English proof (translation)
Introduce `k _ _ _ _ _ _ Γ hs j hj hB g κ hg x x' e e' hx`. Establish `hr : Γ.rank (Γ.m, j + 1) = topRank Γ (j + 1)` using `by have := topRank_add hs (j + 1); omega`. Establish `hval : ∀ p q, g.val p q = κ.val (Fin.cast hr p) (Fin.cast hr q)`. Introduce `p q`. Establish `h1 : g = (toFrame hs hj).symm (embX _ κ)` using `by rw [← hg, MulEquiv.symm_apply_apply]`.

Rewrite using `[h1]`. Unfold `toFrame`. Rewrite using `[frameGL_symm_val, submatrix_apply, frame_symm_of_zero _ (by omega), frame_symm_of_zero _ (by omega)]`. Both sides reduce to the same expression. Unfold `downMap`.

Rewrite using `[dif_neg (by omega), dif_pos (by omega), dif_neg (by omega), dif_pos (by omega), hx]`. Use extensionality with `r q`. Simplify using `only [submatrix_apply, mul_apply, hval]`. Conclude with `(Fintype.sum_equiv (finCongr hr) _ _ (fun p => rfl)).symm`.
-/
theorem downMap_last_mul_of_toFrame_eq : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (hs : 1 ≤ Γ.s) (j : ℕ) (hj : j + 1 < Γ.m) (hB : j + 2 = Γ.m)
    (g : GL (Fin (Γ.rank (Γ.m, j + 1))) k) (κ : GL (Fin (topRank Γ (j + 1))) k),
    toFrame hs hj g = embX (Γ.m - 1 - (j + 1)) κ → ∀ (x x' : ColArgs Γ) (e e' : Vars Γ), x' (j + 1) = x (j + 1) * κ.val →
    downMap hs x' e' (j + 1) = downMap hs x e (j + 1) * g.val := by
  intro k _ _ _ _ _ _ Γ hs j hj hB g κ hg x x' e e' hx
  have hr : Γ.rank (Γ.m, j + 1) = topRank Γ (j + 1) := by have := topRank_add hs (j + 1); omega
  have hval : ∀ p q, g.val p q = κ.val (Fin.cast hr p) (Fin.cast hr q) := by
    intro p q
    have h1 : g = (toFrame hs hj).symm (embX _ κ) := by rw [← hg, MulEquiv.symm_apply_apply]
    rw [h1]
    unfold toFrame
    rw [frameGL_symm_val, submatrix_apply, frame_symm_of_zero _ (by omega), frame_symm_of_zero _ (by omega)]
    rfl
  unfold downMap
  rw [dif_neg (by omega), dif_pos (by omega), dif_neg (by omega), dif_pos (by omega), hx]
  ext r q
  simp only [submatrix_apply, mul_apply, hval]
  exact (Fintype.sum_equiv (finCongr hr) _ _ (fun p => rfl)).symm

end GlobalTheory.TopLevelInv

end
