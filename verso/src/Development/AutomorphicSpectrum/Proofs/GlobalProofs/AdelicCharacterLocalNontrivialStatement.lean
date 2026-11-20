import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterLocalNontrivial
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsAdaptedEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.ComplFrame.frame_cols` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FAdelicCharacterLocalNontrivial.lean&line=184#L184)
-/
theorem _root_.GlobalTheory.T.adapted_frame_orthogonal_subspace : ∀ (D : D7) (V V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι →
    ∀ (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y →
    ∀ T : Finset (Fin m), (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) →
    ∀ C : GL (Fin V.rank) D.host.E, GlobalTheory.BlockForms.IsAdapted D.sp.cm.sig V.gram X Y C →
    ∀ a : ℕ, a ≤ m → (∀ i : Fin m, i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T ↔ i.val < a) →
    ∃ hdim : a + V'.rank + a = V.rank, ∃ B Bi : Matrix (Fin V'.rank) (Fin V'.rank) D.host.E, B * Bi = 1 ∧
      (∀ (i : Fin V.rank) (j : Fin V'.rank), frameMat V V' ι i j = ∑ r : Fin V'.rank, C.1 i (⟨a + r.val, by omega⟩ : Fin V.rank) * B r j) ∧
      ∀ b : Fin V.rank, (b.val < a ∨ V.rank ≤ b.val + a) →
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι) * V.gram) *ᵥ (fun k => C.1 k b) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.ComplFrame.frame_cols | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.ComplFrame.frame_cols | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.ComplFrame.frame_cols <;> assumption)
