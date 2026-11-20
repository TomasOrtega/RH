import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.IotaMem

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Simplify using `only [embedding₂, MonoidHom.coe_comp, Function.comp_apply]`. Unfold `levi`. Simplify using `[glEmb, glEmbHom, glEmbMat]`.
-/
theorem iotaM_castSucc_castSucc (n : ℕ) (y : Mir k n) (r c : Fin (n + 1)) :
    (((embedding₂ k n y : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) : Matrix _ _ k) (Fin.castSucc r) (Fin.castSucc c) =
      ((y : GL (Fin (n + 1)) k) : Matrix _ _ k) r c := by
  simp only [embedding₂, MonoidHom.coe_comp, Function.comp_apply]
  unfold levi
  simp [glEmb, glEmbHom, glEmbMat]

/- English proof (translation)
Simplify using `only [embedding₂, MonoidHom.coe_comp, Function.comp_apply]`. Unfold `levi`. Simplify using `[glEmb, glEmbHom, glEmbMat]`.
-/
theorem iotaM_last_castSucc (n : ℕ) (y : Mir k n) (c : Fin (n + 1)) :
    (((embedding₂ k n y : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) : Matrix _ _ k) (Fin.last (n + 1)) (Fin.castSucc c) = 0 := by
  simp only [embedding₂, MonoidHom.coe_comp, Function.comp_apply]
  unfold levi
  simp [glEmb, glEmbHom, glEmbMat]

end GlobalTheory.CompanionTheory.LeibPhi.IotaMem

namespace GlobalTheory.CompanionTheory.LeibPhi

open GlobalTheory.CompanionTheory.LeibPhi.IotaMem in

/- English proof (translation)
Rewrite using `[mem_mirabolicParabolic_iff, mem_mirabolicParabolic_iff]`. Establish `eF : ∀ a : Fin m, eGP m (j + 1) ⟨false, a⟩ = Fin.castSucc (eGP m j ⟨false, a⟩)`. Introduce `a`. Use `ext`. Simplify using `[blockIndex_false_val]`.

Establish `eT : ∀ b : Fin (j + 1), eGP m (j + 1) ⟨true, Fin.castSucc b⟩ = Fin.castSucc (eGP m j ⟨true, b⟩)`. Introduce `b`. Use `ext`. Simplify using `[blockIndex_true_val]`. Establish `eL : eGP m (j + 1) ⟨true, Fin.last (j + 1)⟩ = Fin.last (m + j + 1)`.

Use `ext`. Simplify using `[blockIndex_true_val]`. Use linear arithmetic over natural numbers and integers. Prove the components needed by the constructor for the conclusion. Introduce `h b a`.

Proceed by induction on `b using Fin.lastCases with`. Consider the case `last`. Rewrite using `[eL, eF]`. Conclude with `iotaM_last_castSucc k (m + j) y _`. Consider the case `cast b`.

Rewrite using `[eT, eF]`. Rewrite using `[iotaM_castSucc_castSucc k (m + j) y]`. Conclude with `h b a`. Introduce `h b a`. Establish `hb` using `h (Fin.castSucc b) a`.

Rewrite `hb` using `[eT, eF, iotaM_castSucc_castSucc k (m + j) y]`. Conclude with `hb`.
-/
theorem mem_mirabolicParabolic_iff_iotaM_mem (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ) (y : Mir k (m + j)) :
    y ∈ MirabolicParabolic k m j ↔ embedding₂ k (m + j) y ∈ MirabolicParabolic k m (j + 1) := by
  rw [mem_mirabolicParabolic_iff, mem_mirabolicParabolic_iff]
  have eF : ∀ a : Fin m, eGP m (j + 1) ⟨false, a⟩ = Fin.castSucc (eGP m j ⟨false, a⟩) := by
    intro a
    ext
    simp [blockIndex_false_val]
  have eT : ∀ b : Fin (j + 1),
      eGP m (j + 1) ⟨true, Fin.castSucc b⟩ = Fin.castSucc (eGP m j ⟨true, b⟩) := by
    intro b
    ext
    simp [blockIndex_true_val]
  have eL : eGP m (j + 1) ⟨true, Fin.last (j + 1)⟩ = Fin.last (m + j + 1) := by
    ext
    simp [blockIndex_true_val]
    omega
  constructor
  · intro h b a
    induction b using Fin.lastCases with
    | last =>
      rw [eL, eF]
      exact iotaM_last_castSucc k (m + j) y _
    | cast b =>
      rw [eT, eF]
      rw [iotaM_castSucc_castSucc k (m + j) y]
      exact h b a
  · intro h b a
    have hb := h (Fin.castSucc b) a
    rw [eT, eF, iotaM_castSucc_castSucc k (m + j) y] at hb
    exact hb

end GlobalTheory.CompanionTheory.LeibPhi

end
