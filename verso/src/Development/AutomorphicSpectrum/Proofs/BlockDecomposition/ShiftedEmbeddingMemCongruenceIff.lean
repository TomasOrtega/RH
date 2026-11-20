import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulMemBall
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Proceed by induction.

Treat this case separately. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Treat this case separately.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Treat this case separately.

Proceed by induction. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Treat this case separately. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem nearOne_glEmbMat_iff (s : kˣ) (m : ℕ) (A : Matrix (Fin m) (Fin m) k) :
    NearOne s (glEmbMat k m A) ↔ NearOne s A := by
  have e1 : ∀ a b : Fin m, glEmbMat k m A (Fin.castSucc a) (Fin.castSucc b) = A a b := by
    intro a b
    simp [glEmbMat]
  have e2 : ∀ a b : Fin m, (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.castSucc a) (Fin.castSucc b) =
      (1 : Matrix (Fin m) (Fin m) k) a b := by
    intro a b
    simp [Matrix.one_apply, Fin.castSucc_inj]
  have z : (0 : k) ∈ (ballSub s : Set k) := (ballSub s).zero_mem
  constructor
  · intro h a b
    have h1 := h (Fin.castSucc a) (Fin.castSucc b)
    rwa [e1, e2] at h1
  · intro h a b
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last =>
        have e : glEmbMat k m A (Fin.last m) (Fin.last m) - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) (Fin.last m) = 0 := by
          simp [glEmbMat]
        rw [e]
        exact z
      | cast j =>
        have e : glEmbMat k m A (Fin.last m) (Fin.castSucc j) - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) (Fin.castSucc j) = 0 := by
          rw [Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne', sub_zero]
          simp [glEmbMat]
        rw [e]
        exact z
    | cast i =>
      induction b using Fin.lastCases with
      | last =>
        have e : glEmbMat k m A (Fin.castSucc i) (Fin.last m) - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.castSucc i) (Fin.last m) = 0 := by
          rw [Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne, sub_zero]
          simp [glEmbMat]
        rw [e]
        exact z
      | cast j =>
        rw [e1, e2]
        exact h i j

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sEmb_mem_congM_iff (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1) (x : Mir k n) :
    sEmb k n x ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs (n + 1) ↔ x ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs n := by
  have e1 : (((sEmb k n x : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k) =
      glEmbMat k (n + 1) ((x : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := rfl
  have e2 : ((((sEmb k n x : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k)⁻¹ : GL (Fin (n + 1 + 1)) k) :
        Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k) =
      glEmbMat k (n + 1) (((x : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
    have : ((sEmb k n x : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k)⁻¹ = ((sEmb k n x⁻¹ : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) := by
      rw [map_inv]; rfl
    rw [this]
    rfl
  show (NearOne s (((sEmb k n x : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k) ∧
        NearOne s ((((sEmb k n x : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k)⁻¹ : GL (Fin (n + 1 + 1)) k) :
          Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k)) ↔
      (NearOne s ((x : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) ∧
        NearOne s (((x : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k))
  rw [e1, e2, nearOne_glEmbMat_iff, nearOne_glEmbMat_iff]

end GlobalTheory.CompanionTheory.BZPhiPG.Onto

end
