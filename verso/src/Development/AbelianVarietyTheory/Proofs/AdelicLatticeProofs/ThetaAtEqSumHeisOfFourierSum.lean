import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem isSBHalf_halfInd {D : D7} {m n : ℕ} (e : AE D) (Λ : AddSubgroup (Mx D m n)) :
    IsSBHalf e Λ (halfInd e Λ) := by
  classical
  refine ⟨fun t ht => ?_, 1, one_pos, fun u hu hh t => ?_, fun t ht => ?_⟩
  · by_contra h
    exact ht (by simp [halfInd, h])
  · have : (t + 1 • u ∈ Λ ∧ IsHalf e (t + 1 • u)) ↔ (t ∈ Λ ∧ IsHalf e t) := by
      rw [one_smul, Λ.add_mem_cancel_right hu]
      refine and_congr_right fun _ => forall_congr' fun i => forall_congr' fun j => ?_
      rw [Matrix.add_apply, mul_add, hh i j, add_left_inj]
    simp only [halfInd, this]
  · by_contra h
    rw [one_smul] at h
    exact ht (by simp [halfInd, h])

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem thetaAt_eq_sum_heis_of_fourier_sum :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (Λ : AddSubgroup (WO S T)) (f₀ Φ f : WO S T → ℂ) (Y : Finset (WO S T)) (a : WO S T → ℂ), IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ f → (∀ u ∈ Λ, u.map (fun z => e * z) ∈ Λ) → (∀ y ∈ Y, IsHalf (cA D e) y) → (∀ t, Φ t = halfInd e Λ t * ∑ y ∈ Y, a y * ψ (symplO S T t y)) → f = ∑ y ∈ Y, a y • heisO ψ S T y f₀ := by
  intro D ψ S T e Λ f₀ Φ f Y a hθ _ hY hΦ
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hθ
  have hΦ' : Φ = ∑ y ∈ Y, a y • fun t => ψ (symplO S T t y) * halfInd e Λ t := by
    funext t
    rw [hΦ t, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hvac : Tm (halfInd e Λ) = f₀ := by simpa using hTm.vac
  rw [hall Tm hTm, hΦ', map_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [map_smul, hTm.modul _ (isSBHalf_halfInd e Λ) y (hY y hy), hvac]

end GlobalTheory
