import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumSumEqSumPair
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodMetric.PolyRep

/- English proof (translation)
By extensionality, compare the relevant components. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem lie_tensor {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ σ : PolyRep m) {R : Type} [CommRing R]
    (A : Mat m R) :
    (ρ.tensor σ).lie A = kron (ρ.lie A) 1 + kron 1 (σ.lie A) := by
  ext i j
  obtain ⟨⟨a, c⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨b, d⟩, rfl⟩ := finProdFinEquiv.surjective j
  set X : Mat m (DualNumber R) := fun τ => Matrix.of fun a b =>
    TrivSqZeroExt.inl ((1 : Mat m R) τ a b) + TrivSqZeroExt.inr (A τ a b) with hX
  have h := ev_dual_model (ρ.tensor σ) A (finProdFinEquiv (a, c)) (finProdFinEquiv (b, d))
  have hk : (ρ.tensor σ).ev X = kron (ρ.ev X) (σ.ev X) := evEnt_kron ρ.ent σ.ent X
  rw [hk] at h
  have h2 := congrArg TrivSqZeroExt.snd h
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] at h2
  have hr : (kron (ρ.lie A) (1 : Matrix (Fin σ.M) (Fin σ.M) R) + kron (1 : Matrix (Fin ρ.M) (Fin ρ.M) R) (σ.lie A))
      (finProdFinEquiv (a, c)) (finProdFinEquiv (b, d))
      = ρ.lie A a b * (1 : Matrix (Fin σ.M) (Fin σ.M) R) c d + (1 : Matrix (Fin ρ.M) (Fin ρ.M) R) a b * σ.lie A c d := by
    simp [kron]
  have hl : kron (ρ.ev X) (σ.ev X) (finProdFinEquiv (a, c)) (finProdFinEquiv (b, d)) = ρ.ev X a b * σ.ev X c d := by
    simp [kron]
  rw [hl, ev_dual_model ρ A a b, ev_dual_model σ A c d] at h2
  rw [← h2]
  refine Eq.trans ?_ hr.symm
  simp [TrivSqZeroExt.snd_mul]
  ring

end GlobalTheory.GoodMetric.PolyRep
