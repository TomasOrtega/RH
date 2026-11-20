import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesPresentationUpToOrderTensorProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePowerSeriesOfCompatibleSystemStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Introduce a local definition for the expression. Establish an intermediate fact. Proceed by induction. Treat this case separately. Treat this case separately.

Treat this case separately. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Split into cases according to the possible forms of the given data. Treat this case separately.

Treat this case separately. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem chart_square_presents : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k)
    (c : Chart G d), Presents k c.x₂ c.nil₂ ∧ ∀ z : ∀ n, G.A n ⊗[k] G.A n,
      (∀ n, pullbackTwo (G.res n) (z (n + 1)) = z n) → ∃! s, ∀ n, c.ev₂ n s = z n := by
  intro p k _ d G c
  have ht := fun n => GlobalTheory.T.powerSeriesPresentation_up_to_order_tensorProduct k (Fin d) (Fin d) (G.A n) (G.A n) (c.x n) (c.nil n) (c.x n)
    (c.nil n) (c.nil₂ n) (c.presents.1 n) (c.presents.1 n)
  refine ⟨⟨fun n => (ht n).1, fun N => ?_⟩, fun z hz => ?_⟩
  · obtain ⟨n, hn⟩ := c.presents.2 N
    exact ⟨n, (ht n).2 N hn hn⟩
  · let r : ∀ n, G.A n.succ ⊗[k] G.A n.succ →ₐ[k] G.A n ⊗[k] G.A n := fun n =>
      Algebra.TensorProduct.map (G.res n : G.A (n + 1) →ₐ[k] G.A n)
        (G.res n : G.A (n + 1) →ₐ[k] G.A n)
    have hr : ∀ n t, r n t = pullbackTwo (G.res n) t := fun n t => by
      induction t with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul a b => rfl
    refine GlobalTheory.T.existsUnique_powerSeries_of_compatible_system k (Fin d ⊕ Fin d) (fun n => G.A n ⊗[k] G.A n) c.x₂ c.nil₂ r
      (fun n i => ?_) ⟨fun n => (ht n).1, fun N => ?_⟩ z (fun n => by rw [hr]; exact hz n)
    · rw [hr]
      cases i with
      | inl i => simp [Chart.x₂, c.res]
      | inr i => simp [Chart.x₂, c.res]
    · obtain ⟨n, hn⟩ := c.presents.2 N
      exact ⟨n, (ht n).2 N hn hn⟩

end GlobalTheory
