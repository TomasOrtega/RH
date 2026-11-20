import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentEvalCommutesSubstAndAlgebraMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePowerSeriesOfCompatibleSystemStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz.Chart

/- English proof (translation)
Introduce `p k _ d G c`. Use `⟨fun n f => ?_, fun n s => ?_, fun b hb => ?_⟩` and prove the remaining obligations. Conclude with `(GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A (n + 1))).2 (G.A n) (G.res n : G.A (n + 1) →ₐ[k] G.A n) (c.x (n + 1)) (c.nil (n + 1)) (c.x n) (c.nil n) (fun i => c.res n i) f`. Set `g : G.A (n + 1) →ₐ[k] G.A n` to `G.res n`. Establish `h` using `(GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d ⊕ Fin d) (G.A (n + 1) ⊗[k] G.A (n + 1))).2 (G.A n ⊗[k] G.A n) (Algebra.TensorProduct.map g g) (c.x₂ (n + 1)) (c.nil₂ (n + 1)) (c.x₂ n) (c.nil₂ n) (fun i => by`.

Consider the cases of `i with`. Consider the case `inl i => simp [x₂, g, c.res n i]`. Consider the case `inr i => simp [x₂, g, c.res n i]) s`. Use `Eq.trans ?_ h` and prove the remaining obligations. Both sides reduce to the same expression.

Conclude with `GlobalTheory.T.existsUnique_powerSeries_of_compatible_system k (Fin d) G.A c.x c.nil (fun n => (G.res n : G.A (n + 1) →ₐ[k] G.A n)) (fun n i => c.res n i) c.presents b hb`.
-/
theorem functions_are_series : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k)
    (c : Chart G d), (∀ n f, G.res n (c.ev (n + 1) f) = c.ev n f) ∧
    (∀ n s, pullbackTwo (G.res n) (c.ev₂ (n + 1) s) = c.ev₂ n s) ∧
    ∀ b : ∀ n, G.A n, (∀ n, G.res n (b (n + 1)) = b n) → ∃! f, ∀ n, c.ev n f = b n := by
  intro p k _ d G c
  refine ⟨fun n f => ?_, fun n s => ?_, fun b hb => ?_⟩
  · exact (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d) (G.A (n + 1))).2 (G.A n) (G.res n : G.A (n + 1) →ₐ[k] G.A n)
      (c.x (n + 1)) (c.nil (n + 1)) (c.x n) (c.nil n) (fun i => c.res n i) f
  · let g : G.A (n + 1) →ₐ[k] G.A n := G.res n
    have h := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d ⊕ Fin d) (G.A (n + 1) ⊗[k] G.A (n + 1))).2
      (G.A n ⊗[k] G.A n) (Algebra.TensorProduct.map g g)
      (c.x₂ (n + 1)) (c.nil₂ (n + 1)) (c.x₂ n) (c.nil₂ n) (fun i => by
        cases i with
        | inl i => simp [x₂, g, c.res n i]
        | inr i => simp [x₂, g, c.res n i]) s
    refine Eq.trans ?_ h
    rfl
  · exact GlobalTheory.T.existsUnique_powerSeries_of_compatible_system k (Fin d) G.A c.x c.nil (fun n => (G.res n : G.A (n + 1) →ₐ[k] G.A n))
      (fun n i => c.res n i) c.presents b hb

end GlobalTheory.Katz.Chart
