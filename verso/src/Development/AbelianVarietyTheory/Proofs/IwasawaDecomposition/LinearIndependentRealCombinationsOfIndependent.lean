import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem linearIndependent_real_combination (g r d : ℕ) (x : Fin r → Fin g → ℂ)
    (e : Fin d → Fin r → ℝ) (hx : LinearIndependent ℝ x) (he : LinearIndependent ℝ e) :
    LinearIndependent ℝ (fun i => ∑ m, (e i m : ℂ) • x m) := by
  rw [Fintype.linearIndependent_iff] at hx he ⊢
  intro c hc
  have hreal : ∀ i, (∑ m, (e i m : ℂ) • x m) = ∑ m, e i m • x m := by
    intro i
    refine Finset.sum_congr rfl fun m _ => ?_
    funext k
    simp [Pi.smul_apply, Complex.real_smul]
  have h1 : ∑ m, (∑ i, c i * e i m) • x m = 0 := by
    have h0 : ∑ i, c i • ∑ m, e i m • x m = 0 := by
      simpa only [hreal] using hc
    rw [← h0]
    simp_rw [Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have h2 := hx _ h1
  refine he c ?_
  funext m
  simpa [Finset.sum_apply, Pi.smul_apply] using h2 m

end GlobalTheory
