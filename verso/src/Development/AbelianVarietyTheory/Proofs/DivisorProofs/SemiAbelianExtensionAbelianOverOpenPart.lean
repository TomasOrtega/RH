import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteLocalBaseAtClosedPointGroupImports
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
namespace GlobalTheory.ZH

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem abLocus_of_over₀ : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → (U₀ : Set M.Z) ⊆ abLocus FinalForm.G := by
  intro o Ω _ _ _ S ρ M U₀ EE FinalForm hO z hz
  rw [FinalForm.ab]
  show S.TT M z = ⊥
  have hle : M.ringOn U₀ ≤ M.O z := RatModel.ringOn_le_O hz
  have hsub : {x | S.th x ≠ 0} ⊆ S.supI M z := by
    intro x hx
    refine ⟨hx, fun y => ?_⟩
    rw [div_eq_mul_inv]
    exact mul_mem (hle (hO.le (S.th_mem y))) (hle (hO.th_unit x hx))
  have hHH : S.HH M z = ⊤ := by
    rw [eq_top_iff, ← S.supp]
    exact AddSubgroup.closure_mono hsub
  rw [ThetaSys.TT, hHH, eq_bot_iff]
  intro a ha
  rw [AddSubgroup.mem_bot]
  have h := fun b => ha b (AddSubgroup.mem_top b)
  funext j
  rcases j with i | i
  · have := h (Pi.single (Sum.inr i) 1)
    simpa [eStd, Pi.single_apply] using this
  · have := h (Pi.single (Sum.inl i) 1)
    simpa [eStd, Pi.single_apply] using this

end GlobalTheory.ZH
