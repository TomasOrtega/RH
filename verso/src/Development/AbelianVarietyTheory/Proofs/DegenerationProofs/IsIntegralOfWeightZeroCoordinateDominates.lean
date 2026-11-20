import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuationEqPolarFormOfWeightZeroMaxStatement
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

/- English proof (translation)
Introduce `p _ V _ j G _ g N N' X _ q H J _ σ cls m hB a w ha hw hi`. Take `⟨ν, hν, hc⟩` from `m.ser a ha w hw`. Apply `hc` to reduce the goal to its premises. Set `e : m.Φ.E.X ≃ₗ[ℤ] X` to `m.xe.toIntLinearEquiv`. Establish `: Module.Free ℤ X` using `Module.Free.of_equiv e`.

Establish `: Module.Finite ℤ X` using `Module.Finite.equiv e`. Establish `hq : ∀ x : X, (q.comp m.xe.toIntLinearEquiv.toLinearMap) (m.xe.symm x) = q x`. Introduce `x`. Rewrite using `[QuadraticMap.comp_apply]`. Conclude with `congrArg q (m.xe.apply_symm_apply x)`.

Use `GlobalTheory.T.valuation_eq_polarForm_of_weightZero_max X q g N J cls p w ν ?_ ?_ hB.lll ?_ hν hi` and prove the remaining obligations. Establish `h` using `m.good.pos.comp (m.xe.symm.injective.tendsto_cofinite)`. Conclude with `h.congr hq`. Conclude with `e.finrank_eq.symm.le.trans ((Nat.le_add_left _ _).trans m.dim.le)`. Introduce `i n`.

Establish `h` using `m.good.short i (m.xe.symm n)`. Rewrite `h` using `[← map_nsmul, ← map_add, hq, hq]`. Conclude with `h`.
-/
theorem Mod.integral_of_weight_zero_dominates : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] (j : V →+* OO p) (G : Over (Sp V)) [GrpObj G] (g N N' : ℕ) (X : Type) [AddCommGroup X] (q : QuadraticMap ℤ X ℝ) (H : LB G.left) (J : Type) [Fintype J] (σ : J → H.Sec) (cls : J → X) (m : Mod p j G g N q H σ cls), Big g N N' → ∀ (a : Sp (PadicAlgCl p) ⟶ G.left) (w : J → PadicAlgCl p), a ≫ G.hom = gPt p ≫ spMap j → Crd H σ a w → (∃ i₀, cls i₀ = 0 ∧ ∀ i, ‖w i‖ ≤ ‖w i₀‖) → ∃ c : Sp (OO p) ⟶ G.left, c ≫ G.hom = spMap j ∧ gPt p ≫ c = a := by
  intro p _ V _ j G _ g N N' X _ q H J _ σ cls m hB a w ha hw hi
  obtain ⟨ν, hν, hc⟩ := m.ser a ha w hw
  apply hc
  let e : m.Φ.E.X ≃ₗ[ℤ] X := m.xe.toIntLinearEquiv
  have : Module.Free ℤ X := Module.Free.of_equiv e
  have : Module.Finite ℤ X := Module.Finite.equiv e
  have hq : ∀ x : X, (q.comp m.xe.toIntLinearEquiv.toLinearMap) (m.xe.symm x) = q x := by
    intro x
    rw [QuadraticMap.comp_apply]
    exact congrArg q (m.xe.apply_symm_apply x)
  refine GlobalTheory.T.valuation_eq_polarForm_of_weightZero_max X q g N J cls p w ν ?_ ?_ hB.lll ?_ hν hi
  · have h := m.good.pos.comp (m.xe.symm.injective.tendsto_cofinite)
    exact h.congr hq
  · exact e.finrank_eq.symm.le.trans ((Nat.le_add_left _ _).trans m.dim.le)
  · intro i n
    have h := m.good.short i (m.xe.symm n)
    rw [← map_nsmul, ← map_add, hq, hq] at h
    exact h

end GlobalTheory.ZH
