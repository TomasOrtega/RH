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
Introduce `o Ω _ _ _ S ρ M U₀ EE FinalForm hO z hz`. Rewrite using `[FinalForm.ab]`. Use `show S.TT M z = ⊥`. Establish `hle : M.ringOn U₀ ≤ M.O z` using `RatModel.ringOn_le_O hz`. Establish `hsub : {x | S.th x ≠ 0} ⊆ S.supI M z`.

Introduce `x hx`. Use `⟨hx, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[div_eq_mul_inv]`. Conclude with `mul_mem (hle (hO.le (S.th_mem y))) (hle (hO.th_unit x hx))`. Establish `hHH : S.HH M z = ⊤`.

Rewrite using `[eq_top_iff, ← S.supp]`. Conclude with `AddSubgroup.closure_mono hsub`. Rewrite using `[ThetaSys.TT, hHH, eq_bot_iff]`. Introduce `a ha`. Rewrite using `[AddSubgroup.mem_bot]`.

Establish `h` using `fun b => ha b (AddSubgroup.mem_top b)`. Use function extensionality and compare the values at `j`. Break down `j with i | i` into its components or cases. Use `h (Pi.single (Sum.inr i) 1)` as an intermediate fact. Simplify `this` using `[eStd, Pi.single_apply]`.

Use `h (Pi.single (Sum.inl i) 1)` as an intermediate fact. Simplify `this` using `[eStd, Pi.single_apply]`.
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
