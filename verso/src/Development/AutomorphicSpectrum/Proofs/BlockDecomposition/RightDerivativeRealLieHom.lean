import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset

noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.LieAct

variable {n : ℕ}

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Distinguish the cases in `hg : g ∈ GLs n`. Conclude with `h g hg`. Rewrite using `[a.2.2 g hg, b.2.2 g hg]`.
-/
theorem SmF_ext {a b : SmF n} (h : ∀ g ∈ GLs n, a.1 g = b.1 g) : a = b := by
  apply Subtype.ext
  funext g
  by_cases hg : g ∈ GLs n
  · exact h g hg
  · rw [a.2.2 g hg, b.2.2 g hg]

/- English proof (translation)
Establish `hev : (DR Y h).1 =ᶠ[nhds g] Rd Y h.1` using `by filter_upwards [GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.mem_nhds hg] with y hy`. Conclude with `DR_apply Y h hy`. Simplify using `only [Rd]`. Rewrite using `[hev.fderiv_eq]`.
-/
theorem Rd_DR (X Y : Mat n) (h : SmF n) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (DR Y h).1 g = Rd X (Rd Y h.1) g := by
  have hev : (DR Y h).1 =ᶠ[nhds g] Rd Y h.1 := by
    filter_upwards [GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.mem_nhds hg] with y hy
    exact DR_apply Y h hy
  simp only [Rd]
  rw [hev.fderiv_eq]

/- English proof (translation)
Use `LinearMap.ext fun h => SmF_ext fun g hg => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, DR_apply _ _ hg, Rd, Matrix.mul_add, map_add]`.
-/
theorem DR_add (X Y : Mat n) : DR (X + Y) = DR X + DR Y := by
  refine LinearMap.ext fun h => SmF_ext fun g hg => ?_
  simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, DR_apply _ _ hg, Rd, Matrix.mul_add, map_add]

/- English proof (translation)
Use `LinearMap.ext fun h => SmF_ext fun g hg => ?_` and prove the remaining obligations. Establish `e : g * ((r : ℂ) • X) = r • (g * X)`. Use extensionality with `a b`. Simplify using `[Matrix.mul_apply, Finset.mul_sum, Complex.real_smul, mul_left_comm]`. Simplify using `only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, DR_apply _ _ hg, Rd, e, map_smul, Complex.real_smul, smul_eq_mul]`.
-/
theorem DR_smul (r : ℝ) (X : Mat n) : DR ((r : ℂ) • X) = (r : ℂ) • DR X := by
  refine LinearMap.ext fun h => SmF_ext fun g hg => ?_
  have e : g * ((r : ℂ) • X) = r • (g * X) := by
    ext a b
    simp [Matrix.mul_apply, Finset.mul_sum, Complex.real_smul, mul_left_comm]
  simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, DR_apply _ _ hg, Rd, e, map_smul,
    Complex.real_smul, smul_eq_mul]

/- English proof (translation)
Use `LinearMap.ext fun h => SmF_ext fun g hg => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply, DR_apply _ _ hg, Rd_DR _ _ _ hg]`. Conclude with `(GlobalTheory.CompanionTheory.RCalc.Rd_bracket X Y h.2.1 hg).symm`.
-/
theorem DR_bracket (X Y : Mat n) : DR (X * Y - Y * X) = DR X * DR Y - DR Y * DR X := by
  refine LinearMap.ext fun h => SmF_ext fun g hg => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply, DR_apply _ _ hg, Rd_DR _ _ _ hg]
  exact (GlobalTheory.CompanionTheory.RCalc.Rd_bracket X Y h.2.1 hg).symm

/- English proof (translation)
Assemble the required witnesses or components as `⟨DR_add, DR_smul, DR_bracket⟩`.
-/
theorem DR_lie (n : ℕ) : (∀ X Y : Mat n, DR (X + Y) = DR X + DR Y) ∧
    (∀ (r : ℝ) (X : Mat n), DR ((r : ℂ) • X) = (r : ℂ) • DR X) ∧
    (∀ X Y : Mat n, DR (X * Y - Y * X) = DR X * DR Y - DR Y * DR X) :=
  ⟨DR_add, DR_smul, DR_bracket⟩

end GlobalTheory.CompanionTheory.ModelS.LieAct
