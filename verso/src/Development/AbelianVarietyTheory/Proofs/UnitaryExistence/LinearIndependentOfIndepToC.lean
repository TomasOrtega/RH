import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.TieUpA
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.BaseChangeTensorProduct
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ReadingComparison

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps
  ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke

section General

variable {K L : Type} [Field K] [Field L] [Algebra K L] {σ : K →+* ℂ} {σ' : L →+* ℂ}
  {C W : Type} [AddCommGroup C] [Module K C] [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem bcMap_tmul (hσ : ∀ a, σ' (algebraMap K L a) = σ a) (f : C →ₛₗ[σ] W) (t : L) (x : C) :
    BaseChangeTensorProduct.bcMap hσ f (t ⊗ₜ x) = σ' t • f x := rfl

/- English proof (translation)
Rewrite using `[linearIndependent_iff_finset_linearIndependent]`. Introduce `s`. Establish `e` using `s.equivFin`. Establish `h1` using `hf _ (fun i => b (e.symm i).1) (hb.comp (fun i => (e.symm i).1) (Subtype.val_injective.comp e.symm.injective))`. Establish `h2` using `h1.comp e e.injective`.

Use `h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.
-/
theorem linearIndependent_of_indepToC {f : C →ₛₗ[σ] W} (hf : IndepToC f) {ι : Type} {b : ι → C}
    (hb : LinearIndependent K b) : LinearIndependent ℂ (fun i => f (b i)) := by
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  have e := s.equivFin
  have h1 := hf _ (fun i => b (e.symm i).1) (hb.comp (fun i => (e.symm i).1)
    (Subtype.val_injective.comp e.symm.injective))
  have h2 := h1.comp e e.injective
  convert h2 using 1
  funext i
  simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h n b hb`. Establish `h1` using `h n (fun i => (1 : L) ⊗ₜ[K] b i) (Module.Flat.linearIndependent_one_tmul hb)`. Simplify `h1` using `only [bcMap_tmul, map_one, one_smul]`. Introduce `h n b hb`.

Use `letI : Algebra K ℂ := σ.toAlgebra`. Use `letI : Algebra L ℂ := σ'.toAlgebra`. Use `haveI : IsScalarTower K L ℂ := IsScalarTower.of_algebraMap_eq fun a => (hσ a).symm`. Use `letI : Module K W := Module.compHom W σ`. Use `haveI : IsScalarTower K ℂ W := ⟨fun a z w => by show (σ a * z) • w = σ a • z • w`.

Rewrite using `[mul_smul]⟩`. Set `g : C →ₗ[K] W` to `{ toFun := f, map_add' := map_add f, map_smul' := fun a x => f.map_smulₛₗ a x }`. Set `F : ℂ ⊗[K] C →ₗ[ℂ] W` to `g.liftBaseChange ℂ`. Set `e` to `Module.Basis.ofVectorSpace K C`. Establish `hF : Function.Injective F`.

Use `LinearMap.injective_of_linearIndependent (Algebra.TensorProduct.basis ℂ e).span_eq ?_` and prove the remaining obligations. Establish `h0` using `linearIndependent_of_indepToC h e.linearIndependent`. Establish `e1 : (F ∘ Algebra.TensorProduct.basis ℂ e) = fun i => f (e i)`. Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp, Algebra.TensorProduct.basis_apply, F, LinearMap.liftBaseChange_one_tmul]`.

Both sides reduce to the same expression. Rewrite using `[e1]`. Conclude with `h0`. Set `φ` to `TensorProduct.AlgebraTensorModule.cancelBaseChange K L ℂ ℂ C`. Establish `h1 : LinearIndependent ℂ (fun i => (1 : ℂ) ⊗ₜ[L] b i)` using `Module.Flat.linearIndependent_one_tmul hb`.

Establish `h2` using `h1.map' (F ∘ₗ φ.toLinearMap) (LinearMap.ker_eq_bot.2 (hF.comp φ.injective))`. Establish `key : ∀ x : L ⊗[K] C, F (φ ((1 : ℂ) ⊗ₜ[L] x)) = BaseChangeTensorProduct.bcMap hσ f x`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul t x`. Rewrite using `[bcMap_tmul]`. Simplify using `only [φ, F, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.liftBaseChange_tmul]`. Use `show (σ' t * 1) • f x = _`. Rewrite using `[mul_one]`.

Consider the case `add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy, map_add]`. Establish `e2 : (fun i => BaseChangeTensorProduct.bcMap hσ f (b i)) = (F ∘ₗ φ.toLinearMap) ∘ fun i => (1 : ℂ) ⊗ₜ[L] b i`. Use function extensionality and compare the values at `fun i => (key (b i)).symm`. Rewrite using `[e2]`. Conclude with `h2`.
-/
theorem indepToC_bcMap_iff (hσ : ∀ a, σ' (algebraMap K L a) = σ a) (f : C →ₛₗ[σ] W) :
    IndepToC (BaseChangeTensorProduct.bcMap hσ f) ↔ IndepToC f := by
  constructor
  · intro h n b hb
    have h1 := h n (fun i => (1 : L) ⊗ₜ[K] b i) (Module.Flat.linearIndependent_one_tmul hb)
    simpa only [bcMap_tmul, map_one, one_smul] using h1
  · intro h n b hb
    letI : Algebra K ℂ := σ.toAlgebra
    letI : Algebra L ℂ := σ'.toAlgebra
    haveI : IsScalarTower K L ℂ := IsScalarTower.of_algebraMap_eq fun a => (hσ a).symm
    letI : Module K W := Module.compHom W σ
    haveI : IsScalarTower K ℂ W := ⟨fun a z w => by
      show (σ a * z) • w = σ a • z • w
      rw [mul_smul]⟩
    let g : C →ₗ[K] W :=
      { toFun := f, map_add' := map_add f, map_smul' := fun a x => f.map_smulₛₗ a x }
    let F : ℂ ⊗[K] C →ₗ[ℂ] W := g.liftBaseChange ℂ
    let e := Module.Basis.ofVectorSpace K C
    have hF : Function.Injective F := by
      refine LinearMap.injective_of_linearIndependent (Algebra.TensorProduct.basis ℂ e).span_eq ?_
      have h0 := linearIndependent_of_indepToC h e.linearIndependent
      have e1 : (F ∘ Algebra.TensorProduct.basis ℂ e) = fun i => f (e i) := by
        funext i
        simp only [Function.comp, Algebra.TensorProduct.basis_apply, F, LinearMap.liftBaseChange_one_tmul]
        rfl
      rw [e1]; exact h0
    let φ := TensorProduct.AlgebraTensorModule.cancelBaseChange K L ℂ ℂ C
    have h1 : LinearIndependent ℂ (fun i => (1 : ℂ) ⊗ₜ[L] b i) := Module.Flat.linearIndependent_one_tmul hb
    have h2 := h1.map' (F ∘ₗ φ.toLinearMap) (LinearMap.ker_eq_bot.2 (hF.comp φ.injective))
    have key : ∀ x : L ⊗[K] C, F (φ ((1 : ℂ) ⊗ₜ[L] x)) = BaseChangeTensorProduct.bcMap hσ f x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul t x =>
        rw [bcMap_tmul]
        simp only [φ, F, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.liftBaseChange_tmul]
        show (σ' t * 1) • f x = _
        rw [mul_one]
      | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy, map_add]
    have e2 : (fun i => BaseChangeTensorProduct.bcMap hσ f (b i)) = (F ∘ₗ φ.toLinearMap) ∘ fun i => (1 : ℂ) ⊗ₜ[L] b i :=
      funext fun i => (key (b i)).symm
    rw [e2]; exact h2

end General

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ)

end GlobalTheory.ReadingComparison
