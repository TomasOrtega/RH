import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.InertiaEigenvalues

/- English proof (translation)
Introduce `l _ P ι hC hG K V _ _ ρ`. Use `⟨fun g z => ?_, fun w => ?_, fun v => ?_⟩` and prove the remaining obligations. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b`.

Simplify using `[stRep_tmul, actVdR, hG, P.PD_actdR]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b`.

Simplify using `[crisIncl_tmul, ιV, hC, P.PD_ι]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Simplify using the standard rewrite rules.
-/
theorem lTensor_iota_equivariant : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (ι : Bst P →ₐ[ℚ_[l]] P.R.BdR), (∀ b, ι (Polynomial.C b) = P.ιB b) → (∀ (g : GQ l) (x : Bst P), ι (actSt P g x) = P.actQdR g (ι x)) → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ (g : ↥(GK K)) (z : V ⊗[ℚ_[l]] Bst P), LinearMap.lTensor V ι.toLinearMap (stRep P ρ g z) = actVdR (P.PD K) ρ g (LinearMap.lTensor V ι.toLinearMap z)) ∧ (∀ w : V ⊗[ℚ_[l]] P.R.B, LinearMap.lTensor V ι.toLinearMap (crisIncl P ℚ_[l] V w) = ιV (P.PD K) (LL := ℚ_[l]) (V := V) w) ∧ ∀ v : V, LinearMap.lTensor V ι.toLinearMap (v ⊗ₜ[ℚ_[l]] (1 : Bst P)) = v ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) := by
  intro l _ P ι hC hG K V _ _ ρ
  refine ⟨fun g z => ?_, fun w => ?_, fun v => ?_⟩
  · induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      simp [stRep_tmul, actVdR, hG, P.PD_actdR]
    | add x y hx hy => simp only [map_add, hx, hy]
  · induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      simp [crisIncl_tmul, ιV, hC, P.PD_ι]
    | add x y hx hy => simp only [map_add, hx, hy]
  · simp

end GlobalTheory.InertiaEigenvalues
