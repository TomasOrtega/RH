import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
open Formalism.REAL Finset
namespace GlobalTheory

/- English proof (translation)
Introduce `t`. Proceed by induction on `t with`. Consider the case `zero => intro f g _ w`. Simplify using the standard rewrite rules. Consider the case `succ t ih`.

Introduce `f g h w`. Simplify using `only [List.ofFn_succ, List.prod_cons, Module.End.mul_apply]`. Rewrite using `[h, ih (fun i => f i.succ) (fun i => g i.succ) (fun k => h k.succ)]`.
-/
theorem ofFn_prod_intertwine {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ι : W →ₗ[ℂ] V) : ∀ (t : ℕ) (f : Fin t → Module.End ℂ V)
    (g : Fin t → Module.End ℂ W), (∀ k w, ι (g k w) = f k (ι w)) →
    ∀ w, ι ((List.ofFn g).prod w) = (List.ofFn f).prod (ι w) := by
  intro t
  induction t with
  | zero => intro f g _ w; simp
  | succ t ih =>
    intro f g h w
    simp only [List.ofFn_succ, List.prod_cons, Module.End.mul_apply]
    rw [h, ih (fun i => f i.succ) (fun i => g i.succ) (fun k => h k.succ)]

/- English proof (translation)
Introduce `V W _ _ _ _ n t E E' ι h a b u w`. Establish `hT : ∀ (u : ℂ) (a b : Fin n) (w : W), ι (Tm E' u a b w) = Tm E u a b (ι w)`. Introduce `u a b w`. Unfold `Tm`. Apply the tactic sequence `split_ifs <;> simp [h, Module.algebraMap_end_apply]`.

Unfold `qminor`. Rewrite using `[LinearMap.sum_apply, LinearMap.sum_apply, map_sum]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Module.End.mul_apply, Module.End.mul_apply, Module.End.intCast_apply, Module.End.intCast_apply, map_zsmul]`. Use `congr 1`.

Conclude with `ofFn_prod_intertwine ι t _ _ (fun k w => hT _ _ _ w) w`.
-/
theorem qminor_intertwine : ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (n t : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (E' : Fin n → Fin n → Module.End ℂ W) (ι : W →ₗ[ℂ] V), (∀ a b w, ι (E' a b w) = E a b (ι w)) → ∀ (a b : Fin t → Fin n) (u : ℂ) (w : W), ι (qminor E' a b u w) = qminor E a b u (ι w) := by
  intro V W _ _ _ _ n t E E' ι h a b u w
  have hT : ∀ (u : ℂ) (a b : Fin n) (w : W), ι (Tm E' u a b w) = Tm E u a b (ι w) := by
    intro u a b w
    unfold Tm
    split_ifs <;> simp [h, Module.algebraMap_end_apply]
  unfold qminor
  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.intCast_apply,
    Module.End.intCast_apply, map_zsmul]
  congr 1
  exact ofFn_prod_intertwine ι t _ _ (fun k w => hT _ _ _ w) w

end GlobalTheory
