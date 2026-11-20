import Mathlib

namespace GlobalTheory.ProductLeftMaps

open TensorProduct

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Both sides reduce to the same expression. Consider the case `tmul x e`. Take `⟨a, b⟩` from `x`.

Simplify using `[Algebra.TensorProduct.map_tmul]`. Consider the case `add x y hx hy`. Rewrite using `[map_add, hx, hy, map_add, map_add]`. Both sides reduce to the same expression.
-/
theorem prodLeft_eq_maps {F A B E : Type} [Field F] [CommRing A] [CommRing B] [CommRing E]
    [Algebra F A] [Algebra F B] [Algebra F E] (z : TensorProduct F (A × B) E) :
    TensorProduct.prodLeft F F A B E z =
      ((Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) :
          TensorProduct F (A × B) E → TensorProduct F A E) z,
       (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) :
          TensorProduct F (A × B) E → TensorProduct F B E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp; rfl
  | tmul x e =>
    obtain ⟨a, b⟩ := x
    simp [Algebra.TensorProduct.map_tmul]
  | add x y hx hy =>
    rw [map_add, hx, hy, map_add, map_add]
    rfl

/- English proof (translation)
Introduce `F A B E _ _ _ _ _ _ _ z h1 h2`. Apply `(TensorProduct.prodLeft F F A B E).injective` to reduce the goal to its premises. Rewrite using `[prodLeft_eq_maps, h1, h2, map_zero]`. Both sides reduce to the same expression.
-/
theorem main : ∀ {F A B E : Type} [inst : Field F] [inst_1 : CommRing A] [inst_2 : CommRing B]
    [inst_3 : CommRing E] [inst_4 : Algebra F A] [inst_5 : Algebra F B] [inst_6 : Algebra F E]
    (z : TensorProduct F (A × B) E),
    (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) :
        TensorProduct F (A × B) E → TensorProduct F A E) z = (0 : TensorProduct F A E) →
    (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) :
        TensorProduct F (A × B) E → TensorProduct F B E) z = (0 : TensorProduct F B E) →
    z = (0 : TensorProduct F (A × B) E) := by
  intro F A B E _ _ _ _ _ _ _ z h1 h2
  apply (TensorProduct.prodLeft F F A B E).injective
  rw [prodLeft_eq_maps, h1, h2, map_zero]
  rfl

end GlobalTheory.ProductLeftMaps
