import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeviRep

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `V _ _ Bf hsymm hpos v w`. Set `c : PreInnerProductSpace.Core ℂ V` to `{ inner := fun x y => Bf y x conj_inner_symm := fun x y => by show starRingEnd ℂ (Bf x y) = Bf y x`. Rewrite using `[hsymm x y]`. Use `re_inner_nonneg := fun x => by show 0 ≤ RCLike.re (Bf x x)`. Distinguish the cases in `hx : x = 0`.

Substitute `hx` using the available equality. Simplify using the standard rewrite rules. Conclude with `(hpos x hx).le`. Use `add_left := fun x y z => by show Bf z (x + y) = Bf z x + Bf z y`. Conclude with `map_add _ _ _`.

Use `smul_left := fun x y r => by show Bf y (r • x) = starRingEnd ℂ r * Bf y x`. Rewrite using `[LinearMap.map_smulₛₗ, smul_eq_mul] }`. Establish `h` using `@InnerProductSpace.Core.inner_mul_inner_self_le ℂ V _ _ _ c v w`. Express the relevant statement in the definitionally equal form `‖Bf w v‖ * ‖Bf v w‖ ≤ RCLike.re (Bf v v) * RCLike.re (Bf w w) at h`. Rewrite `h` using `[hsymm v w, RCLike.norm_conj]`.

Rewrite using `[sq]`. Conclude with `h`.
-/
theorem hermitianForm_norm_sq_le_re_mul_re :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
    (∀ v w, Bf w v = starRingEnd ℂ (Bf v w)) → (∀ v, v ≠ 0 → 0 < (Bf v v).re) →
    ∀ v w, ‖Bf v w‖ ^ 2 ≤ (Bf v v).re * (Bf w w).re := by
  intro V _ _ Bf hsymm hpos v w
  let c : PreInnerProductSpace.Core ℂ V :=
    { inner := fun x y => Bf y x
      conj_inner_symm := fun x y => by
        show starRingEnd ℂ (Bf x y) = Bf y x
        rw [hsymm x y]
      re_inner_nonneg := fun x => by
        show 0 ≤ RCLike.re (Bf x x)
        by_cases hx : x = 0
        · subst hx; simp
        · exact (hpos x hx).le
      add_left := fun x y z => by
        show Bf z (x + y) = Bf z x + Bf z y
        exact map_add _ _ _
      smul_left := fun x y r => by
        show Bf y (r • x) = starRingEnd ℂ r * Bf y x
        rw [LinearMap.map_smulₛₗ, smul_eq_mul] }
  have h := @InnerProductSpace.Core.inner_mul_inner_self_le ℂ V _ _ _ c v w
  change ‖Bf w v‖ * ‖Bf v w‖ ≤ RCLike.re (Bf v v) * RCLike.re (Bf w w) at h
  rw [hsymm v w, RCLike.norm_conj] at h
  rw [sq]
  exact h

end GlobalTheory
