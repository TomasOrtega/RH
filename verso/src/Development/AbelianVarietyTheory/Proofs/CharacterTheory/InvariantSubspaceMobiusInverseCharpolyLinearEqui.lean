import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

open Polynomial in

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intros`. Both sides reduce to the same expression. Consider the case `succ n ih`. Introduce `V V' _ _ _ _ _ _ e g`.

Rewrite using `[_root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_succ, _root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_succ, e.charpoly_conj]`. Use `congr 1`. Set `σ : {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W} ≃ {W : Submodule F V' // W ≠ ⊤ ∧ ∀ x ∈ W, e.conj g x ∈ W}` to `(Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv fun W => by`. Express the relevant statement in the definitionally equal form `_ ↔ (Submodule.orderIsoMapComap e W ≠ ⊤ ∧ ∀ y ∈ W.map (e : V →ₗ[F] V'), e.conj g y ∈ W.map (e : V →ₗ[F] V'))`. Use `and_congr ?_ ⟨fun h y hy => ?_, fun h x hx => ?_⟩` and prove the remaining obligations.

Conclude with `((Submodule.orderIsoMapComap e).injective.ne_iff' (map_top _)).symm`. Take `⟨x, hx, rfl⟩` from `Submodule.mem_map.mp hy`. Simplify `Submodule.mem_map_of_mem (f := (e : V →ₗ[F] V')) (h x hx)` using `[LinearEquiv.conj_apply]`. Use `h (e x) (Submodule.mem_map_of_mem hx)` as an intermediate fact. Simplify `this` using `[LinearEquiv.conj_apply, Submodule.mem_map_equiv]`.

Rewrite using `[← finsum_comp_equiv σ]`. Use `finsum_congr fun W => ?_` and prove the remaining obligations. Rewrite using `[← ih W.1 (W.1.map (e : V →ₗ[F] V')) (e.submoduleMap W.1)]`. Use `show _root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec s n (W.1.map (e : V →ₗ[F] V')) _ = _`. Use `congr 1`.
-/
theorem _root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_linearEquiv_conj {F : Type} [Field F]
    (s : F[X] → ℂ) (n : ℕ) :
    ∀ (V V' : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [AddCommGroup V']
      [Module F V'] [FiniteDimensional F V'] (e : V ≃ₗ[F] V') (g : Module.End F V),
      _root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec s n V' (e.conj g) =
        _root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec s n V g := by
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro V V' _ _ _ _ _ _ e g
    rw [_root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_succ, _root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_succ,
      e.charpoly_conj]
    congr 1
    let σ : {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W} ≃
        {W : Submodule F V' // W ≠ ⊤ ∧ ∀ x ∈ W, e.conj g x ∈ W} :=
      (Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv fun W => by
        change _ ↔ (Submodule.orderIsoMapComap e W ≠ ⊤ ∧
          ∀ y ∈ W.map (e : V →ₗ[F] V'), e.conj g y ∈ W.map (e : V →ₗ[F] V'))
        refine and_congr ?_ ⟨fun h y hy => ?_, fun h x hx => ?_⟩
        · exact ((Submodule.orderIsoMapComap e).injective.ne_iff' (map_top _)).symm
        · obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
          simpa [LinearEquiv.conj_apply] using
            Submodule.mem_map_of_mem (f := (e : V →ₗ[F] V')) (h x hx)
        · have := h (e x) (Submodule.mem_map_of_mem hx)
          simpa [LinearEquiv.conj_apply, Submodule.mem_map_equiv] using this
    rw [← finsum_comp_equiv σ]
    refine finsum_congr fun W => ?_
    rw [← ih W.1 (W.1.map (e : V →ₗ[F] V')) (e.submoduleMap W.1)]
    show _root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec s n (W.1.map (e : V →ₗ[F] V')) _ = _
    congr 1

open Polynomial in

/- English proof (translation)
Unfold `_root_.GlobalTheory.CuspGL.psi`. Rewrite using `[← e.finrank_eq]`. Conclude with `_root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_linearEquiv_conj s _ V V' e g`.
-/
theorem _root_.GlobalTheory.CuspGL.psi_conj (F : Type) [Field F]
    (s : F[X] → ℂ) (V V' : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V']
    (e : V ≃ₗ[F] V') (g : Module.End F V) :
    _root_.GlobalTheory.CuspGL.psi s V' (e.conj g) =
      _root_.GlobalTheory.CuspGL.psi s V g := by
  unfold _root_.GlobalTheory.CuspGL.psi
  rw [← e.finrank_eq]
  exact _root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_linearEquiv_conj s _ V V' e g

end GlobalTheory.CuspGL
