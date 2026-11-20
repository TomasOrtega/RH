import Mathlib
import Formalism.LocalToGlobal.Divisibility.ProjLemmas

set_option autoImplicit false

noncomputable section

open NumberField
open scoped Matrix ComplexOrder

namespace GlobalTheory.CentralLevelOp

open Formalism.DivisionValues Formalism.L2.DIV

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem lvlOp_mem_lvlNab : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : NumberField.InfinitePlace K), Formalism.DivisionValues.IsConjAt v0 →
    ∀ (S : Formalism.L2.DIV.CSD K), (S.H.map v0.embedding).PosDef →
    ∀ (G : Type) [Group G] [Fintype G] (r : Representation K G S.Forms), S.ActGood r →
    ∀ (P : Subgroup G) (ψ : P →* Kˣ) (a : MonoidAlgebra K G), (∀ b, a * b = b * a) → (∀ t : G, ∃ n : ℤ, a.coeff t = n) →
    ∀ x ∈ S.lvlNab r P ψ, (S.lvlOp r P ψ a).mulVec x ∈ S.lvlNab r P ψ := by
  intro K _ _ _ v0 h0 S hH G _ _ r hr P ψ a hc hz x hx
  have hE := (level_operator_spec K v0 h0 S hH G r hr P ψ a (hc _)).1
  change (S.lvlE r P ψ).mulVec x ∈ S.nabLat at hx
  change (S.lvlE r P ψ).mulVec ((S.lvlOp r P ψ a).mulVec x) ∈ S.nabLat
  rw [Matrix.mulVec_mulVec, hE, ← Matrix.mulVec_mulVec, CSD.gaMat, Matrix.sum_mulVec]
  refine Submodule.sum_mem _ fun t _ => ?_
  obtain ⟨n, hn⟩ := hz t
  rw [Matrix.smul_mulVec, hn, Int.cast_smul_eq_zsmul]
  exact Submodule.smul_of_tower_mem _ n ((action_preserves_lattice K S G r hr t).1 _ hx)

end GlobalTheory.CentralLevelOp
