import Mathlib
open Matrix

namespace GlobalTheory

/- English proof (translation)
Introduce `r k Mq ε hM hε t`. Establish `hU : IsUnit Mq` using `(Matrix.isUnit_iff_isUnit_det Mq).2 (Ne.isUnit hM)`. Establish `hinj : Function.Injective Mq.mulVecLin` using `Matrix.mulVec_injective_iff_isUnit.2 hU`. Establish `hli : LinearIndependent ℚ (fun i => Mq *ᵥ ε i)` using `hε.map' Mq.mulVecLin (LinearMap.ker_eq_bot.2 hinj)`. Set `U : Matrix (Fin k) (Fin r) ℚ` to `Matrix.of fun i => Mq *ᵥ ε i`.

Establish `hrow : LinearIndependent ℚ U.row` using `hli`. Establish `hrank : U.rank = Fintype.card (Fin k)` using `hrow.rank_matrix`. Establish `htop : LinearMap.range U.mulVecLin = ⊤`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Rewrite using `[Module.finrank_fintype_fun_eq_card]`.

Conclude with `hrank`. Take `⟨x, hx⟩` from `LinearMap.range_eq_top.1 htop t`. Use `⟨x, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[dotProduct_comm, ← hx]`. Both sides reduce to the same expression.
-/
theorem exists_dotProduct_mulVec_eq_of_linearIndependent :
    ∀ (r k : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (ε : Fin k → Fin r → ℚ), Mq.det ≠ 0 →
      LinearIndependent ℚ ε → ∀ t : Fin k → ℚ,
      ∃ x : Fin r → ℚ, ∀ i, x ⬝ᵥ Mq *ᵥ ε i = t i := by
  intro r k Mq ε hM hε t
  have hU : IsUnit Mq := (Matrix.isUnit_iff_isUnit_det Mq).2 (Ne.isUnit hM)
  have hinj : Function.Injective Mq.mulVecLin := Matrix.mulVec_injective_iff_isUnit.2 hU
  have hli : LinearIndependent ℚ (fun i => Mq *ᵥ ε i) :=
    hε.map' Mq.mulVecLin (LinearMap.ker_eq_bot.2 hinj)
  let U : Matrix (Fin k) (Fin r) ℚ := Matrix.of fun i => Mq *ᵥ ε i
  have hrow : LinearIndependent ℚ U.row := hli
  have hrank : U.rank = Fintype.card (Fin k) := hrow.rank_matrix
  have htop : LinearMap.range U.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fintype_fun_eq_card]
    exact hrank
  obtain ⟨x, hx⟩ := LinearMap.range_eq_top.1 htop t
  refine ⟨x, fun i => ?_⟩
  rw [dotProduct_comm, ← hx]
  rfl

end GlobalTheory
