import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `l _ k _ _ _`. Rewrite using `[pow_one]`. Set `_ : Algebra (ZMod l) k` to `ZMod.algebra k l`. Establish `hnd` using `traceForm_nondegenerate (ZMod l) k`. Set `b` to `Module.finBasis (ZMod l) k`.

Set `d` to `(Algebra.traceForm (ZMod l) k).dualBasis hnd b`. Use `⟨(Algebra.trace (ZMod l) k).toAddMonoidHom, ?_, Module.finrank (ZMod l) k, b, d, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Apply `hnd.1 x` to reduce the goal to its premises. Introduce `y`.

Rewrite using `[Algebra.traceForm_apply, mul_comm]`. Conclude with `hx y`. Introduce `z conv_lhs => rw [← d.sum_repr z]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, mul_comm z (b j)]`.

Simplify using `only [LinearMap.toAddMonoidHom_coe]`. Take `⟨c, hc⟩ : ∃ c, Algebra.trace (ZMod l) k (b j * z) = c` from `⟨_, rfl⟩`. Rewrite using `[hc]`. Use `conv_lhs => rw [← ZMod.natCast_zmod_val c]`. Rewrite using `[Nat.cast_smul_eq_nsmul, nsmul_eq_mul]`.
-/
theorem finiteField_exists_traceForm_dualBases_pow_one :
    ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k] [CharP k l],
      ∃ t : k →+ ZMod (l ^ 1), (∀ b, (∀ a, t (a * b) = 0) → b = 0) ∧
        ∃ (n : ℕ) (a e : Fin n → k), ∀ z, z = ∑ j, ((t (a j * z)).val : k) * e j := by
  intro l _ k _ _ _
  rw [pow_one]
  let _ : Algebra (ZMod l) k := ZMod.algebra k l
  have hnd := traceForm_nondegenerate (ZMod l) k
  let b := Module.finBasis (ZMod l) k
  let d := (Algebra.traceForm (ZMod l) k).dualBasis hnd b
  refine ⟨(Algebra.trace (ZMod l) k).toAddMonoidHom, ?_, Module.finrank (ZMod l) k, b, d, ?_⟩
  · intro x hx
    apply hnd.1 x
    intro y
    rw [Algebra.traceForm_apply, mul_comm]
    exact hx y
  · intro z
    conv_lhs => rw [← d.sum_repr z]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, mul_comm z (b j)]
    simp only [LinearMap.toAddMonoidHom_coe]
    obtain ⟨c, hc⟩ : ∃ c, Algebra.trace (ZMod l) k (b j * z) = c := ⟨_, rfl⟩
    rw [hc]
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

end GlobalTheory
