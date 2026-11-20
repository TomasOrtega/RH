import Mathlib

/- English proof (translation)
Introduce `l _ K _ _ S hS j F hF x`. Establish `hx : x ∈ Algebra.adjoin ℚ S` using `hS ▸ Algebra.mem_top`. Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem y hy => exact hF y hy`. Consider the case `algebraMap q`.

Rewrite using `[eq_ratCast, map_ratCast]`. Conclude with `SubfieldClass.ratCast_mem F q`. Consider the case `add y z _ _ hy hz`. Rewrite using `[map_add]`. Conclude with `add_mem hy hz`.

Consider the case `mul y z _ _ hy hz`. Rewrite using `[map_mul]`. Conclude with `mul_mem hy hz`.
-/
theorem UpperTheory.Reformulated.B.Qj1.mem_of_adjoin_top.{u_2} :
    ∀ {l : ℕ}
    [inst : Fact (Nat.Prime l)] {K : Type u_2} [inst_1 : Field K] [inst_2 : CharZero K] {S : Set K},
    Algebra.adjoin ℚ S = ⊤ →
      ∀ (j : K →+* PadicAlgCl l) (F : IntermediateField ℚ_[l] (PadicAlgCl l)),
        (∀ s ∈ S, (j : K → PadicAlgCl l) s ∈ F) → ∀ (x : K), (j : K → PadicAlgCl l) x ∈ F := by
  intro l _ K _ _ S hS j F hF x
  have hx : x ∈ Algebra.adjoin ℚ S := hS ▸ Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem y hy => exact hF y hy
  | algebraMap q =>
    rw [eq_ratCast, map_ratCast]
    exact SubfieldClass.ratCast_mem F q
  | add y z _ _ hy hz =>
    rw [map_add]
    exact add_mem hy hz
  | mul y z _ _ hy hz =>
    rw [map_mul]
    exact mul_mem hy hz
