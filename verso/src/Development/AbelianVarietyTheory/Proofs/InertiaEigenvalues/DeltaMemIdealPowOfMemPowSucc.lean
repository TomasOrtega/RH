import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Introduce `l hl A _ D J hlJ n`. Establish `hl0 : 0 < l` using `hl.out.pos`. Proceed by induction on `n with`. Consider the case `zero => intro x _`. Simplify using the standard rewrite rules.

Consider the case `succ n ih`. Introduce `x hx`. Establish `key : x ∈ J ^ (n + 1 + 1) ∧ D.δ x ∈ J ^ (n + 1)`. Rewrite `hx` using `[pow_succ' J (n + 1)]`. Use `Submodule.mul_induction_on hx ?_ ?_` and prove the remaining obligations.

Introduce `a ha b hb`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ' J (n + 1)]`. Conclude with `Ideal.mul_mem_mul ha hb`. Rewrite using `[D.δ_mul]`.

Establish `h1 : a ^ l * D.δ b ∈ J ^ (n + 1)`. Rewrite using `[pow_succ']`. Conclude with `Ideal.mul_mem_mul (Ideal.pow_mem_of_mem J ha l hl0) (ih b hb)`. Establish `h2 : b ^ l * D.δ a ∈ J ^ (n + 1)` using `Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hb l hl0)`. Establish `h3 : (l : A) * D.δ a * D.δ b ∈ J ^ (n + 1)`.

Rewrite using `[pow_succ']`. Conclude with `Ideal.mul_mem_mul (Ideal.mul_mem_right _ _ hlJ) (ih b hb)`. Conclude with `Ideal.add_mem _ (Ideal.add_mem _ h1 h2) h3`. Introduce and unpack `y z ⟨hy1, hy2⟩ ⟨hz1, hz2⟩`. Use `⟨Ideal.add_mem _ hy1 hz1, ?_⟩` and prove the remaining obligations.

Rewrite using `[D.δ_add]`. Use `Ideal.sub_mem _ (Ideal.add_mem _ hy2 hz2) (Ideal.sum_mem _ fun k hk => ?_)` and prove the remaining obligations. Establish `hk0 : 0 < k` using `(Finset.mem_Ioo.1 hk).1`. Establish `hyk : y ^ k ∈ J ^ (n + 1)` using `Ideal.pow_le_pow_right (Nat.le_succ _) (Ideal.pow_mem_of_mem _ hy1 k hk0)`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hyk)`.

Conclude with `key.2`.
-/
theorem delta_pow_succ_mem_pow : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (J : Ideal A),
    (l : A) ∈ J → ∀ (n : ℕ), ∀ x ∈ J ^ (n + 1), D.δ x ∈ J ^ n := by
  intro l hl A _ D J hlJ n
  have hl0 : 0 < l := hl.out.pos
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    have key : x ∈ J ^ (n + 1 + 1) ∧ D.δ x ∈ J ^ (n + 1) := by
      rw [pow_succ' J (n + 1)] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha b hb
        refine ⟨?_, ?_⟩
        · rw [pow_succ' J (n + 1)]; exact Ideal.mul_mem_mul ha hb
        · rw [D.δ_mul]
          have h1 : a ^ l * D.δ b ∈ J ^ (n + 1) := by
            rw [pow_succ']; exact Ideal.mul_mem_mul (Ideal.pow_mem_of_mem J ha l hl0) (ih b hb)
          have h2 : b ^ l * D.δ a ∈ J ^ (n + 1) :=
            Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hb l hl0)
          have h3 : (l : A) * D.δ a * D.δ b ∈ J ^ (n + 1) := by
            rw [pow_succ']; exact Ideal.mul_mem_mul (Ideal.mul_mem_right _ _ hlJ) (ih b hb)
          exact Ideal.add_mem _ (Ideal.add_mem _ h1 h2) h3
      · rintro y z ⟨hy1, hy2⟩ ⟨hz1, hz2⟩
        refine ⟨Ideal.add_mem _ hy1 hz1, ?_⟩
        rw [D.δ_add]
        refine Ideal.sub_mem _ (Ideal.add_mem _ hy2 hz2) (Ideal.sum_mem _ fun k hk => ?_)
        have hk0 : 0 < k := (Finset.mem_Ioo.1 hk).1
        have hyk : y ^ k ∈ J ^ (n + 1) :=
          Ideal.pow_le_pow_right (Nat.le_succ _) (Ideal.pow_mem_of_mem _ hy1 k hk0)
        exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hyk)
    exact key.2

end GlobalTheory.BSP
