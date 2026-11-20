import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects

/- English proof (translation)
Introduce `E _ _ W _ _ La h x`. Use `Submodule.span_induction (p := fun x _ => ∃ d : ℤ, d ≠ 0 ∧ d • x ∈ La) (fun y hy => ⟨1, one_ne_zero, by simpa using hy⟩) ⟨1, one_ne_zero, by simp⟩ ?_ ?_ (h.span_eq_top ▸ Submodule.mem_top : x ∈ Submodule.span E (La : Set W))` and prove the remaining obligations. Introduce and unpack `y z - - ⟨d, hd, hy⟩ ⟨e, he, hz⟩`. Use `⟨d * e, mul_ne_zero hd he, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add, mul_smul d e z, mul_comm d e, mul_smul e d y]`.

Conclude with `add_mem (La.zsmul_mem hy e) (La.zsmul_mem hz d)`. Introduce and unpack `a y - ⟨d, hd, hy⟩`. Take `⟨m, hm, hi⟩` from `((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)).exists_integral_multiple`. Use `⟨m * d, mul_ne_zero hm hd, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul, smul_comm d a y, ← smul_assoc]`.

Conclude with `h.smul_mem ⟨m • a, hi⟩ _ hy`.
-/
theorem UpperTheory.Reformulated.B.ExistsZsmulMem.exists_zsmul_mem.{u_1, u_2} :
    ∀ {E : Type u_1} [inst : Field E] [NumberField E] {W : Type u_2} [inst_2 : AddCommGroup W]
    [inst_3 : _root_.Module E W] {La : AddSubgroup W},
    GroundTheory.Heights₂.Heights.FiniteCovolume.IsLattice E La →
      ∀ (x : W),
        ∃ (d : ℤ),
          d ≠ (0 : ℤ) ∧
            d • x ∈ La := by
  intro E _ _ W _ _ La h x
  refine Submodule.span_induction (p := fun x _ => ∃ d : ℤ, d ≠ 0 ∧ d • x ∈ La)
    (fun y hy => ⟨1, one_ne_zero, by simpa using hy⟩) ⟨1, one_ne_zero, by simp⟩ ?_ ?_
    (h.span_eq_top ▸ Submodule.mem_top : x ∈ Submodule.span E (La : Set W))
  · rintro y z - - ⟨d, hd, hy⟩ ⟨e, he, hz⟩
    refine ⟨d * e, mul_ne_zero hd he, ?_⟩
    rw [smul_add, mul_smul d e z, mul_comm d e, mul_smul e d y]
    exact add_mem (La.zsmul_mem hy e) (La.zsmul_mem hz d)
  · rintro a y - ⟨d, hd, hy⟩
    obtain ⟨m, hm, hi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
      (Algebra.IsAlgebraic.isAlgebraic a)).exists_integral_multiple
    refine ⟨m * d, mul_ne_zero hm hd, ?_⟩
    rw [mul_smul, smul_comm d a y, ← smul_assoc]
    exact h.smul_mem ⟨m • a, hi⟩ _ hy
