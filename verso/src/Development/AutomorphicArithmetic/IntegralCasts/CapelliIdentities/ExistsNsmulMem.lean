import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects

/- English proof (translation)
Introduce `E W _ _ _ _ La hL w`. Proceed by induction on `(hL.span_eq_top ▸ Submodule.mem_top : w ∈ Submodule.span E (La : Set W)) using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_pos, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_pos, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨⟨d, hd, hx⟩, ⟨e, he, hy⟩⟩` from `And.intro hx hy`. Use `⟨d * e, mul_pos hd he, smul_add (d * e) x y ▸ La.add_mem ?_ ?_⟩` and prove the remaining obligations. Use `exacts [mul_comm e d ▸ mul_smul e d x ▸ La.nsmul_mem hx e, mul_smul d e y ▸ La.nsmul_mem hy d]`. Consider the case `smul a x _ hx`. Take `⟨⟨d, hd, hx⟩, n, s, hn, hs⟩` from `And.intro hx (((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (.of_finite ℚ a)).exists_nsmul_eq (NumberField.RingOfIntegers E))`.

Use `⟨n * d, mul_pos (Nat.pos_of_ne_zero hn) hd, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul, smul_comm d a x, ← smul_assoc, hs]`. Conclude with `hL.smul_mem s _ hx`.
-/
theorem UpperTheory.Reformulated.B.ExistsNsmulMem.exists_nsmul_mem.{u_1, u_2} :
    ∀ {E : Type u_1} {W : Type u_2} [inst : Field E] [NumberField E] [inst_2 : AddCommGroup W]
    [inst_3 : _root_.Module E W] {La : AddSubgroup W},
    GroundTheory.Heights₂.Heights.FiniteCovolume.IsLattice E La →
      ∀ (w : W),
        ∃ (d : ℕ),
          (0 : ℕ) < d ∧
            d • w ∈ La := by
  intro E W _ _ _ _ La hL w
  induction (hL.span_eq_top ▸ Submodule.mem_top : w ∈ Submodule.span E (La : Set W))
    using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨⟨d, hd, hx⟩, ⟨e, he, hy⟩⟩ := And.intro hx hy
    refine ⟨d * e, mul_pos hd he, smul_add (d * e) x y ▸ La.add_mem ?_ ?_⟩
    exacts [mul_comm e d ▸ mul_smul e d x ▸ La.nsmul_mem hx e, mul_smul d e y ▸ La.nsmul_mem hy d]
  | smul a x _ hx =>
    obtain ⟨⟨d, hd, hx⟩, n, s, hn, hs⟩ := And.intro hx (((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
      (.of_finite ℚ a)).exists_nsmul_eq (NumberField.RingOfIntegers E))
    refine ⟨n * d, mul_pos (Nat.pos_of_ne_zero hn) hd, ?_⟩
    rw [mul_smul, smul_comm d a x, ← smul_assoc, hs]; exact hL.smul_mem s _ hx
