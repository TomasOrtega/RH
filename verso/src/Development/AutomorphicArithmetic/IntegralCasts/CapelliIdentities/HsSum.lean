import Mathlib

noncomputable def UpperTheory.Reformulated.B.Qh70.Hs :
    {L V ι : Type} →
      [inst : Field L] →
        [inst_1 : Algebra ℂ L] →
          [inst_2 : AddCommGroup V] → [_root_.Module L V] → Subalgebra ℂ L → Finset ι → (ι → V) → V → Prop :=
    fun {L V ι : Type} [Field L] [Algebra ℂ L] [AddCommGroup V] [_root_.Module L V] (B : Subalgebra ℂ L) (P : Finset ι)
        (g : ι → V) (w : V) ↦
      ∃ (c : ι → L), (∀ (S : ι), c S ∈ B) ∧ w = ∑ S ∈ P, c S • g S

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Supply the required witnesses or components.
-/
theorem UpperTheory.Reformulated.B.Qh70.Hs_sum :
    ∀ {L V ι : Type} [inst : Field L] [inst_1 : Algebra ℂ L] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module L V]
      {B : Subalgebra ℂ L} {P : Finset ι} {g : ι → V} {α : Type} (s : Finset α) (f : α → V),
      (∀ a ∈ s, UpperTheory.Reformulated.B.Qh70.Hs B P g (f a)) → UpperTheory.Reformulated.B.Qh70.Hs B P g (∑ a ∈ s, f a) := by
  intro L V ι _ _ _ _ B P g α s f h
  refine Finset.sum_induction f (UpperTheory.Reformulated.B.Qh70.Hs B P g) ?_ ?_ h
  · rintro a b ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    refine ⟨fun S => c S + d S, fun S => B.add_mem (hc S) (hd S), ?_⟩
    simp only [add_smul, Finset.sum_add_distrib]
  · exact ⟨fun _ => 0, fun _ => B.zero_mem, by simp⟩
