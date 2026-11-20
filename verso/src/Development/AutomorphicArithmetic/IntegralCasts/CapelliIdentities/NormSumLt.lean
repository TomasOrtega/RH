import Mathlib

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem UpperTheory.Reformulated.B.Qe17.norm_sum_lt :
    ∀ {F ι : Type} [inst : NormedField F] [IsUltrametricDist F]
    (s : Finset ι) (f : ι → F) {C : ℝ}, (0 : ℝ) < C → (∀ i ∈ s, ‖f i‖ < C) → ‖∑ i ∈ s, f i‖ < C := by
  intro F ι _ _ s f C hC h
  refine Finset.sum_induction f (fun x => ‖x‖ < C) ?_ ?_ h
  · intro a b ha hb
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max a b) (max_lt ha hb)
  · simpa using hC
