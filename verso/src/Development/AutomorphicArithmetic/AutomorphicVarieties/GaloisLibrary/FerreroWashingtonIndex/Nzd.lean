import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle

open UpperTheory.V.FW

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Treat this case separately. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem UpperTheory.V.FW.nzd :
    ∀ (k A : Type) [CommRing k] [AddCommGroup A] (a : A) (x : AddMonoidAlgebra k A), (∀ m : ℕ, m • a = 0 → m = 0) → (1 - AddMonoidAlgebra.single a 1) * x = 0 → x = 0 := by
  intro k A _ _ a x ha h
  have hx : AddMonoidAlgebra.single a (1:k) * x = x := by
    rw [sub_mul, one_mul, sub_eq_zero] at h; exact h.symm
  have step : ∀ c, x.coeff (c + a) = x.coeff c := by
    intro c
    conv_lhs => rw [← hx]
    rw [AddMonoidAlgebra.coeff_single_mul_apply, one_mul, add_comm c a, neg_add_cancel_left]
  have key : ∀ b (n : ℕ), x.coeff (b + n • a) = x.coeff b := by
    intro b n
    induction n with
    | zero => simp
    | succ n ih => rw [succ_nsmul, ← add_assoc, step, ih]
  by_contra hne
  obtain ⟨b, hb⟩ : ∃ b, x.coeff b ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hne (AddMonoidAlgebra.ext (Finsupp.ext fun c => by simp [hc c]))
  have hinj : Function.Injective fun n : ℕ => b + n • a := by
    intro n m hnm
    simp only [add_right_inj] at hnm
    rcases le_total n m with hle | hle
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
      rw [add_nsmul, left_eq_add] at hnm
      simp [ha d hnm]
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
      rw [add_nsmul, add_eq_left] at hnm
      simp [ha d hnm]
  exact Set.infinite_of_injective_forall_mem hinj
    (fun n => show b + n • a ∈ (x.coeff.support : Set A) by simp [key, hb])
    x.coeff.support.finite_toSet
