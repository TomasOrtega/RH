import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle

open UpperTheory.V.FW

/- English proof (translation)
Introduce `k A _ _ a x ha h`. Establish `hx : AddMonoidAlgebra.single a (1:k) * x = x`. Rewrite `h` using `[sub_mul, one_mul, sub_eq_zero]`. Conclude with `h.symm`. Establish `step : ∀ c, x.coeff (c + a) = x.coeff c`.

Introduce `c`. Use `conv_lhs => rw [← hx]`. Rewrite using `[AddMonoidAlgebra.coeff_single_mul_apply, one_mul, add_comm c a, neg_add_cancel_left]`. Establish `key : ∀ b (n : ℕ), x.coeff (b + n • a) = x.coeff b`. Introduce `b n`.

Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [succ_nsmul, ← add_assoc, step, ih]`. Assume the negation of the conclusion as `hne`. Choose the witnesses or unpack the hypotheses as in `⟨b, hb⟩ : ∃ b, x.coeff b ≠ 0 := by`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hne (AddMonoidAlgebra.ext (Finsupp.ext fun c => by simp [hc c]))`. Establish `hinj : Function.Injective fun n : ℕ => b + n • a`. Introduce `n m hnm`.

Simplify using `only [add_right_inj] at hnm`. Break down `le_total n m with hle | hle` into its components or cases. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hle`. Rewrite `hnm` using `[add_nsmul, left_eq_add]`. Simplify using `[ha d hnm]`.

Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hle`. Rewrite `hnm` using `[add_nsmul, add_eq_left]`. Simplify using `[ha d hnm]`. Conclude with `Set.infinite_of_injective_forall_mem hinj (fun n => show b + n • a ∈ (x.coeff.support : Set A) by simp [key, hb]) x.coeff.support.finite_toSet`.
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
