import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup

open CategoryTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Clear the denominators using the available nonvanishing facts. Put the polynomial expressions in normal form.

Establish an intermediate fact. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem UpperTheory.altChain_of_permSplit :
    UpperTheory.V.Af.BA.PermSplit → UpperTheory.V.Af.BA.AltChain := by
  intro hP Γ I _ _ K p
  simp only [UpperTheory.V.Af.BA.Cx.alt, UpperTheory.V.Af.BA.Cx.d, Linear.smul_comp, Linear.comp_smul,
    Preadditive.sum_comp, Preadditive.comp_sum, UpperTheory.V.Af.BA.Cx.reC_comp]
  simp only [Finset.smul_sum, smul_smul]
  set c : ℂ := ((p + 1 + 1).factorial : ℂ)⁻¹ with hc
  have hx : ∀ x : Fin (p + 2),
      ∑ σ : Equiv.Perm (Fin (p + 2)),
        ((-1 : ℂ) ^ (x : ℕ) * (c * (((Equiv.Perm.sign σ : ℤ)) : ℂ))) • K.reC (σ ∘ x.succAbove) =
      ∑ q : Fin (p + 2) × Equiv.Perm (Fin (p + 1)),
        (c * ((-1 : ℂ) ^ (q.1 : ℕ) * ((Equiv.Perm.sign q.2 : ℤ) : ℂ))) • K.reC (q.1.succAbove ∘ q.2) := by
    intro x
    obtain ⟨e, he⟩ := hP (p + 1) x
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl ?_
    rintro ⟨i, τ⟩ -
    obtain ⟨hs, hk⟩ := he i τ
    have hf : (e (i, τ) : Fin (p + 2) → Fin (p + 2)) ∘ x.succAbove = i.succAbove ∘ τ := funext hk
    rw [hf, hs]
    congr 1
    push_cast
    have h1 : (-1 : ℂ) ^ (x : ℕ) * (-1 : ℂ) ^ (x : ℕ) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      simp
    linear_combination (c * (-1 : ℂ) ^ (i : ℕ) * ((Equiv.Perm.sign τ : ℤ) : ℂ)) * h1
  rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  conv_rhs => rw [Finset.sum_comm, ← Fintype.sum_prod_type']
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  rintro ⟨i, τ⟩ -
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  have hF : ((p + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hP2 : ((p : ℂ) + 2) ≠ 0 := by exact_mod_cast (by omega : p + 2 ≠ 0)
  rw [hc, Nat.factorial_succ (p + 1)]
  push_cast
  field_simp
  ring_nf
  have h2 : (2 + (p : ℂ)) ≠ 0 := by rwa [add_comm]
  field_simp
  ring
