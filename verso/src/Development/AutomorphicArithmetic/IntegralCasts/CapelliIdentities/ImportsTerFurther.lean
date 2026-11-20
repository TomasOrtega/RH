import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Apply an available result and prove the equalities needed to match it to the conclusion.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Apply an available result and prove the equalities needed to match it to the conclusion. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.Reformulated.B.Ga5b.exists_nat_smul_mem :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
    [inst_2 : NumberField.IsCMField E] {N : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E N) (v : Fin N → E),
    ∃ (n : ℕ),
      (0 : ℕ) < n ∧
        (↑n : E) • v ∈
          X.Λ := by
  intro E _ _ _ N X v
  refine Submodule.span_induction (fun x hx => ⟨1, one_pos, by simpa using hx⟩) ⟨1, one_pos, by simp⟩
    ?_ ?_ (X.Λ_span ▸ Submodule.mem_top : v ∈ Submodule.span E (X.Λ : Set (Fin N → E)))
  · rintro x y - - ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, mul_pos ha hb, ?_⟩
    convert X.Λ.add_mem (nsmul_mem hx b) (nsmul_mem hy a) using 1
    ext i; simp; ring
  · rintro c x - ⟨a, ha, hx⟩
    obtain ⟨m, s, hm, hs⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
      (.of_finite ℚ c)).exists_nsmul_eq (NumberField.RingOfIntegers E)
    refine ⟨m * a, mul_pos (Nat.pos_of_ne_zero hm) ha, ?_⟩
    convert X.Λ.smul_mem s hx using 1
    rw [← algebraMap_smul E s, ← hs]; ext i; simp; ring
