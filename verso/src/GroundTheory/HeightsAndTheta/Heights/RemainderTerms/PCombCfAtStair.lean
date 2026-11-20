import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Equiv Comb

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.
-/
theorem Comb.stair_strictAnti (m : ℕ) : StrictAnti (stair m) := by
  intro a b hab
  have hb := b.isLt
  have hab' : (a : ℕ) < b := hab
  simp only [stair]
  omega

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Prove the first alternative. Prove the second alternative. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem CombCfAtStair.proof (h1 : CombCfUpdateZero.Statement) : CombCfAtStair.Statement := by
  intro m n
  induction n with
  | zero =>
    intro lam hlam
    have hs := Comb.stair_strictAnti m
    have hl : StrictAnti (fun i => lam i + stair m i) := by
      intro a b hab
      have h2 := hlam hab.le
      have h3 := hs hab
      simp only
      omega
    simp only [alternantPsum, List.replicate_zero, List.map_nil, List.prod_nil, mul_one,
      vandermondeOf_X_eq_alt]
    rw [cf_alt_of_strictAnti hl hs]
    by_cases h0 : lam = 0
    · subst h0
      have hu : latticeWords 0 (0 : Fin m → ℕ) = univ := by
        rw [Finset.eq_univ_iff_forall]
        intro w
        simp only [latticeWords, mem_filter, mem_univ, true_and]
        refine ⟨fun t ht i j _ => ?_, fun i => pcnt_zero w i⟩
        have ht0 : t = 0 := by omega
        subst ht0
        rw [pcnt_zero, pcnt_zero]
      rw [hu, Finset.card_univ]
      simp
    · have hne : (fun i => lam i + stair m i) ≠ stair m := by
        intro h
        apply h0
        funext i
        have := congrFun h i
        show lam i = 0
        omega
      rw [if_neg hne, latticeWords_eq_empty_of_sum_ne]
      · simp
      · intro hsum
        apply h0
        funext i
        have := (Finset.sum_eq_zero_iff.mp hsum) i (mem_univ i)
        simpa using this
  | succ n ih =>
    intro lam hlam
    have hsplit : alternantPsum m (List.replicate (n + 1) 1) =
        alternantPsum m (List.replicate n 1) * psum (Fin m) ℚ 1 := by
      simp only [alternantPsum, List.replicate_succ', List.map_append, List.prod_append,
        List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
    rw [hsplit, cf_mul_psum, card_latticeWords_succ n lam hlam, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.cast_ite, Nat.cast_zero]
    by_cases hgood : 1 ≤ lam i ∧ Antitone (Function.update lam i (lam i - 1))
    · rw [if_pos (by omega), if_pos hgood.1]
      have hup : Function.update (fun j => lam j + stair m j) i (lam i + stair m i - 1) =
          fun j => Function.update lam i (lam i - 1) j + stair m j := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp only [Function.update_self]
          omega
        · simp only [Function.update_of_ne hj]
      rw [hup]
      exact ih _ hgood.2
    · have hR : (if 1 ≤ lam i then
          (((latticeWords n (Function.update lam i (lam i - 1))).card : ℕ) : ℚ) else 0) = 0 := by
        split_ifs with hi
        · rw [latticeWords_eq_empty_of_not_antitone n _ (fun h => hgood ⟨hi, h⟩)]
          simp
        · rfl
      rw [hR]
      split_ifs with hL
      · refine h1 m _ (isAlt_vandermonde_mul_prod _) lam hlam i hL ?_
        by_cases hi : lam i = 0
        · exact Or.inl hi
        · exact Or.inr fun h => hgood ⟨by omega, h⟩
      · rfl

end GroundTheory.Heights₂.Heights.RestTerms
