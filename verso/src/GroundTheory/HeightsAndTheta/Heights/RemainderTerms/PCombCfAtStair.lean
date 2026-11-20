import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Equiv Comb

/- English proof (translation)
Introduce `a b hab`. Establish `hb` using `b.isLt`. Establish `hab' : (a : ℕ) < b` using `hab`. Simplify using `only [stair]`. Use linear arithmetic over natural numbers and integers.
-/
theorem Comb.stair_strictAnti (m : ℕ) : StrictAnti (stair m) := by
  intro a b hab
  have hb := b.isLt
  have hab' : (a : ℕ) < b := hab
  simp only [stair]
  omega

/- English proof (translation)
Introduce `m n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `lam hlam`. Establish `hs` using `Comb.stair_strictAnti m`.

Establish `hl : StrictAnti (fun i => lam i + stair m i)`. Introduce `a b hab`. Establish `h2` using `hlam hab.le`. Establish `h3` using `hs hab`. Simplify using `only`.

Use linear arithmetic over natural numbers and integers. Simplify using `only [alternantPsum, List.replicate_zero, List.map_nil, List.prod_nil, mul_one, vandermondeOf_X_eq_alt]`. Rewrite using `[cf_alt_of_strictAnti hl hs]`. Distinguish the cases in `h0 : lam = 0`. Substitute `h0` using the available equality.

Establish `hu : latticeWords 0 (0 : Fin m → ℕ) = univ`. Rewrite using `[Finset.eq_univ_iff_forall]`. Introduce `w`. Simplify using `only [latticeWords, mem_filter, mem_univ, true_and]`. Use `⟨fun t ht i j _ => ?_, fun i => pcnt_zero w i⟩` and prove the remaining obligations.

Establish `ht0 : t = 0` using `by omega`. Substitute `ht0` using the available equality. Rewrite using `[pcnt_zero, pcnt_zero]`. Rewrite using `[hu, Finset.card_univ]`. Simplify using the standard rewrite rules.

Establish `hne : (fun i => lam i + stair m i) ≠ stair m`. Introduce `h`. Apply `h0` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Use `congrFun h i` as an intermediate fact.

Use `show lam i = 0`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg hne, latticeWords_eq_empty_of_sum_ne]`. Simplify using the standard rewrite rules. Introduce `hsum`.

Apply `h0` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Use `(Finset.sum_eq_zero_iff.mp hsum) i (mem_univ i)` as an intermediate fact. Simplify using `using this`. Consider the case `succ n ih`.

Introduce `lam hlam`. Establish `hsplit : alternantPsum m (List.replicate (n + 1) 1) = alternantPsum m (List.replicate n 1) * psum (Fin m) ℚ 1`. Simplify using `only [alternantPsum, List.replicate_succ', List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]`. Rewrite using `[hsplit, cf_mul_psum, card_latticeWords_succ n lam hlam, Nat.cast_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Nat.cast_ite, Nat.cast_zero]`. Distinguish the cases in `hgood : 1 ≤ lam i ∧ Antitone (Function.update lam i (lam i - 1))`. Rewrite using `[if_pos (by omega), if_pos hgood.1]`. Establish `hup : Function.update (fun j => lam j + stair m j) i (lam i + stair m i - 1) = fun j => Function.update lam i (lam i - 1) j + stair m j`. Use function extensionality and compare the values at `j`.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `only [Function.update_self]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Function.update_of_ne hj]`.

Rewrite using `[hup]`. Conclude with `ih _ hgood.2`. Establish `hR : (if 1 ≤ lam i then (((latticeWords n (Function.update lam i (lam i - 1))).card : ℕ) : ℚ) else 0) = 0` using `by split_ifs with hi`. Rewrite using `[latticeWords_eq_empty_of_not_antitone n _ (fun h => hgood ⟨hi, h⟩)]`. Simplify using the standard rewrite rules.

Both sides reduce to the same expression. Rewrite using `[hR]`. Use `split_ifs with hL`. Use `h1 m _ (isAlt_vandermonde_mul_prod _) lam hlam i hL ?_` and prove the remaining obligations. Distinguish the cases in `hi : lam i = 0`.

Conclude with `Or.inl hi`. Conclude with `Or.inr fun h => hgood ⟨by omega, h⟩`. Both sides reduce to the same expression.
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
