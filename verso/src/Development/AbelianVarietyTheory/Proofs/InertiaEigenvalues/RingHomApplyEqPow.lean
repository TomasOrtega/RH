import Mathlib

namespace GlobalTheory.FixedOfPower
open Polynomial

/- English proof (translation)
Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem fix_of_pow {k : Type} [Field k] (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (τ : k →+* k) (c : k) (hc : c ^ p = c) : τ c = c := by
  classical
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  let f : ZMod p →+* k := ZMod.castHom (dvd_refl p) k
  have hc' : ∃ a, f a = c := by
    by_contra hcon
    have hP0 : (X ^ p - X : k[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k hp1
    have hsub : insert c (Finset.univ.image f) ⊆ (X ^ p - X : k[X]).roots.toFinset := by
      intro x hx
      rw [Multiset.mem_toFinset, mem_roots hP0]
      show eval x (X ^ p - X) = 0
      rw [eval_sub, eval_pow, eval_X, sub_eq_zero]
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hc
      · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
        rw [← map_pow, ZMod.pow_card]
    have hcard : (insert c (Finset.univ.image f)).card = p + 1 := by
      rw [Finset.card_insert_of_notMem (by simpa using hcon),
        Finset.card_image_of_injective _ f.injective, Finset.card_univ, ZMod.card]
    have hle := (Finset.card_le_card hsub).trans
      ((Multiset.toFinset_card_le _).trans (card_roots' (X ^ p - X : k[X])))
    rw [hcard, FiniteField.X_pow_card_sub_X_natDegree_eq k hp1] at hle
    omega
  obtain ⟨a, rfl⟩ := hc'
  exact DFunLike.congr_fun (RingHom.ext_zmod (τ.comp f) f) a

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem ringHom_apply_eq_pow {k : Type} [Field k] (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (τ : k →+* k) (N : ℕ) (hN : 0 < N) (z : k) (hz : z ^ p ^ N = z) :
    ∃ e : ℕ, τ z = z ^ p ^ e := by
  have : ExpChar k p := ExpChar.prime Fact.out
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  let g : k[X] := ∏ e ∈ Finset.range (M + 1), (X - C (z ^ p ^ e))
  have hg : g.map (frobenius k p) = g := by
    have e1 : ∀ e : ℕ, (z ^ p ^ e) ^ p = z ^ p ^ (e + 1) := fun e => by rw [← pow_mul, pow_succ]
    simp only [g, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      frobenius_def, e1]
    rw [Finset.prod_range_succ, Finset.prod_range_succ' (fun e => X - C (z ^ p ^ e)), hz, pow_zero,
      pow_one]
  have hcoef : ∀ i, (g.coeff i) ^ p = g.coeff i := by
    intro i
    have h := congrArg (fun q : k[X] => q.coeff i) hg
    simpa [Polynomial.coeff_map, frobenius_def] using h
  have hτ : g.map τ = g := by
    ext i
    rw [Polynomial.coeff_map]
    exact fix_of_pow p τ _ (hcoef i)
  have hz0 : g.eval z = 0 := by
    simp only [g, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.succ_pos M)) (by simp)
  have hτz : g.eval (τ z) = 0 := by
    rw [← hτ, Polynomial.eval_map, Polynomial.eval₂_at_apply, hz0, map_zero]
  simp only [g, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hτz
  obtain ⟨e, -, he⟩ := Finset.prod_eq_zero_iff.mp hτz
  exact ⟨e, sub_eq_zero.mp he⟩

end GlobalTheory.FixedOfPower
