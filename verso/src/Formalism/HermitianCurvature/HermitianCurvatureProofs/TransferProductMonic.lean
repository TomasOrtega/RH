import Formalism.HermitianCurvature.StatementI

namespace Formalism.FourierDecayAlt.P.Misc

open Formalism.FourierDecayAlt.I Finset Polynomial

/- English proof (translation)
Introduce `F _ o q hq hq0 a`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1` using `h (1, 1) ⟨o.one_mem, o.one_mem, 0, o.zero_mem, by simp⟩`. Establish `h2` using `h (q, 0) ⟨hq, o.zero_mem, 1, o.one_mem, by simp⟩`.

Simplify using `only [mul_one, mul_zero, sub_zero] at h1 h2`. Establish `e2 : a.1 * q / q = a.1` using `by field_simp`. Rewrite `h2` using `[e2]`. Use `⟨h2, ?_, (a.1 - a.2) / q, h1, by field_simp⟩` and prove the remaining obligations. Establish `: a.2 = a.1 - q * ((a.1 - a.2) / q)` using `by field_simp; ring`.

Rewrite using `[this]`. Conclude with `o.sub_mem h2 (o.mul_mem hq h1)`. Introduce and unpack `⟨ha1, ha2, s, hs, has⟩ b ⟨hb1, hb2, t, ht, hbt⟩`. Establish `ha : a.1 = a.2 + q * s` using `by linear_combination has`. Establish `hb : b.1 = b.2 + q * t` using `by linear_combination hbt`.

Establish `e : (a.1 * b.1 - a.2 * b.2) / q = a.2 * t + s * b.2 + q * s * t`. Rewrite using `[ha, hb]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `o.add_mem (o.add_mem (o.mul_mem ha2 ht) (o.mul_mem hs hb2)) (o.mul_mem (o.mul_mem hq hs) ht)`.
-/
theorem selfDualG_holds : SelfDualG := by
  intro F _ o q hq hq0 a
  constructor
  · intro h
    have h1 := h (1, 1) ⟨o.one_mem, o.one_mem, 0, o.zero_mem, by simp⟩
    have h2 := h (q, 0) ⟨hq, o.zero_mem, 1, o.one_mem, by simp⟩
    simp only [mul_one, mul_zero, sub_zero] at h1 h2
    have e2 : a.1 * q / q = a.1 := by field_simp
    rw [e2] at h2
    refine ⟨h2, ?_, (a.1 - a.2) / q, h1, by field_simp⟩
    have : a.2 = a.1 - q * ((a.1 - a.2) / q) := by field_simp; ring
    rw [this]; exact o.sub_mem h2 (o.mul_mem hq h1)
  · rintro ⟨ha1, ha2, s, hs, has⟩ b ⟨hb1, hb2, t, ht, hbt⟩
    have ha : a.1 = a.2 + q * s := by linear_combination has
    have hb : b.1 = b.2 + q * t := by linear_combination hbt
    have e : (a.1 * b.1 - a.2 * b.2) / q = a.2 * t + s * b.2 + q * s * t := by
      rw [ha, hb]; field_simp; ring
    rw [e]
    exact o.add_mem (o.add_mem (o.mul_mem ha2 ht) (o.mul_mem hs hb2)) (o.mul_mem (o.mul_mem hq hs) ht)

/- English proof (translation)
Rewrite using `[TpolyProd, TpolyProd, List.ofFn_succ', List.concat_eq_append, List.reverse_append]`. Simplify using `[List.prod_cons]`.
-/
lemma tpolyProd_succ {A : Type} [Ring A] (n : ℕ) (p c ci : ℕ → A) :
    TpolyProd (n + 1) p c ci = Tpoly (p (n + 1)) (c (n + 1)) (ci (n + 1)) * TpolyProd n p c ci := by
  rw [TpolyProd, TpolyProd, List.ofFn_succ', List.concat_eq_append, List.reverse_append]
  simp [List.prod_cons]

/- English proof (translation)
Introduce `A _ _ n p c ci`. Proceed by induction on `n with`. Consider the case `zero => simp [TpolyProd]`. Consider the case `succ n ih`. Take `⟨hm, hd, hb⟩` from `ih`.

Establish `e00 : TpolyProd (n + 1) p c ci 0 0 = (X + C (p (n + 1))) * TpolyProd n p c ci 0 0 - C (c (n + 1)) * TpolyProd n p c ci 1 0`. Rewrite using `[tpolyProd_succ]`. Simplify using `[Tpoly, Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg]`. Establish `e10 : TpolyProd (n + 1) p c ci 1 0 = C (ci (n + 1)) * TpolyProd n p c ci 0 0`. Rewrite using `[tpolyProd_succ]`.

Simplify using `[Tpoly, Matrix.mul_apply, Fin.sum_univ_two]`. Establish `hXm : (X + C (p (n + 1)) : A[X]).Monic` using `monic_X_add_C _`. Establish `hprod : ((X + C (p (n + 1))) * TpolyProd n p c ci 0 0).Monic` using `hXm.mul hm`. Establish `hpd : ((X + C (p (n + 1))) * TpolyProd n p c ci 0 0).natDegree = n + 1`. Rewrite using `[hXm.natDegree_mul hm, natDegree_X_add_C, hd]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hlow : (C (c (n + 1)) * TpolyProd n p c ci 1 0).degree < ((X + C (p (n + 1))) * TpolyProd n p c ci 0 0).degree`. Rewrite using `[degree_eq_natDegree hprod.ne_zero, hpd]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[e00]`. Conclude with `hprod.sub_of_left hlow`. Rewrite using `[e00]`. Conclude with `(natDegree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt hlow)).trans hpd`. Rewrite using `[e10]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem tProdMonic_holds : TProdMonic := by
  intro A _ _ n p c ci
  induction n with
  | zero => simp [TpolyProd]
  | succ n ih =>
    obtain ⟨hm, hd, hb⟩ := ih
    have e00 : TpolyProd (n + 1) p c ci 0 0 =
        (X + C (p (n + 1))) * TpolyProd n p c ci 0 0 - C (c (n + 1)) * TpolyProd n p c ci 1 0 := by
      rw [tpolyProd_succ]; simp [Tpoly, Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg]
    have e10 : TpolyProd (n + 1) p c ci 1 0 = C (ci (n + 1)) * TpolyProd n p c ci 0 0 := by
      rw [tpolyProd_succ]; simp [Tpoly, Matrix.mul_apply, Fin.sum_univ_two]
    have hXm : (X + C (p (n + 1)) : A[X]).Monic := monic_X_add_C _
    have hprod : ((X + C (p (n + 1))) * TpolyProd n p c ci 0 0).Monic := hXm.mul hm
    have hpd : ((X + C (p (n + 1))) * TpolyProd n p c ci 0 0).natDegree = n + 1 := by
      rw [hXm.natDegree_mul hm, natDegree_X_add_C, hd]; ring
    have hlow : (C (c (n + 1)) * TpolyProd n p c ci 1 0).degree <
        ((X + C (p (n + 1))) * TpolyProd n p c ci 0 0).degree := by
      rw [degree_eq_natDegree hprod.ne_zero, hpd]
      calc (C (c (n + 1)) * TpolyProd n p c ci 1 0).degree
          ≤ (C (c (n + 1))).degree + (TpolyProd n p c ci 1 0).degree := degree_mul_le _ _
        _ ≤ 0 + (TpolyProd n p c ci 1 0).degree := by gcongr; exact degree_C_le
        _ < (n : WithBot ℕ) := by simpa using hb
        _ ≤ ((n + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.le_succ n
    refine ⟨?_, ?_, ?_⟩
    · rw [e00]; exact hprod.sub_of_left hlow
    · rw [e00]; exact (natDegree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt hlow)).trans hpd
    · rw [e10]
      calc (C (ci (n + 1)) * TpolyProd n p c ci 0 0).degree
          ≤ (C (ci (n + 1))).degree + (TpolyProd n p c ci 0 0).degree := degree_mul_le _ _
        _ ≤ 0 + (TpolyProd n p c ci 0 0).degree := by gcongr; exact degree_C_le
        _ = (n : WithBot ℕ) := by rw [zero_add, degree_eq_natDegree hm.ne_zero, hd]
        _ < ((n + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self n

end Formalism.FourierDecayAlt.P.Misc

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.Misc.selfDualG_holds`.
-/
theorem Formalism.FourierDecayAlt.P.self_dual_gamma : Formalism.FourierDecayAlt.I.SelfDualG := Formalism.FourierDecayAlt.P.Misc.selfDualG_holds
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.Misc.tProdMonic_holds`.
-/
theorem Formalism.FourierDecayAlt.P.transfer_product_monic : Formalism.FourierDecayAlt.I.TProdMonic := Formalism.FourierDecayAlt.P.Misc.tProdMonic_holds
