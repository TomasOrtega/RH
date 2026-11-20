import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.NullStableAlt

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

/- English proof (translation)
Establish `h : (⁅pderiv (R` using `ℂ) i, pderiv (R := ℂ) j⁆ : Derivation ℂ (PX m n) (PX m n)) = 0 := by`. Apply `MvPolynomial.derivation_ext` to reduce the goal to its premises. Introduce `k`. Rewrite using `[Derivation.commutator_apply, pderiv_X, pderiv_X]`. Apply the tactic sequence `by_cases h1 : j = k <;> by_cases h2 : i = k <;> simp [Pi.single_apply, h1, h2]`.

Use `congrArg (fun D : Derivation ℂ (PX m n) (PX m n) => D p) h` as an intermediate fact. Simplify `this` using `[Derivation.commutator_apply, sub_eq_zero]`.
-/
theorem hop_pderiv_comm' (i j : Fin m × Fin n × Bool) (p : PX m n) :
    pderiv (R := ℂ) i (pderiv (R := ℂ) j p) = pderiv (R := ℂ) j (pderiv (R := ℂ) i p) := by
  have h : (⁅pderiv (R := ℂ) i, pderiv (R := ℂ) j⁆ : Derivation ℂ (PX m n) (PX m n)) = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    rw [Derivation.commutator_apply, pderiv_X, pderiv_X]
    by_cases h1 : j = k <;> by_cases h2 : i = k <;> simp [Pi.single_apply, h1, h2]
  have := congrArg (fun D : Derivation ℂ (PX m n) (PX m n) => D p) h
  simpa [Derivation.commutator_apply, sub_eq_zero] using this

/- English proof (translation)
Simplify using `[cr]`.
-/
theorem cr_false (c : ℝ) (a : Fin m) (i : Fin n) (Q : PX m n) :
    cr c (a, i, false) Q = -pderiv (a, i, false) Q + (2 * c : ℂ) • (X (a, i, true) * Q) := by
  simp [cr]

/- English proof (translation)
Simplify using `[cr]`.
-/
theorem cr_true (c : ℝ) (a : Fin m) (i : Fin n) (Q : PX m n) :
    cr c (a, i, true) Q = -pderiv (a, i, true) Q + (2 * c : ℂ) • (X (a, i, false) * Q) := by
  simp [cr]

/- English proof (translation)
Distinguish the cases in `hr : r = 0`. Substitute `hr` using the available equality. Simplify using `[fock]`. Rewrite using `[fock, support_C, if_neg hr, Finset.sum_singleton, coeff_C, if_pos rfl]`. Simplify using `[fockMono, smul_eq_C_mul]`.
-/
theorem hop_fock_C (c : ℝ) (r : ℂ) : fock c (C r : PX m n) = C r := by
  classical
  by_cases hr : r = 0
  · subst hr; simp [fock]
  · rw [fock, support_C, if_neg hr, Finset.sum_singleton, coeff_C, if_pos rfl]
    simp [fockMono, smul_eq_C_mul]

/- English proof (translation)
Take `⟨a, i, e⟩` from `j`. Consider the cases of `e`. Rewrite using `[cr_false, cr_false]`. Simplify using `only [map_add, map_neg, map_smul, Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_C_mul, hop_pderiv_comm' k (a, i, false)]`. Distinguish the cases in `h : k = (a, i, true)`.

Substitute `h` using the available equality. Simplify using `[Pi.single_apply]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[Pi.single_apply, h, Ne.symm h]`. Rewrite using `[cr_true, cr_true]`.

Simplify using `only [map_add, map_neg, map_smul, Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_C_mul, hop_pderiv_comm' k (a, i, true)]`. Distinguish the cases in `h : k = (a, i, false)`. Substitute `h` using the available equality. Simplify using `[Pi.single_apply]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `[Pi.single_apply, h, Ne.symm h]`.
-/
theorem hop_pderiv_cr (c : ℝ) (j k : Fin m × Fin n × Bool) (Q : PX m n) :
    pderiv k (cr c j Q) = cr c j (pderiv k Q) + C (2 * c : ℂ) * (if k = (j.1, j.2.1, !j.2.2) then Q else 0) := by
  obtain ⟨a, i, e⟩ := j
  cases e
  · rw [cr_false, cr_false]
    simp only [map_add, map_neg, map_smul, Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_C_mul,
      hop_pderiv_comm' k (a, i, false)]
    by_cases h : k = (a, i, true)
    · subst h; simp [Pi.single_apply]; ring
    · simp [Pi.single_apply, h, Ne.symm h]
  · rw [cr_true, cr_true]
    simp only [map_add, map_neg, map_smul, Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_C_mul,
      hop_pderiv_comm' k (a, i, true)]
    by_cases h : k = (a, i, false)
    · subst h; simp [Pi.single_apply]; ring
    · simp [Pi.single_apply, h, Ne.symm h]

/- English proof (translation)
Apply the tactic sequence `unfold sgn; rw [h]; split_ifs <;> norm_num`.
-/
theorem sgn_mul_same (ε : Fin m → Bool) {a b : Fin m} (h : ε a = ε b) : sgn ε a * sgn ε b = 1 := by
  unfold sgn; rw [h]; split_ifs <;> norm_num

/- English proof (translation)
Unfold `sgn`. Apply the tactic sequence `cases ha : ε a <;> cases hb : ε b <;> simp_all`.
-/
theorem sgn_mul_diff (ε : Fin m → Bool) {a b : Fin m} (h : ε a ≠ ε b) : sgn ε a * sgn ε b = -1 := by
  unfold sgn
  cases ha : ε a <;> cases hb : ε b <;> simp_all

/- English proof (translation)
Take `⟨a, i, e⟩` from `j`. Consider the cases of `e`. Rewrite using `[cr_false, cr_false, Derivation.leibniz, pderiv_C, smul_zero, add_zero, smul_eq_mul, smul_eq_C_mul, smul_eq_C_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[cr_true, cr_true, Derivation.leibniz, pderiv_C, smul_zero, add_zero, smul_eq_mul, smul_eq_C_mul, smul_eq_C_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hop_cr_C_mul (c : ℝ) (j : Fin m × Fin n × Bool) (r : ℂ) (Q : PX m n) : cr c j (C r * Q) = C r * cr c j Q := by
  obtain ⟨a, i, e⟩ := j
  cases e
  · rw [cr_false, cr_false, Derivation.leibniz, pderiv_C, smul_zero, add_zero, smul_eq_mul, smul_eq_C_mul, smul_eq_C_mul]; ring
  · rw [cr_true, cr_true, Derivation.leibniz, pderiv_C, smul_zero, add_zero, smul_eq_mul, smul_eq_C_mul, smul_eq_C_mul]; ring

section
variable (hB : FockBasic)
include hB

def hop_fL {c : ℝ} (hc : 0 < c) : PX m n →ₗ[ℂ] PX m n := IsLinearMap.mk' (fock c) (hB m n c hc).1

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fL_apply {c : ℝ} (hc : 0 < c) (p : PX m n) : hop_fL hB hc p = fock c p := rfl

/- English proof (translation)
The claim follows from `(hB m n c hc).2.2 k p`.
-/
theorem hop_fock_X_mul {c : ℝ} (hc : 0 < c) (k : Fin m × Fin n × Bool) (p : PX m n) :
    fock c (X k * p) = cr c k (fock c p) := (hB m n c hc).2.2 k p

/- English proof (translation)
The claim follows from `(hB m n c hc).1.map_add p q`.
-/
theorem fock_add'' {c : ℝ} (hc : 0 < c) (p q : PX m n) : fock c (p + q) = fock c p + fock c q :=
  (hB m n c hc).1.map_add p q

/- English proof (translation)
Rewrite using `[← fL_apply hB hc, map_zero]`.
-/
theorem fock_zero' {c : ℝ} (hc : 0 < c) : fock c (0 : PX m n) = 0 := by
  rw [← fL_apply hB hc, map_zero]

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C r => rw [hop_fock_C, pderiv_C, pderiv_C, fock_zero' hB hc, mul_zero]`. Consider the case `add p q hp hq`. Rewrite using `[fock_add'' hB hc, map_add, hp, hq, map_add, fock_add'' hB hc, mul_add]`. Consider the case `mul_X p j ih`.

Establish `hsplit : pderiv k (X j * p) = X j * pderiv k p + (if k = j then p else 0)`. Rewrite using `[Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]`. Distinguish the cases in `h : k = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Pi.single_apply, h, Ne.symm h]`. Establish `hcond : ((k.1, k.2.1, !k.2.2) = (j.1, j.2.1, !j.2.2)) ↔ k = j`. Take `⟨a, i, e⟩` from `j`. Take `⟨b, l, e'⟩` from `k`. Simplify using `[Prod.ext_iff]`.

Rewrite using `[mul_comm p (X j), hop_fock_X_mul hB hc, hop_pderiv_cr, ih, hsplit, fock_add'' hB hc, hop_fock_X_mul hB hc, hop_cr_C_mul]`. Distinguish the cases in `h : k = j`. Rewrite using `[if_pos (hcond.2 h), if_pos h]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg (mt hcond.1 h), if_neg h, fock_zero' hB hc]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hop_deriv_fock {c : ℝ} (hc : 0 < c) (k : Fin m × Fin n × Bool) (p : PX m n) :
    pderiv (k.1, k.2.1, !k.2.2) (fock c p) = C (2 * c : ℂ) * fock c (pderiv k p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => rw [hop_fock_C, pderiv_C, pderiv_C, fock_zero' hB hc, mul_zero]
  | add p q hp hq =>
    rw [fock_add'' hB hc, map_add, hp, hq, map_add, fock_add'' hB hc, mul_add]
  | mul_X p j ih =>
    have hsplit : pderiv k (X j * p) = X j * pderiv k p + (if k = j then p else 0) := by
      rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]
      by_cases h : k = j
      · subst h; simp
      · simp [Pi.single_apply, h, Ne.symm h]
    have hcond : ((k.1, k.2.1, !k.2.2) = (j.1, j.2.1, !j.2.2)) ↔ k = j := by
      obtain ⟨a, i, e⟩ := j
      obtain ⟨b, l, e'⟩ := k
      simp [Prod.ext_iff]
    rw [mul_comm p (X j), hop_fock_X_mul hB hc, hop_pderiv_cr, ih, hsplit, fock_add'' hB hc, hop_fock_X_mul hB hc, hop_cr_C_mul]
    by_cases h : k = j
    · rw [if_pos (hcond.2 h), if_pos h]; ring
    · rw [if_neg (mt hcond.1 h), if_neg h, fock_zero' hB hc]; ring

/- English proof (translation)
Establish `h1` using `hop_fock_X_mul hB hc (a, i, true) q`. Establish `h2` using `hop_deriv_fock hB hc (a, i, false) q`. Rewrite `h1` using `[cr_true, smul_eq_C_mul]`. Simplify using `only [Bool.not_false] at h2`. Rewrite using `[h1, h2]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hop_tr_false {c : ℝ} (hc : 0 < c) (a : Fin m) (i : Fin n) (q : PX m n) :
    C (2 * c : ℂ) * (X (a, i, false) * fock c q) = fock c (X (a, i, true) * q) + C (2 * c : ℂ) * fock c (pderiv (a, i, false) q) := by
  have h1 := hop_fock_X_mul hB hc (a, i, true) q
  have h2 := hop_deriv_fock hB hc (a, i, false) q
  rw [cr_true, smul_eq_C_mul] at h1
  simp only [Bool.not_false] at h2
  rw [h1, h2]; ring

/- English proof (translation)
Establish `h1` using `hop_fock_X_mul hB hc (a, i, false) q`. Establish `h2` using `hop_deriv_fock hB hc (a, i, true) q`. Rewrite `h1` using `[cr_false, smul_eq_C_mul]`. Simplify using `only [Bool.not_true] at h2`. Rewrite using `[h1, h2]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hop_tr_true {c : ℝ} (hc : 0 < c) (a : Fin m) (i : Fin n) (q : PX m n) :
    C (2 * c : ℂ) * (X (a, i, true) * fock c q) = fock c (X (a, i, false) * q) + C (2 * c : ℂ) * fock c (pderiv (a, i, true) q) := by
  have h1 := hop_fock_X_mul hB hc (a, i, false) q
  have h2 := hop_deriv_fock hB hc (a, i, true) q
  rw [cr_false, smul_eq_C_mul] at h1
  simp only [Bool.not_true] at h2
  rw [h1, h2]; ring

/- English proof (translation)
Introduce `m n ε c hc a b p`. Establish `hc0 : (c : ℂ) ≠ 0` using `by exact_mod_cast hc.ne'`. Use `set Y := fock c p with hY`. Establish `d1 : ∀ i, pderiv (a, i, false) Y = C (2 * c : ℂ) * fock c (pderiv (a, i, true) p)` using `fun i => hop_deriv_fock hB hc (a, i, true) p`. Establish `d2 : ∀ i, pderiv (b, i, true) Y = C (2 * c : ℂ) * fock c (pderiv (b, i, false) p)` using `fun i => hop_deriv_fock hB hc (b, i, false) p`.

Unfold `hOp Dop`. Rewrite using `[← fL_apply hB hc]`. Distinguish the cases in `h : ε a = ε b`. Rewrite using `[if_pos h, map_sum, sgn_mul_same ε h]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_sub, fL_apply, fL_apply, d1, d2]`. Establish `e1` using `hop_tr_false hB hc b i (pderiv (a, i, true) p)`. Establish `e2` using `hop_tr_true hB hc a i (pderiv (b, i, false) p)`. Rewrite `e1` using `[hop_pderiv_comm' (b, i, false) (a, i, true)]`. Simplify using `only [sub_self, mul_zero, map_zero, zero_mul, sub_zero, map_one, one_mul]`.

Take the linear combination `e1 - e2`. Rewrite using `[if_neg h, map_sum, sgn_mul_diff ε h]`. Establish `hab : a ≠ b` using `fun e => h (e ▸ rfl)`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_sub, map_smul, map_smul, fL_apply, fL_apply, d1, d2, smul_eq_C_mul, smul_eq_C_mul]`.

Establish `t2` using `hop_tr_true hB hc a i (pderiv (b, i, false) p)`. Establish `t3` using `hop_tr_true hB hc a i p`. Establish `t4` using `hop_tr_false hB hc b i (X (a, i, false) * p)`. Establish `e5 : pderiv (b, i, false) (X (a, i, false) * p) = X (a, i, false) * pderiv (b, i, false) p`. Rewrite using `[Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]`.

Establish `: ((b, i, false) : Fin m × Fin n × Bool) ≠ (a, i, false)` using `by simp [Ne.symm hab]`. Simplify using `[Pi.single_apply, this]`. Rewrite `t4` using `[e5]`. Rewrite `t2` using `[hop_pderiv_comm' (a, i, true) (b, i, false)]`. Establish `e6 : fock c (X (b, i, true) * (X (a, i, false) * p)) = fock c (X (a, i, false) * X (b, i, true) * p)`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hK : (C (1 / (2 * c) : ℂ) : PX m n) * C (2 * c : ℂ) = 1`. Rewrite using `[← map_mul, show (1 / (2 * c) : ℂ) * (2 * c) = 1 by field_simp, map_one]`. Establish `e7 : (c : ℂ) * (1 - -1) = 2 * c` using `by ring`.

Simplify using `only [e7, map_neg, map_one, neg_one_mul, neg_neg]`. Take the linear combination `t2 - X (b, i, false) * t3 - C (1 / (2 * c) : ℂ) * t4 - C (1 / (2 * c) : ℂ) * e6 + (X (b, i, false) * fock c (X (a, i, false) * p) - fock c (X (a, i, false) * pderiv (b, i, false) p)) * hK`.
-/
theorem fockHOp_of : FockHOp := by
  intro m n ε c hc a b p
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  set Y := fock c p with hY
  have d1 : ∀ i, pderiv (a, i, false) Y = C (2 * c : ℂ) * fock c (pderiv (a, i, true) p) := fun i => hop_deriv_fock hB hc (a, i, true) p
  have d2 : ∀ i, pderiv (b, i, true) Y = C (2 * c : ℂ) * fock c (pderiv (b, i, false) p) := fun i => hop_deriv_fock hB hc (b, i, false) p
  unfold hOp Dop
  rw [← fL_apply hB hc]
  by_cases h : ε a = ε b
  · rw [if_pos h, map_sum, sgn_mul_same ε h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sub, fL_apply, fL_apply, d1, d2]
    have e1 := hop_tr_false hB hc b i (pderiv (a, i, true) p)
    have e2 := hop_tr_true hB hc a i (pderiv (b, i, false) p)
    rw [hop_pderiv_comm' (b, i, false) (a, i, true)] at e1
    simp only [sub_self, mul_zero, map_zero, zero_mul, sub_zero, map_one, one_mul]
    linear_combination e1 - e2
  · rw [if_neg h, map_sum, sgn_mul_diff ε h]
    have hab : a ≠ b := fun e => h (e ▸ rfl)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sub, map_smul, map_smul, fL_apply, fL_apply, d1, d2, smul_eq_C_mul, smul_eq_C_mul]
    have t2 := hop_tr_true hB hc a i (pderiv (b, i, false) p)
    have t3 := hop_tr_true hB hc a i p
    have t4 := hop_tr_false hB hc b i (X (a, i, false) * p)
    have e5 : pderiv (b, i, false) (X (a, i, false) * p) = X (a, i, false) * pderiv (b, i, false) p := by
      rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]
      have : ((b, i, false) : Fin m × Fin n × Bool) ≠ (a, i, false) := by simp [Ne.symm hab]
      simp [Pi.single_apply, this]
    rw [e5] at t4
    rw [hop_pderiv_comm' (a, i, true) (b, i, false)] at t2
    have e6 : fock c (X (b, i, true) * (X (a, i, false) * p)) = fock c (X (a, i, false) * X (b, i, true) * p) := by
      congr 1; ring
    have hK : (C (1 / (2 * c) : ℂ) : PX m n) * C (2 * c : ℂ) = 1 := by
      rw [← map_mul, show (1 / (2 * c) : ℂ) * (2 * c) = 1 by field_simp, map_one]
    have e7 : (c : ℂ) * (1 - -1) = 2 * c := by ring
    simp only [e7, map_neg, map_one, neg_one_mul, neg_neg]
    linear_combination t2 - X (b, i, false) * t3 - C (1 / (2 * c) : ℂ) * t4 - C (1 / (2 * c) : ℂ) * e6 +
      (X (b, i, false) * fock c (X (a, i, false) * p) - fock c (X (a, i, false) * pderiv (b, i, false) p)) * hK

end

end PositivityTheory.Rg.Sw.LC
