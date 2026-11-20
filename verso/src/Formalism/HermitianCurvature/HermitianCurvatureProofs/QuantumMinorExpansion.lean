import Formalism.HermitianCurvature.StatementQr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainRecursionFromSingleDescent
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorCommutatorQuantumDet

open Finset Polynomial

noncomputable section

namespace Formalism.FourierDecayAlt.P.QuantumMinorExpansion

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.Qx6

section ring
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)

/- English proof (translation)
Use `split_ifs with h`. Substitute `h` using the available equality. Establish `h1 : bE (a c) (a ∘ c.succAbove) = a ∘ (c.cycleRange.symm)`. Use function extensionality and compare the values at `k`. Use `Fin.cases ?_ (fun k => ?_) k` and prove the remaining obligations.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite using `[h1, quantumMinorRowSkew_holds A n (N + 1) E a b _ w, Equiv.Perm.sign_symm, Fin.sign_cycleRange, zsmul_eq_mul]`. Simplify using the standard rewrite rules. Take `⟨c', rfl⟩` from `Fin.exists_succAbove_eq h`.

Conclude with `quantumMinor_eq_zero_of_row_eq quantumMinorRowSkew_holds E _ b w 0 c'.succ (Fin.succ_ne_zero _).symm (by simp)`.
-/
theorem cons_row {N : ℕ} (a b : Fin (N + 1) → Fin n) (q c : Fin (N + 1)) (w : ℂ) :
    qminor E (bE (a c) (a ∘ q.succAbove)) b w =
      if c = q then ((-1 : ℤ) ^ (q : ℕ)) • qminor E a b w else 0 := by
  split_ifs with h
  · subst h
    have h1 : bE (a c) (a ∘ c.succAbove) = a ∘ (c.cycleRange.symm) := by
      funext k
      refine Fin.cases ?_ (fun k => ?_) k
      · simp
      · simp
    rw [h1, quantumMinorRowSkew_holds A n (N + 1) E a b _ w, Equiv.Perm.sign_symm, Fin.sign_cycleRange, zsmul_eq_mul]
    simp
  · obtain ⟨c', rfl⟩ := Fin.exists_succAbove_eq h
    exact quantumMinor_eq_zero_of_row_eq quantumMinorRowSkew_holds E _ b w 0 c'.succ (Fin.succ_ne_zero _).symm (by simp)

/- English proof (translation)
Rewrite using `[← cons_row, quantum_minor_expand_last_line E expansion_last_line quantumMinorRowSkew_holds hE]`.
-/
theorem sumA (hE : GlRel E) {N : ℕ} (a b : Fin (N + 1) → Fin n) (q c : Fin (N + 1)) (w : ℂ) :
    ∑ x : Fin (N + 1), ((-1 : ℤ) ^ (x : ℕ)) •
        (qminor E (a ∘ q.succAbove) (b ∘ x.succAbove) (w - 1) * Tm E w (a c) (b x)) =
      if c = q then ((-1 : ℤ) ^ (q : ℕ)) • qminor E a b w else 0 := by
  rw [← cons_row, quantum_minor_expand_last_line E expansion_last_line quantumMinorRowSkew_holds hE]

/- English proof (translation)
Unfold `Tm`. Use `Commute.add_right ?_ (qDetCentral_of quantumMinorRowSkew_holds quantumMinorColSkew_holds A n E hE w c d)` and prove the remaining obligations. Use `split_ifs`. Conclude with `(Algebra.commutes v (qdet E w)).symm`. Conclude with `Commute.zero_right _`.
-/
theorem det_comm_Tm (hE : GlRel E) (w v : ℂ) (c d : Fin n) : Commute (qdet E w) (Tm E v c d) := by
  unfold Tm
  refine Commute.add_right ?_ (qDetCentral_of quantumMinorRowSkew_holds quantumMinorColSkew_holds A n E hE w c d)
  split_ifs
  · exact (Algebra.commutes v (qdet E w)).symm
  · exact Commute.zero_right _

/- English proof (translation)
Unfold `qminor`. Use `Commute.sum_right _ _ _ fun σ _ => ?_` and prove the remaining obligations. Use `Commute.mul_right (Int.commute_cast _ _) ?_` and prove the remaining obligations. Use `Commute.list_prod_right _ _ fun x hx => ?_` and prove the remaining obligations. Rewrite `hx` using `[List.mem_ofFn]`.

Take `⟨k, rfl⟩` from `hx`. Conclude with `det_comm_Tm E hE _ _ _ _`.
-/
theorem det_comm_minor (hE : GlRel E) {t : ℕ} (a b : Fin t → Fin n) (w v : ℂ) :
    Commute (qdet E w) (qminor E a b v) := by
  unfold qminor
  refine Commute.sum_right _ _ _ fun σ _ => ?_
  refine Commute.mul_right (Int.commute_cast _ _) ?_
  refine Commute.list_prod_right _ _ fun x hx => ?_
  rw [List.mem_ofFn] at hx
  obtain ⟨k, rfl⟩ := hx
  exact det_comm_Tm E hE _ _ _ _

/- English proof (translation)
Unfold `qminor`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_intCast, map_list_prod, List.map_ofFn]`. Use `congr 3`.

Use function extensionality and compare the values at `k`. Simplify using `only [Function.comp, Tm, map_add, hE']`. Use `split_ifs`. Rewrite using `[hf]`. Rewrite using `[map_zero]`.
-/
theorem map_qminor {B : Type} [Ring B] [Algebra ℂ B] (f : B →+* A)
    (hf : ∀ v, f (algebraMap ℂ B v) = algebraMap ℂ A v) (E' : Fin n → Fin n → B) (hE' : ∀ a b, f (E' a b) = E a b)
    {t : ℕ} (a b : Fin t → Fin n) (u : ℂ) : f (qminor E' a b u) = qminor E a b u := by
  unfold qminor
  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 3
  funext k
  simp only [Function.comp, Tm, map_add, hE']
  split_ifs
  · rw [hf]
  · rw [map_zero]

def EX (a b : Fin n) : A[X] := C (E a b) + if a = b then X else 0

/- English proof (translation)
Introduce `a b c d`. Establish `key : ∀ x y s t : A[X], (∀ p, s * p = p * s) → (∀ p, t * p = p * t) → (x + s) * (y + t) - (y + t) * (x + s) = x * y - y * x`. Introduce `x y s t hs ht`. Rewrite using `[add_mul, add_mul, mul_add, mul_add, mul_add, mul_add, hs y, hs t, ht x]`. Normalize the expressions using the abelian group laws.

Establish `hs : ∀ (P : Prop) [Decidable P] (p : A[X]), (if P then X else 0) * p = p * (if P then X else 0)`. Introduce `P _ p`. Use `split_ifs`. Conclude with `X_mul`. Simplify using the standard rewrite rules.

Unfold `EX`. Rewrite using `[key _ _ _ _ (hs _) (hs _), ← C_mul, ← C_mul, ← C_sub, hE a b c d]`. Apply the tactic sequence `by_cases h1 : b = c <;> by_cases h2 : d = a`. Substitute `h1` using the available equality. Substitute `h2` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h1, h2, Ne.symm h2]`. Simplify using `[h1, h2, Ne.symm h1]`. Simplify using `[h1, h2]`.
-/
theorem EX_gl (hE : GlRel E) : GlRel (EX E) := by
  intro a b c d
  have key : ∀ x y s t : A[X], (∀ p, s * p = p * s) → (∀ p, t * p = p * t) →
      (x + s) * (y + t) - (y + t) * (x + s) = x * y - y * x := by
    intro x y s t hs ht
    rw [add_mul, add_mul, mul_add, mul_add, mul_add, mul_add, hs y, hs t, ht x]
    abel
  have hs : ∀ (P : Prop) [Decidable P] (p : A[X]), (if P then X else 0) * p = p * (if P then X else 0) := by
    intro P _ p
    split_ifs
    · exact X_mul
    · simp
  unfold EX
  rw [key _ _ _ _ (hs _) (hs _), ← C_mul, ← C_mul, ← C_sub, hE a b c d]
  by_cases h1 : b = c <;> by_cases h2 : d = a
  · subst h1; subst h2; simp
  · simp [h1, h2, Ne.symm h2]
  · simp [h1, h2, Ne.symm h1]
  · simp [h1, h2]

/- English proof (translation)
Unfold `Tm EX`. Rewrite using `[Polynomial.algebraMap_apply]`. Apply the tactic sequence `split_ifs <;> simp [add_assoc]`.
-/
theorem Tm_EX (v : ℂ) (c p : Fin n) : Tm (EX E) v c p = C (Tm E v c p) + if c = p then X else 0 := by
  unfold Tm EX
  rw [Polynomial.algebraMap_apply]
  split_ifs <;> simp [add_assoc]

/- English proof (translation)
Establish `step : ∀ k, (∀ p, (Z p).coeff (k + 1) = 0) → ∀ p, (Z p).coeff k = 0`. Introduce `k hk c`. Establish `h1` using `congrArg (fun f => coeff f (k + 1)) (h c)`. Simplify using `only [Tm_EX, mul_add, Finset.sum_add_distrib, coeff_add, finsetSum_coeff, coeff_mul_C, hk, zero_mul, Finset.sum_const_zero, zero_add, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, coeff_mul_X, coeff_zero] at h1`. Conclude with `h1`.

Establish `all : ∀ N, (∀ k, N ≤ k → ∀ p, (Z p).coeff k = 0) → ∀ k p, (Z p).coeff k = 0`. Introduce `N`. Proceed by induction on `N with`. Consider the case `zero => intro h k p`. Conclude with `h k (Nat.zero_le _) p`.

Consider the case `succ N ih`. Introduce `h`. Apply `ih` to reduce the goal to its premises. Introduce `k hk`. Break down `Nat.eq_or_lt_of_le hk with rfl | hlt` into its components or cases.

Conclude with `step _ (h _ le_rfl)`. Conclude with `h k hlt`. Introduce `p`. Use extensionality with `k`. Rewrite using `[coeff_zero]`.

Use `all (Finset.univ.sup (fun p => (Z p).natDegree) + 1) ?_ k p` and prove the remaining obligations. Introduce `k hk p`. Apply `coeff_eq_zero_of_natDegree_lt` to reduce the goal to its premises. Use `Finset.le_sup (f := fun p => (Z p).natDegree) (Finset.mem_univ p)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem cancel (Z : Fin n → A[X]) (v : ℂ) (h : ∀ c, ∑ p, Z p * Tm (EX E) v c p = 0) : ∀ p, Z p = 0 := by
  have step : ∀ k, (∀ p, (Z p).coeff (k + 1) = 0) → ∀ p, (Z p).coeff k = 0 := by
    intro k hk c
    have h1 := congrArg (fun f => coeff f (k + 1)) (h c)
    simp only [Tm_EX, mul_add, Finset.sum_add_distrib, coeff_add, finsetSum_coeff, coeff_mul_C, hk, zero_mul,
      Finset.sum_const_zero, zero_add, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, coeff_mul_X,
      coeff_zero] at h1
    exact h1
  have all : ∀ N, (∀ k, N ≤ k → ∀ p, (Z p).coeff k = 0) → ∀ k p, (Z p).coeff k = 0 := by
    intro N
    induction N with
    | zero => intro h k p; exact h k (Nat.zero_le _) p
    | succ N ih =>
      intro h
      apply ih
      intro k hk
      rcases Nat.eq_or_lt_of_le hk with rfl | hlt
      · exact step _ (h _ le_rfl)
      · exact h k hlt
  intro p
  ext k
  rw [coeff_zero]
  refine all (Finset.univ.sup (fun p => (Z p).natDegree) + 1) ?_ k p
  intro k hk p
  apply coeff_eq_zero_of_natDegree_lt
  have := Finset.le_sup (f := fun p => (Z p).natDegree) (Finset.mem_univ p)
  omega

end ring

/- English proof (translation)
Use function extensionality and compare the values at `j`. Distinguish the cases in `h : i'.castSucc < q`. Rewrite using `[Fin.succAbove_of_castSucc_lt _ _ h, min_eq_left h.le, max_eq_right h.le]`. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only [skip2, Function.comp, Fin.succAbove, Fin.lt_def, Fin.val_castSucc] at h ⊢`.

Apply the tactic sequence `split_ifs <;> simp at * <;> omega`. Establish `h'` using `not_lt.mp h`. Establish `h2 : q ≤ q.succAbove i'`. Rewrite using `[Fin.succAbove_of_le_castSucc _ _ h']`. Conclude with `h'.trans (Fin.castSucc_lt_succ).le`.

Rewrite using `[min_eq_right h2, max_eq_left h2]`. Conclude with `skip_succ_double_identity m q i' j (by simpa [Fin.le_def] using h')`.
-/
theorem skip_two_succAbove_comp {m : ℕ} (q : Fin (m + 2)) (i' : Fin (m + 1)) :
    (skip2 (min (q.succAbove i') q) (max (q.succAbove i') q) : Fin m → Fin (m + 2)) =
      q.succAbove ∘ i'.succAbove := by
  funext j
  by_cases h : i'.castSucc < q
  · rw [Fin.succAbove_of_castSucc_lt _ _ h, min_eq_left h.le, max_eq_right h.le]
    apply Fin.ext
    simp only [skip2, Function.comp, Fin.succAbove, Fin.lt_def, Fin.val_castSucc] at h ⊢
    split_ifs <;> simp at * <;> omega
  · have h' := not_lt.mp h
    have h2 : q ≤ q.succAbove i' := by
      rw [Fin.succAbove_of_le_castSucc _ _ h']
      exact h'.trans (Fin.castSucc_lt_succ).le
    rw [min_eq_right h2, max_eq_left h2]
    exact skip_succ_double_identity m q i' j (by simpa [Fin.le_def] using h')

/- English proof (translation)
Unfold `eps`. Distinguish the cases in `h : x.castSucc < q`. Rewrite using `[Fin.succAbove_of_castSucc_lt _ _ h, if_pos (by simpa [Fin.lt_def] using h)]`. Simplify using the standard rewrite rules. Establish `h'` using `not_lt.mp h`.

Rewrite using `[Fin.succAbove_of_le_castSucc _ _ h', if_neg (by simp [Fin.le_def] at h' ⊢; omega)]`. Simplify using `[pow_succ]`.
-/
theorem sign_succ {m : ℕ} (q : Fin (m + 1)) (x : Fin m) :
    ((-1 : ℤ) ^ (x : ℕ)) = (-1) ^ ((q.succAbove x : Fin (m + 1)) : ℕ) * eps (q.succAbove x) q := by
  unfold eps
  by_cases h : x.castSucc < q
  · rw [Fin.succAbove_of_castSucc_lt _ _ h, if_pos (by simpa [Fin.lt_def] using h)]
    simp
  · have h' := not_lt.mp h
    rw [Fin.succAbove_of_le_castSucc _ _ h', if_neg (by simp [Fin.le_def] at h' ⊢; omega)]
    simp [pow_succ]

/- English proof (translation)
Apply the tactic sequence `unfold eps; split_ifs <;> simp`.
-/
theorem eps_sq {t : ℕ} (i q : Fin t) : eps i q * eps i q = 1 := by
  unfold eps; split_ifs <;> simp

/- English proof (translation)
Unfold `eps`. Establish `: (i : ℕ) ≠ q` using `fun h' => h (Fin.ext h')`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem eps_swap {t : ℕ} {i q : Fin t} (h : i ≠ q) : eps q i = -eps i q := by
  unfold eps
  have : (i : ℕ) ≠ q := fun h' => h (Fin.ext h')
  split_ifs <;> omega

section core
variable {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin (m + 2) → Fin (m + 2) → A)

/- English proof (translation)
Establish `h` using `sumA E hE id id q c (u + 1)`. Simplify using `only [Function.id_comp, id_eq, add_sub_cancel_right] at h`. Conclude with `h`.
-/
theorem quantum_minor_expansion_first_sum (hE : GlRel E) (q c : Fin (m + 2)) (u : ℂ) :
    ∑ p : Fin (m + 2), ((-1 : ℤ) ^ (p : ℕ)) • (qminor E q.succAbove p.succAbove u * Tm E (u + 1) c p) =
      if c = q then ((-1 : ℤ) ^ (q : ℕ)) • qdet E (u + 1) else 0 := by
  have h := sumA E hE id id q c (u + 1)
  simp only [Function.id_comp, id_eq, add_sub_cancel_right] at h
  exact h

/- English proof (translation)
Distinguish the cases in `hc : c = q`. Establish `hne : c ≠ q.succAbove i'` using `by rw [hc]; exact (Fin.succAbove_ne _ _).symm`. Rewrite using `[if_neg hne, if_pos hc, zero_add]`. Establish `hrows : q.succAbove ∘ i'.succAbove = (q.succAbove i').succAbove ∘ q'.succAbove`. Rewrite using `[← skip_two_succAbove_comp q i', ← skip_two_succAbove_comp (q.succAbove i') q', hq', min_comm, max_comm]`.

Establish `h` using `sumA E hE (q.succAbove i').succAbove j.succAbove q' q' (u + 1)`. Simplify using `only [add_sub_cancel_right, if_true, hq'] at h`. Rewrite using `[hrows, hc]`. Conclude with `h`. Take `⟨c', rfl⟩` from `Fin.exists_succAbove_eq hc`.

Rewrite using `[if_neg hc, add_zero]`. Establish `h` using `sumA E hE q.succAbove j.succAbove i' c' (u + 1)`. Simplify using `only [add_sub_cancel_right] at h`. Rewrite using `[h]`. Simplify using `only [(Fin.succAbove_right_injective (p := q)).eq_iff]`.
-/
theorem quantum_minor_expansion_second_sum (hE : GlRel E) (q : Fin (m + 2)) (i' : Fin (m + 1)) (q' : Fin (m + 1))
    (hq' : (q.succAbove i').succAbove q' = q) (j c : Fin (m + 2)) (u : ℂ) :
    ∑ x : Fin (m + 1), ((-1 : ℤ) ^ (x : ℕ)) •
        (qminor E (q.succAbove ∘ i'.succAbove) (j.succAbove ∘ x.succAbove) u * Tm E (u + 1) c (j.succAbove x)) =
      (if c = q.succAbove i' then ((-1 : ℤ) ^ (i' : ℕ)) • qminor E q.succAbove j.succAbove (u + 1) else 0) +
        (if c = q then ((-1 : ℤ) ^ (q' : ℕ)) • qminor E (q.succAbove i').succAbove j.succAbove (u + 1) else 0) := by
  by_cases hc : c = q
  · have hne : c ≠ q.succAbove i' := by rw [hc]; exact (Fin.succAbove_ne _ _).symm
    rw [if_neg hne, if_pos hc, zero_add]
    have hrows : q.succAbove ∘ i'.succAbove = (q.succAbove i').succAbove ∘ q'.succAbove := by
      rw [← skip_two_succAbove_comp q i', ← skip_two_succAbove_comp (q.succAbove i') q', hq', min_comm, max_comm]
    have h := sumA E hE (q.succAbove i').succAbove j.succAbove q' q' (u + 1)
    simp only [add_sub_cancel_right, if_true, hq'] at h
    rw [hrows, hc]
    exact h
  · obtain ⟨c', rfl⟩ := Fin.exists_succAbove_eq hc
    rw [if_neg hc, add_zero]
    have h := sumA E hE q.succAbove j.succAbove i' c' (u + 1)
    simp only [add_sub_cancel_right] at h
    rw [h]
    simp only [(Fin.succAbove_right_injective (p := q)).eq_iff]

def Xf (σ : ℤ) (q : Fin (m + 2)) (i' : Fin (m + 1)) (j : Fin (m + 2)) (u : ℂ) (p : Fin (m + 2)) : A :=
  ((-1 : ℤ) ^ (p : ℕ)) • (qminor E (q.succAbove i').succAbove j.succAbove (u + 1) * qminor E q.succAbove p.succAbove u -
      qminor E q.succAbove j.succAbove (u + 1) * qminor E (q.succAbove i').succAbove p.succAbove u) -
    (j.insertNth (α := fun _ => A) 0 (fun x : Fin (m + 1) => (σ * (-1 : ℤ) ^ (x : ℕ)) •
      (qdet E (u + 1) * qminor E (q.succAbove ∘ i'.succAbove) (j.succAbove ∘ x.succAbove) u))) p

/- English proof (translation)
Unfold `Xf`. Simplify using `only [sub_mul, Finset.sum_sub_distrib]`. Rewrite using `[Fin.sum_univ_succAbove (fun p => (j.insertNth (α := fun _ => A) 0 (fun x : Fin (m + 1) => (σ * (-1 : ℤ) ^ (x : ℕ)) • (qdet E (u + 1) * qminor E (q.succAbove ∘ i'.succAbove) (j.succAbove ∘ x.succAbove) u))) p * Tm E (u + 1) c p) j]`. Simplify using `only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, zero_mul, zero_add]`. Establish `e1 : ∀ (a : A) (r : Fin (m + 2)), ∑ p : Fin (m + 2), ((-1 : ℤ) ^ (p : ℕ)) • (a * qminor E r.succAbove p.succAbove u) * Tm E (u + 1) c p = a * (if c = r then ((-1 : ℤ) ^ (r : ℕ)) • qdet E (u + 1) else 0)`.

Introduce `a r`. Rewrite using `[← quantum_minor_expansion_first_sum E hE r c u, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, mul_smul_comm, mul_assoc]`. Establish `e2 : ∑ x : Fin (m + 1), (σ * (-1 : ℤ) ^ (x : ℕ)) • (qdet E (u + 1) * qminor E (q.succAbove ∘ i'.succAbove) (j.succAbove ∘ x.succAbove) u) * Tm E (u + 1) c (j.succAbove x) = σ • (qdet E (u + 1) * ((if c = q.succAbove i' then ((-1 : ℤ) ^ (i' : ℕ)) • qminor E q.succAbove j.succAbove …`.

Rewrite using `[← quantum_minor_expansion_second_sum E hE q i' q' hq' j c u, Finset.mul_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, mul_smul_comm, mul_assoc, smul_smul]`. Simplify using `only [smul_sub, sub_mul, Finset.sum_sub_distrib]`. Rewrite using `[e1, e1, e2]`.

Establish `c1` using `(det_comm_minor E hE (q.succAbove i').succAbove j.succAbove (u + 1) (u + 1)).eq`. Establish `c2` using `(det_comm_minor E hE q.succAbove j.succAbove (u + 1) (u + 1)).eq`. Establish `hne : q ≠ q.succAbove i'` using `(Fin.succAbove_ne _ _).symm`. Distinguish the cases in `h1 : c = q`. Substitute `h1` using the available equality.

Rewrite using `[if_pos rfl, if_neg hne, if_neg hne, if_pos rfl, mul_zero, sub_zero, zero_add, mul_smul_comm, mul_smul_comm, smul_smul, hσ1, c1, sub_self]`. Rewrite using `[if_neg h1, if_neg h1, mul_zero, zero_sub, add_zero]`. Distinguish the cases in `h2 : c = q.succAbove i'`. Rewrite using `[if_pos h2, if_pos h2, mul_smul_comm, mul_smul_comm, smul_smul, hσ2, c2, neg_smul, sub_neg_eq_add, neg_add_cancel]`. Rewrite using `[if_neg h2, if_neg h2, mul_zero, mul_zero, smul_zero, neg_zero, sub_zero]`.
-/
theorem step1 (hE : GlRel E) (σ : ℤ) (q : Fin (m + 2)) (i' : Fin (m + 1)) (q' : Fin (m + 1))
    (hq' : (q.succAbove i').succAbove q' = q) (hσ1 : σ * (-1) ^ (q' : ℕ) = (-1) ^ (q : ℕ))
    (hσ2 : σ * (-1) ^ (i' : ℕ) = -(-1) ^ ((q.succAbove i' : Fin (m + 2)) : ℕ)) (j c : Fin (m + 2)) (u : ℂ) :
    ∑ p : Fin (m + 2), Xf E σ q i' j u p * Tm E (u + 1) c p = 0 := by
  unfold Xf
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [Fin.sum_univ_succAbove (fun p => (j.insertNth (α := fun _ => A) 0 (fun x : Fin (m + 1) => (σ * (-1 : ℤ) ^ (x : ℕ)) •
      (qdet E (u + 1) * qminor E (q.succAbove ∘ i'.succAbove) (j.succAbove ∘ x.succAbove) u))) p * Tm E (u + 1) c p) j]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, zero_mul, zero_add]
  have e1 : ∀ (a : A) (r : Fin (m + 2)), ∑ p : Fin (m + 2), ((-1 : ℤ) ^ (p : ℕ)) • (a * qminor E r.succAbove p.succAbove u) *
      Tm E (u + 1) c p = a * (if c = r then ((-1 : ℤ) ^ (r : ℕ)) • qdet E (u + 1) else 0) := by
    intro a r
    rw [← quantum_minor_expansion_first_sum E hE r c u, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, mul_assoc]
  have e2 : ∑ x : Fin (m + 1), (σ * (-1 : ℤ) ^ (x : ℕ)) •
      (qdet E (u + 1) * qminor E (q.succAbove ∘ i'.succAbove) (j.succAbove ∘ x.succAbove) u) *
        Tm E (u + 1) c (j.succAbove x) = σ • (qdet E (u + 1) *
      ((if c = q.succAbove i' then ((-1 : ℤ) ^ (i' : ℕ)) • qminor E q.succAbove j.succAbove (u + 1) else 0) +
        (if c = q then ((-1 : ℤ) ^ (q' : ℕ)) • qminor E (q.succAbove i').succAbove j.succAbove (u + 1) else 0))) := by
    rw [← quantum_minor_expansion_second_sum E hE q i' q' hq' j c u, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, mul_assoc, smul_smul]
  simp only [smul_sub, sub_mul, Finset.sum_sub_distrib]
  rw [e1, e1, e2]
  have c1 := (det_comm_minor E hE (q.succAbove i').succAbove j.succAbove (u + 1) (u + 1)).eq
  have c2 := (det_comm_minor E hE q.succAbove j.succAbove (u + 1) (u + 1)).eq
  have hne : q ≠ q.succAbove i' := (Fin.succAbove_ne _ _).symm
  by_cases h1 : c = q
  · subst h1
    rw [if_pos rfl, if_neg hne, if_neg hne, if_pos rfl, mul_zero, sub_zero, zero_add, mul_smul_comm, mul_smul_comm,
      smul_smul, hσ1, c1, sub_self]
  · rw [if_neg h1, if_neg h1, mul_zero, zero_sub, add_zero]
    by_cases h2 : c = q.succAbove i'
    · rw [if_pos h2, if_pos h2, mul_smul_comm, mul_smul_comm, smul_smul, hσ2, c2, neg_smul, sub_neg_eq_add,
        neg_add_cancel]
    · rw [if_neg h2, if_neg h2, mul_zero, mul_zero, smul_zero, neg_zero, sub_zero]

end core

section final
variable {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin (m + 2) → Fin (m + 2) → A)

/- English proof (translation)
Establish `hne : q.succAbove i' ≠ q` using `Fin.succAbove_ne _ _`. Establish `hsq` using `eps_sq (q.succAbove i') q`. Prove the components needed by the constructor for the conclusion. Establish `h` using `sign_succ (q.succAbove i') q'`. Rewrite `h` using `[hq', eps_swap hne]`.

Rewrite using `[h]`. Take the linear combination `((-1) ^ (q : ℕ)) * hsq`. Rewrite using `[sign_succ q i']`. Take the linear combination `(-(-1) ^ ((q.succAbove i' : Fin (m + 2)) : ℕ)) * hsq`.
-/
theorem signs (q : Fin (m + 2)) (i' q' : Fin (m + 1)) (hq' : (q.succAbove i').succAbove q' = q) :
    (-eps (q.succAbove i') q) * (-1) ^ (q' : ℕ) = (-1) ^ (q : ℕ) ∧
      (-eps (q.succAbove i') q) * (-1) ^ (i' : ℕ) = -(-1) ^ ((q.succAbove i' : Fin (m + 2)) : ℕ) := by
  have hne : q.succAbove i' ≠ q := Fin.succAbove_ne _ _
  have hsq := eps_sq (q.succAbove i') q
  constructor
  · have h := sign_succ (q.succAbove i') q'
    rw [hq', eps_swap hne] at h
    rw [h]
    linear_combination ((-1) ^ (q : ℕ)) * hsq
  · rw [sign_succ q i']
    linear_combination (-(-1) ^ ((q.succAbove i' : Fin (m + 2)) : ℕ)) * hsq

/- English proof (translation)
Take `⟨q', hq'⟩` from `Fin.exists_succAbove_eq (Fin.succAbove_ne q i').symm`. Take `⟨h1, h2⟩` from `signs q i' q' hq'`. Conclude with `cancel E (Xf (EX E) _ q i' j u) (u + 1) (fun c => step1 (EX E) (EX_gl E hE) _ q i' q' hq' h1 h2 j c u) p`.
-/
theorem Xf_poly (hE : GlRel E) (u : ℂ) (q : Fin (m + 2)) (i' : Fin (m + 1)) (j p : Fin (m + 2)) :
    Xf (EX E) (-eps (q.succAbove i') q) q i' j u p = 0 := by
  obtain ⟨q', hq'⟩ := Fin.exists_succAbove_eq (Fin.succAbove_ne q i').symm
  obtain ⟨h1, h2⟩ := signs q i' q' hq'
  exact cancel E (Xf (EX E) _ q i' j u) (u + 1)
    (fun c => step1 (EX E) (EX_gl E hE) _ q i' q' hq' h1 h2 j c u) p

/- English proof (translation)
Rewrite using `[← mul_pow]`. Simplify using the standard rewrite rules.
-/
theorem sq_one (k : ℕ) : ((-1 : ℤ) ^ k * (-1) ^ k) = 1 := by
  rw [← mul_pow]; simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Establish `h0` using `h j`. Unfold `Xf at h0`. Rewrite `h0` using `[Fin.insertNth_apply_same, sub_zero]`. Establish `h1` using `congrArg (fun y => ((-1 : ℤ) ^ (j : ℕ)) • y) h0`.

Simplify using `only [smul_smul, sq_one, one_smul, smul_zero] at h1`. Conclude with `h1`. Introduce `x`. Establish `h0` using `h (j.succAbove x)`. Unfold `Xf at h0`.

Rewrite `h0` using `[Fin.insertNth_apply_succAbove, sub_eq_zero]`. Establish `h1` using `congrArg (fun y => ((-1 : ℤ) ^ ((j.succAbove x : Fin (m + 2)) : ℕ)) • y) h0`. Simplify using `only [smul_smul, sq_one, one_smul] at h1`. Rewrite using `[h1, zsmul_eq_mul]`.
-/
theorem of_Xf (σ : ℤ) (u : ℂ) (q : Fin (m + 2)) (i' : Fin (m + 1)) (j : Fin (m + 2))
    (h : ∀ p, Xf E σ q i' j u p = 0) :
    (qminor E (q.succAbove i').succAbove j.succAbove (u + 1) * qminor E q.succAbove j.succAbove u -
      qminor E q.succAbove j.succAbove (u + 1) * qminor E (q.succAbove i').succAbove j.succAbove u = 0) ∧
    ∀ x : Fin (m + 1),
      qminor E (q.succAbove i').succAbove j.succAbove (u + 1) * qminor E q.succAbove (j.succAbove x).succAbove u -
        qminor E q.succAbove j.succAbove (u + 1) * qminor E (q.succAbove i').succAbove (j.succAbove x).succAbove u =
      (((-1) ^ ((j.succAbove x : Fin (m + 2)) : ℕ) * (σ * (-1) ^ (x : ℕ)) : ℤ) : A) *
        (qdet E (u + 1) * qminor E (q.succAbove ∘ i'.succAbove) (j.succAbove ∘ x.succAbove) u) := by
  constructor
  · have h0 := h j
    unfold Xf at h0
    rw [Fin.insertNth_apply_same, sub_zero] at h0
    have h1 := congrArg (fun y => ((-1 : ℤ) ^ (j : ℕ)) • y) h0
    simp only [smul_smul, sq_one, one_smul, smul_zero] at h1
    exact h1
  · intro x
    have h0 := h (j.succAbove x)
    unfold Xf at h0
    rw [Fin.insertNth_apply_succAbove, sub_eq_zero] at h0
    have h1 := congrArg (fun y => ((-1 : ℤ) ^ ((j.succAbove x : Fin (m + 2)) : ℕ)) • y) h0
    simp only [smul_smul, sq_one, one_smul] at h1
    rw [h1, zsmul_eq_mul]

/- English proof (translation)
Take `⟨h0, h1⟩` from `of_Xf (EX E) _ u q i' j (Xf_poly E hE u q i' j)`. Establish `hf : ∀ v : ℂ, (constantCoeff : A[X] →+* A) (algebraMap ℂ A[X] v) = algebraMap ℂ A v`. Introduce `v`. Rewrite using `[Polynomial.algebraMap_apply]`. Simplify using the standard rewrite rules.

Establish `hE' : ∀ a b, (constantCoeff : A[X] →+* A) (EX E a b) = E a b`. Introduce `a b`. Unfold `EX`. Apply the tactic sequence `split_ifs <;> simp`. Establish `F : ∀ {t : ℕ} (a b : Fin t → Fin (m + 2)) (w : ℂ), (constantCoeff : A[X] →+* A) (qminor (EX E) a b w) = qminor E a b w` using `fun a b w => map_qminor E constantCoeff hf (EX E) hE' a b w`.

Prove the components needed by the constructor for the conclusion. Establish `h2` using `congrArg (constantCoeff : A[X] →+* A) h0`. Simplify `h2` using `only [map_sub, map_mul, F, map_zero]`. Introduce `x`. Establish `h2` using `congrArg (constantCoeff : A[X] →+* A) (h1 x)`.

Simplify using `only [map_sub, map_mul, F, map_intCast, qdet] at h2`. Rewrite using `[h2]`. Establish `hsg : ((-1 : ℤ) ^ ((j.succAbove x : Fin (m + 2)) : ℕ) * (-eps (q.succAbove i') q * (-1) ^ (x : ℕ))) = eps (q.succAbove i') q * eps j (j.succAbove x)`. Rewrite using `[sign_succ j x, eps_swap (Fin.succAbove_ne j x).symm]`. Take the linear combination `(eps (q.succAbove i') q * eps j (j.succAbove x)) * sq_one ((j.succAbove x : Fin (m + 2)) : ℕ)`.

Rewrite using `[hsg]`. Both sides reduce to the same expression.
-/
theorem jacS (hE : GlRel E) (u : ℂ) (q : Fin (m + 2)) (i' : Fin (m + 1)) (j : Fin (m + 2)) :
    (qminor E (q.succAbove i').succAbove j.succAbove (u + 1) * qminor E q.succAbove j.succAbove u -
      qminor E q.succAbove j.succAbove (u + 1) * qminor E (q.succAbove i').succAbove j.succAbove u = 0) ∧
    ∀ x : Fin (m + 1),
      qminor E (q.succAbove i').succAbove j.succAbove (u + 1) * qminor E q.succAbove (j.succAbove x).succAbove u -
        qminor E q.succAbove j.succAbove (u + 1) * qminor E (q.succAbove i').succAbove (j.succAbove x).succAbove u =
      ((eps (q.succAbove i') q * eps j (j.succAbove x) : ℤ) : A) *
        (qdet E (u + 1) * qminor E (q.succAbove ∘ i'.succAbove) (j.succAbove ∘ x.succAbove) u) := by
  obtain ⟨h0, h1⟩ := of_Xf (EX E) _ u q i' j (Xf_poly E hE u q i' j)
  have hf : ∀ v : ℂ, (constantCoeff : A[X] →+* A) (algebraMap ℂ A[X] v) = algebraMap ℂ A v := by
    intro v
    rw [Polynomial.algebraMap_apply]
    simp
  have hE' : ∀ a b, (constantCoeff : A[X] →+* A) (EX E a b) = E a b := by
    intro a b
    unfold EX
    split_ifs <;> simp
  have F : ∀ {t : ℕ} (a b : Fin t → Fin (m + 2)) (w : ℂ),
      (constantCoeff : A[X] →+* A) (qminor (EX E) a b w) = qminor E a b w :=
    fun a b w => map_qminor E constantCoeff hf (EX E) hE' a b w
  constructor
  · have h2 := congrArg (constantCoeff : A[X] →+* A) h0
    simpa only [map_sub, map_mul, F, map_zero] using h2
  · intro x
    have h2 := congrArg (constantCoeff : A[X] →+* A) (h1 x)
    simp only [map_sub, map_mul, F, map_intCast, qdet] at h2
    rw [h2]
    have hsg : ((-1 : ℤ) ^ ((j.succAbove x : Fin (m + 2)) : ℕ) * (-eps (q.succAbove i') q * (-1) ^ (x : ℕ))) =
        eps (q.succAbove i') q * eps j (j.succAbove x) := by
      rw [sign_succ j x, eps_swap (Fin.succAbove_ne j x).symm]
      linear_combination (eps (q.succAbove i') q * eps j (j.succAbove x)) *
        sq_one ((j.succAbove x : Fin (m + 2)) : ℕ)
    rw [hsg]
    rfl

/- English proof (translation)
Establish `hs : ∀ r : Fin (m + 2), (skip1 r : Fin (m + 1) → Fin (m + 2)) = r.succAbove` using `fun r => funext (skip_succ_identity (m + 1) r)`. Take `⟨i', rfl⟩` from `Fin.exists_succAbove_eq hiq`. Take `⟨h0, h1⟩` from `jacS E hE u q i' j`. Distinguish the cases in `hjp : j = p`. Substitute `hjp` using the available equality.

Rewrite using `[if_pos (Or.inr rfl), hs, hs, hs]`. Conclude with `h0`. Take `⟨x, rfl⟩` from `Fin.exists_succAbove_eq (Ne.symm hjp)`. Rewrite using `[if_neg (by tauto), skip_two_succAbove_comp q i', min_comm j, max_comm j, skip_two_succAbove_comp j x, hs, hs, hs, hs]`. Conclude with `h1 x`.
-/
theorem jac2 (hE : GlRel E) (u : ℂ) (i q j p : Fin (m + 2)) (hiq : i ≠ q) :
    qminor E (skip1 i) (skip1 j) (u + 1) * qminor E (skip1 q) (skip1 p) u -
        qminor E (skip1 q) (skip1 j) (u + 1) * qminor E (skip1 i) (skip1 p) u =
      if i = q ∨ j = p then 0 else
        ((eps i q * eps j p : ℤ) : A) *
          (qdet E (u + 1) * qminor E (skip2 (min i q) (max i q)) (skip2 (min j p) (max j p)) u) := by
  have hs : ∀ r : Fin (m + 2), (skip1 r : Fin (m + 1) → Fin (m + 2)) = r.succAbove :=
    fun r => funext (skip_succ_identity (m + 1) r)
  obtain ⟨i', rfl⟩ := Fin.exists_succAbove_eq hiq
  obtain ⟨h0, h1⟩ := jacS E hE u q i' j
  by_cases hjp : j = p
  · subst hjp
    rw [if_pos (Or.inr rfl), hs, hs, hs]
    exact h0
  · obtain ⟨x, rfl⟩ := Fin.exists_succAbove_eq (Ne.symm hjp)
    rw [if_neg (by tauto), skip_two_succAbove_comp q i', min_comm j, max_comm j, skip_two_succAbove_comp j x, hs, hs, hs, hs]
    exact h1 x

end final

end Formalism.FourierDecayAlt.P.QuantumMinorExpansion

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr in
/- English proof (translation)
Introduce `A _ _ t E hE u i q j p`. Distinguish the cases in `hiq : i = q`. Substitute `hiq` using the available equality. Simplify using the standard rewrite rules. Break down `t with _ | _ | m` into its components or cases.

Conclude with `i.elim0`. Conclude with `absurd (Fin.ext (by omega)) hiq`. Conclude with `Formalism.FourierDecayAlt.P.QuantumMinorExpansion.jac2 E hE u i q j p hiq`.
-/
theorem Formalism.FourierDecayAlt.P.quantum_jacobi_identity : Formalism.FourierDecayAlt.Qr.QJacobi := by
  intro A _ _ t E hE u i q j p
  by_cases hiq : i = q
  · subst hiq
    simp
  rcases t with _ | _ | m
  · exact i.elim0
  · exact absurd (Fin.ext (by omega)) hiq
  · exact Formalism.FourierDecayAlt.P.QuantumMinorExpansion.jac2 E hE u i q j p hiq
