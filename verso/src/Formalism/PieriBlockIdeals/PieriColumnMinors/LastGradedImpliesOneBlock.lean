import Formalism.PieriBlockIdeals.BranchingBoundLastGradedOneRow
import Formalism.PieriBlockIdeals.PieriColumnMinors.DividedPowerZeroZeroVector

open MvPolynomial

namespace Formalism.CohomologicalDescent.LD

open Formalism.GradedWeylDivisibility

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem lastGradedImpliesLast : LastGradedImpliesLast := by
  intro h l p q w M lam2 hl ha hw eL heL i μ hd
  have h0 : Antitone (0 : Fin (q + p) → ℤ) := fun _ _ _ => le_rfl
  refine h l p q w M lam2 0 hl ha hw h0 0 eL (fun μ2 _ => heL μ2) i μ hd ?_
  simp [depth2]

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem last_graded_implies_one_block' : OneRowBoundOfLastGraded :=
  fun h l q w M lam2 ξ hl ha hw hξ => h l 1 q w M lam2 ξ hl ha hw hξ

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem depth2Levi : Depth2Levi := by
  intro p q w lam2 μ2 ξ
  unfold depth2 blockWtLast
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem depth_two_block_eq_sum_diff (p q w : ℕ) (lam2 : Fin q → ℕ) (μ : Fin (q + p) → ℕ) :
    depth2 (fun a : Fin (q + p) => if a.val < q then 1 else 0) (blockWtLast p q w lam2) μ =
      ((∑ b, lam2 b : ℕ) : ℤ) - ((∑ b : Fin q, μ (Fin.castAdd p b) : ℕ) : ℤ) := by
  unfold depth2 blockWtLast
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Finset.sum_sub_distrib]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem sum_block_weight_last (p q w : ℕ) (lam2 : Fin q → ℕ) :
    ∑ a, blockWtLast p q w lam2 a = ∑ b, lam2 b + p * w := by
  unfold blockWtLast
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Replace the relevant objects with their definitions. Replace the chosen expression with an arbitrary variable. Use linear arithmetic over natural numbers and integers.
-/
theorem depthLastIff : DepthLastIff := by
  intro p q w i lam2 μ hsum
  rw [depth_two_block_eq_sum_diff, sum_block_weight_last, Fin.sum_univ_add] at *
  unfold IsDepthLast
  generalize p * w = pw at *
  omega

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Replace the relevant objects with their definitions. Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem depth2Dual : Depth2Dual := by
  intro r M ξ lam μ hl hm
  constructor
  · unfold depth2
    rw [← Equiv.sum_comp Fin.revPerm fun a => ξ a * ((lam a : ℤ) - (μ a : ℤ))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Nat.cast_sub (hl _), Nat.cast_sub (hm _)]
    simp only [Fin.revPerm_apply]
    ring
  · intro hξ a b hab
    exact neg_le_neg (hξ (Fin.rev_le_rev.mpr hab))

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mem_shapes_iff (p w i q : ℕ) (lam2 tau : Fin q → ℕ) :
    tau ∈ shapes p w i lam2 ↔ (∀ a, lam2 a ≤ tau a ∧ tau a ≤ lam2 a + i) ∧
      (∀ a b : Fin q, a ≤ b → tau b ≤ tau a) ∧ ∑ a, tau a = ∑ a, lam2 a + i ∧
      (∀ b : Fin q, ∀ j < tau b, colLen lam2 tau j ≤ p) ∧ boxesOfContent lam2 tau (w : ℤ) = 0 := by
  simp [shapes, Fintype.mem_piFinset, Finset.mem_Icc]

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations.

Apply the first step, then apply the next step to every resulting obligation.
-/
theorem boxes_of_content_shift (q c : ℕ) (lam2 tau : Fin q → ℕ) (x : ℤ) :
    boxesOfContent (fun b => lam2 b + c) (fun b => tau b + c) (x + (c : ℤ)) = boxesOfContent lam2 tau x := by
  unfold boxesOfContent
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  push_cast
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> omega

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem column_length_shift (q c : ℕ) (lam2 tau : Fin q → ℕ) (j : ℕ) :
    colLen (fun b => lam2 b + c) (fun b => tau b + c) (j + c) = colLen lam2 tau j := by
  unfold colLen
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> omega

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem column_length_below_shift (q c : ℕ) (lam2 tau : Fin q → ℕ) (j : ℕ) (hj : j < c) :
    colLen (fun b => lam2 b + c) (fun b => tau b + c) j = 0 := by
  unfold colLen
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro a _ ⟨h1, _⟩
  have h1' : lam2 a + c ≤ j := h1
  omega

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem shapes_shift_iff (p w i q c : ℕ) (lam2 tau : Fin q → ℕ) :
    (fun b => tau b + c) ∈ shapes p (w + c) i (fun b => lam2 b + c) ↔ tau ∈ shapes p w i lam2 := by
  rw [mem_shapes_iff, mem_shapes_iff]
  have hbx : boxesOfContent (fun b => lam2 b + c) (fun b => tau b + c) ((w + c : ℕ) : ℤ) =
      boxesOfContent lam2 tau (w : ℤ) := by
    rw [Nat.cast_add]
    exact boxes_of_content_shift q c lam2 tau w
  rw [hbx, Finset.sum_add_distrib, Finset.sum_add_distrib]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨fun a => ?_, fun a b hab => ?_, by omega, fun b j hj => ?_, h5⟩
    · have := h1 a
      omega
    · have := h2 a b hab
      omega
    · rw [← column_length_shift q c]
      exact h4 b (j + c) (by omega)
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨fun a => ?_, fun a b hab => ?_, by omega, fun b j hj => ?_, h5⟩
    · have := h1 a
      omega
    · have := h2 a b hab
      omega
    · by_cases hjc : j < c
      · rw [column_length_below_shift q c lam2 tau j hjc]
        exact Nat.zero_le _
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + c := ⟨j - c, by omega⟩
        rw [column_length_shift]
        exact h4 b j' (by omega)

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite the hypotheses and the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem multiplicity_shift_invariant (p w i q c : ℕ) (lam2 : Fin q → ℕ) (x : ℤ) :
    mu p (w + c) i (fun b => lam2 b + c) (x + (c : ℤ)) = mu p w i lam2 x := by
  unfold mu
  apply le_antisymm
  · refine Finset.sup_le fun tau' htau' => ?_
    have hge : ∀ a, c ≤ tau' a := fun a => by
      have := ((mem_shapes_iff _ _ _ _ _ _).mp htau').1 a
      omega
    have he : tau' = fun b => (tau' b - c) + c := funext fun b => by
      have := hge b
      omega
    rw [he] at htau' ⊢
    rw [boxes_of_content_shift]
    exact Finset.le_sup (f := fun tau => boxesOfContent lam2 tau x) ((shapes_shift_iff _ _ _ _ _ _ _).mp htau')
  · refine Finset.sup_le fun tau htau => ?_
    rw [← boxes_of_content_shift q c lam2 tau x]
    exact Finset.le_sup (f := fun tau => boxesOfContent (fun b => lam2 b + c) tau (x + (c : ℤ)))
      ((shapes_shift_iff _ _ _ _ _ _ _).mpr htau)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem dnShift : DnShift := by
  intro p w i q c lam2 hb
  unfold Dn
  have hr : q + (w + c) + i = c + (q + w + i) := by omega
  rw [hr, Finset.prod_range_add]
  have h1 : ∏ k ∈ Finset.range c, (((w + c : ℕ) : ℤ) - ((k : ℤ) - (q : ℤ))) ^
      mu p (w + c) i (fun b => lam2 b + c) ((k : ℤ) - (q : ℤ)) = 1 := by
    refine Finset.prod_eq_one fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    have hz : mu p (w + c) i (fun b => lam2 b + c) ((k : ℤ) - (q : ℤ)) = 0 := by
      by_contra hne
      have := (muRange p (w + c) i q c (fun b => lam2 b + c) _
        (fun b => ⟨Nat.le_add_left _ _, Nat.add_le_add_right (hb b) c⟩) hne).1
      omega
    rw [hz, pow_zero]
  rw [h1, one_mul]
  refine Finset.prod_congr rfl fun k _ => ?_
  have e1 : (((c + k : ℕ) : ℤ) - (q : ℤ)) = ((k : ℤ) - (q : ℤ)) + (c : ℤ) := by
    push_cast
    ring
  rw [e1, multiplicity_shift_invariant]
  congr 1
  push_cast
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.

A detailed English derivation is pending.
-/
theorem dnLastIndep : DnLastIndep := by
  intro p w i q M M' lam2 hwM hb hMM
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hMM
  have e1 : M + c - w = (M - w) + c := by omega
  have e2 : (fun b : Fin q => M + c - lam2 (Fin.rev b)) = fun b => (M - lam2 (Fin.rev b)) + c :=
    funext fun b => by
      have := hb (Fin.rev b)
      omega
  rw [e1, e2]
  exact dnShift p (M - w) i q c (fun b => M - lam2 (Fin.rev b)) fun b => by
    have := hb (Fin.rev b)
    omega

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem dominance_of_nabla_weight (r : ℕ) (ν μ : Fin r → ℕ) (hν : Antitone ν) (x : MvPolynomial (Fin r × Fin r) ℤ)
    (hx : x ∈ nablaWt r ν μ) (hne : x ≠ 0) :
    (∀ k : ℕ, (∑ a : Fin r with a.val < k, μ a) ≤ ∑ a : Fin r with a.val < k, ν a) ∧ ∑ a, μ a = ∑ a, ν a := by
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hne
  have hdom := dualWeylDominanceZ r r ν le_rfl hν x hx.1 d hd
  have hwt : Finsupp.weight (rowW r r) d = μ := hx.2 (MvPolynomial.mem_support_iff.mp hd)
  have h1 : ∀ a, rowDeg d a = μ a := fun a => by rw [← ldrow_weight_rowW, hwt]
  have h2 : ∀ a : Fin r, rowNu (r := r) ν a = ν a := fun a => by
    unfold rowNu
    rw [dif_pos a.isLt]
  simp only [h1, h2] at hdom
  exact hdom

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exp_le_of_nonzero_weight_vectors (l r : ℕ) (ν μ : Fin r → ℕ) (e : ℕ) (hl : l.Prime)
    (H : ∀ x ∈ nablaWt r ν μ, x ≠ 0 → ExpLe l r ν μ e) : ExpLe l r ν μ e := by
  intro x hx
  by_cases h0 : x = 0
  · refine ⟨1, (Nat.prime_iff_prime_int.mp hl).not_dvd_one, ?_⟩
    rw [h0, smul_zero]
    exact Submodule.zero_mem _
  · exact H x hx h0 x hx

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. It suffices to derive a contradiction.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem block_weight_last_antitone (p q w : ℕ) (lam2 : Fin q → ℕ) (ha : Antitone lam2) (hb : ∀ b, w ≤ lam2 b) :
    Antitone (blockWtLast p q w lam2) := by
  intro a b
  unfold blockWtLast
  refine Fin.addCases (fun a' => ?_) (fun a' => ?_) a <;>
    refine Fin.addCases (fun b' => ?_) (fun b' => ?_) b <;> intro hab
  · rw [Fin.append_left, Fin.append_left]
    refine ha ?_
    have h1 : (Fin.castAdd p a').val ≤ (Fin.castAdd p b').val := hab
    simp only [Fin.val_castAdd] at h1
    exact Fin.le_def.mpr h1
  · rw [Fin.append_left, Fin.append_right]
    exact hb a'
  · exfalso
    have h1 : (Fin.natAdd q a').val ≤ (Fin.castAdd p b').val := hab
    have h2 := b'.isLt
    simp only [Fin.val_natAdd, Fin.val_castAdd] at h1
    omega
  · rw [Fin.append_right, Fin.append_right]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem sum_lt_q_eq_sum_cast_add (p q : ℕ) (f : Fin (q + p) → ℕ) :
    (∑ a : Fin (q + p) with a.val < q, f a) = ∑ b : Fin q, f (Fin.castAdd p b) := by
  rw [Finset.sum_filter, Fin.sum_univ_add]
  simp

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem depth_exists_last_block (p q w : ℕ) (lam2 : Fin q → ℕ) (ha : Antitone lam2) (hb : ∀ b, w ≤ lam2 b)
    (μ : Fin (q + p) → ℕ) (x : MvPolynomial (Fin (q + p) × Fin (q + p)) ℤ)
    (hx : x ∈ nablaWt (q + p) (blockWtLast p q w lam2) μ) (hne : x ≠ 0) :
    ∃ i : ℕ, IsDepthLast p q w μ i ∧
      depth2 (fun a : Fin (q + p) => if a.val < q then 1 else 0) (blockWtLast p q w lam2) μ = (i : ℤ) := by
  obtain ⟨hdom, htot⟩ := dominance_of_nabla_weight _ _ μ (block_weight_last_antitone p q w lam2 ha hb) x hx hne
  have h1 := hdom q
  rw [sum_lt_q_eq_sum_cast_add, sum_lt_q_eq_sum_cast_add] at h1
  have h2 : ∀ b : Fin q, blockWtLast p q w lam2 (Fin.castAdd p b) = lam2 b := fun b => Fin.append_left _ _ b
  simp only [h2] at h1
  refine ⟨∑ b, lam2 b - ∑ b : Fin q, μ (Fin.castAdd p b), ?_⟩
  have hiff := depthLastIff p q w (∑ b, lam2 b - ∑ b : Fin q, μ (Fin.castAdd p b)) lam2 μ htot
  have h3 : depth2 (fun a : Fin (q + p) => if a.val < q then 1 else 0) (blockWtLast p q w lam2) μ =
      ((∑ b, lam2 b - ∑ b : Fin q, μ (Fin.castAdd p b) : ℕ) : ℤ) := by
    rw [depth_two_block_eq_sum_diff, Nat.cast_sub h1]
  exact ⟨hiff.mpr h3, h3⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Supply the required witnesses or components. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis.

Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem peelBoundLast : PeelBoundLast := by
  intro hD l q w M lam2 ξ hl ha hb hξ i' eL heL μ hμ
  have hl1 : 0 < l - 1 := by have := hl.two_le; omega
  refine exp_le_of_nonzero_weight_vectors l _ _ μ _ hl fun x hx hne => ?_
  obtain ⟨i, hd, _⟩ := depth_exists_last_block 1 q w lam2 ha (fun b => (hb b).1) μ x hx hne
  have h1 := hD l q w M lam2 ξ hl ha hb hξ i' eL heL i μ hd hμ
  refine expLeMono l _ _ μ _ _ ?_ h1
  refine Nat.add_le_add_left ?_ eL
  refine (Nat.le_div_iff_mul_le hl1).mpr ?_
  have h2 := dnVal l 1 (M - w) i q 0 (fun b : Fin q => M - lam2 (Fin.rev b)) hl fun b => by
    have := hb (Fin.rev b)
    exact ⟨Nat.zero_le _, by omega⟩
  rw [one_mul] at h2
  rw [mul_comm]
  refine le_trans h2 ?_
  rcases Nat.eq_zero_or_pos q with hq | hq
  · omega
  · have := hb ⟨0, hq⟩
    omega

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem block_weight_last_one_one (w y : ℕ) : blockWtLast 1 1 w (fun _ : Fin 1 => y) = wt2 y w := by
  funext a
  fin_cases a <;> rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Substitute using the available equality. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem lemmaDLastGraded_rank2 : LemmaDLastGraded_rank2 := by
  intro l w y M ξ hl hwy hyM _ i' e _ i μ hd _
  have hd' : μ 1 = w + i := by simpa [IsDepthLast] using hd
  rw [block_weight_last_one_one]
  show ExpLe l 2 (wt2 y w) μ (e + padicValInt l (Dn 1 (M - w) i fun _ : Fin 1 => M - y))
  rw [expLeIffKilled l 2 _ μ e _ hl (dnNeZero 1 (M - w) i 1 _)]
  intro x hx
  refine ⟨1, (Nat.prime_iff_prime_int.mp hl).not_dvd_one, ?_⟩
  by_cases hex : ∃ j, w + j ≤ y ∧ μ = wt2 (y - j) (w + j)
  · obtain ⟨j, hj, rfl⟩ := hex
    have hd'' : w + j = w + i := hd'
    have hij : j = i := by omega
    subst hij
    rw [(rank2Exact y w j hj).1] at hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [dn2 1 (M - w) (M - y) j le_rfl (by omega), smul_smul]
    have hyw : M - w - (M - y) = y - w := by omega
    rw [hyw]
    have : (1 * ((l : ℤ) ^ e * ((j.factorial * (y - w).choose j : ℕ) : ℤ)) * c) =
        ((l : ℤ) ^ e * (j.factorial : ℤ) * c) * ((y - w).choose j : ℤ) := by
      push_cast
      ring
    rw [this, mul_smul]
    exact Submodule.smul_mem _ _ (ld_gen_mem_weyl y w j)
  · have hbot := rank2Other y w μ hwy (fun j hj hμ => hex ⟨j, hj, hμ⟩)
    rw [hbot] at hx
    rw [(Submodule.mem_bot ℤ).mp hx, smul_zero]
    exact Submodule.zero_mem _

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem restriction_eq_block_weight (n t : ℕ) (lam : ℕ → ℕ) (hc : ∀ a, n ≤ a → a < n + t → lam a = lam n) :
    res (n + t) lam = blockWtLast t n (lam n) (res n lam) := by
  funext a
  unfold blockWtLast
  refine Fin.addCases (fun b => ?_) (fun b => ?_) a
  · rw [Fin.append_left]
    rfl
  · rw [Fin.append_right]
    show lam (Fin.natAdd n b).val = lam n
    rw [Fin.val_natAdd]
    exact hc _ (Nat.le_add_right _ _) (Nat.add_lt_add_left b.isLt n)

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem restriction_antitone (n : ℕ) (lam : ℕ → ℕ) (ha : ∀ a b, a ≤ b → b < n → lam b ≤ lam a) : Antitone (res n lam) :=
  fun a b hab => ha a.val b.val hab b.isLt

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem exponent_bound_peel_one_row (hD : BranchingBoundLastGradedOneRow) (l n : ℕ) (lam : ℕ → ℕ) (ξ : ℕ → ℤ) (hl : l.Prime)
    (ha : ∀ a b, a ≤ b → b < n + 1 → lam b ≤ lam a) (hξ : Antitone ξ) (I : ℤ) (e : ℕ)
    (hE : ExpUpTo l n lam ξ I e) : ExpUpTo l (n + 1) lam ξ I (e + (lam 0 + n - lam n - 1) / (l - 1)) := by
  intro μ hμ
  have hres := restriction_eq_block_weight n 1 lam (fun a h1 h2 => by
    have : a = n := by omega
    rw [this])
  rw [hres] at hμ ⊢
  refine peelBoundLast hD l n (lam n) (lam 0) (res n lam) (res (n + 1) ξ) hl
    (restriction_antitone n lam fun a b hab hb => ha a b hab (by omega))
    (fun b => ⟨ha b.val n (le_of_lt b.isLt) (by omega), ha 0 b.val (Nat.zero_le _) (by have := b.isLt; omega)⟩)
    (fun a b hab => hξ hab) I e (fun μ2 h2 => hE μ2 ?_) μ hμ
  rw [depth2Levi] at h2
  exact h2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem peelRows : PeelRows := by
  intro hD l n s h lam ξ hl ha hh hξ I e hE
  induction s with
  | zero => simpa using hE
  | succ s ih =>
    have ih' := ih (fun a b hab hb => ha a b hab (by omega)) (by
      have := ha (n + s - 1) (n + s) (by omega) (by omega)
      have e1 : n + (s + 1) - 1 = n + s := by omega
      rw [e1] at hh
      omega)
    have h1 := exponent_bound_peel_one_row hD l (n + s) lam ξ hl (fun a b hab hb => ha a b hab (by omega)) hξ I _ ih'
    intro μ hμ
    refine expLeMono l _ _ μ _ _ ?_ (h1 μ hμ)
    have e1 : n + (s + 1) - 1 = n + s := by omega
    rw [e1] at hh
    have h2 : (lam 0 + (n + s) - lam (n + s) - 1) / (l - 1) ≤ (h - 1) / (l - 1) :=
      Nat.div_le_div_right (by omega)
    rw [Nat.succ_mul]
    omega

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem blockStep : BlockStep := by
  intro hD l n t lam hl ht ha hc eL heL I μ hμ
  have hres := restriction_eq_block_weight n t lam hc
  have hanti : Antitone (res n lam) := restriction_antitone n lam fun a b hab hb => ha a b hab (by omega)
  have hb : ∀ b : Fin n, lam n ≤ res n lam b ∧ res n lam b ≤ lam 0 := fun b =>
    ⟨ha b.val n (le_of_lt b.isLt) (by omega), ha 0 b.val (Nat.zero_le _) (by have := b.isLt; omega)⟩
  rw [hres] at hμ ⊢
  refine exp_le_of_nonzero_weight_vectors l _ _ μ _ hl fun x hx hne => ?_
  obtain ⟨i, hd, hi⟩ := depth_exists_last_block t n (lam n) (res n lam) hanti (fun b => (hb b).1) μ x hx hne
  have hμ' : depth2 (fun a : Fin (n + t) => if a.val < n then 1 else 0) (blockWtLast t n (lam n) (res n lam)) μ ≤
      (I : ℤ) := hμ
  rw [hi] at hμ'
  have hiI : i ≤ I := by exact_mod_cast hμ'
  have h1 := hD l t n (lam n) (lam 0) (res n lam) hl hanti hb eL heL i μ hd
  refine expLeMono l _ _ μ _ _ (Nat.add_le_add_left ?_ eL) h1
  unfold blockCost
  exact Finset.le_sup (f := fun i => padicValInt l (Dn t (lam 0 - lam n) i fun b : Fin n => lam 0 - res n lam (Fin.rev b)))
    (Finset.mem_range.mpr (by omega))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem varpi_antitone (c : ℕ) : Antitone (varpi c) := by
  intro a b hab
  unfold varpi
  split_ifs <;> omega

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem applicationSteps : ApplicationSteps := by
  intro hD l k j t q h lam hl ht ha hc hh ecl hecl I
  have hP1 := last_graded_implies_one_block' hD
  have hLast := lastGradedImpliesLast hD
  have s3 := peelRows hP1 l k j h lam (fun _ => 0) hl (fun a b hab hb => ha a b hab (by omega)) (by
      have := ha (k + j - 1) (k + j + t + q - 1) (by omega) (by omega)
      omega) (fun _ _ _ => le_rfl) 0 ecl (fun μ _ => hecl μ)
  have s3' : ∀ μ2 : Fin (k + j) → ℕ, ExpLe l (k + j) (res (k + j) lam) μ2 (ecl + j * ((h - 1) / (l - 1))) :=
    fun μ2 => s3 μ2 (by simp [depth2, res])
  have s2 := blockStep hLast l (k + j) t lam hl ht (fun a b hab hb => ha a b hab (by omega)) hc _ s3' I
  have s1 := peelRows hP1 l (k + j + t) q h lam (varpi (k + j)) hl ha hh (varpi_antitone _) I _ s2
  have e : q * ((h - 1) / (l - 1)) + blockCost l (k + j) t I lam + j * ((h - 1) / (l - 1)) + ecl =
      ecl + j * ((h - 1) / (l - 1)) + blockCost l (k + j) t I lam + q * ((h - 1) / (l - 1)) := by ring
  rw [e]
  exact s1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem last_graded_implies_last : LastGradedImpliesLast := lastGradedImpliesLast
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem last_graded_implies_one_block : OneRowBoundOfLastGraded := last_graded_implies_one_block'
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem depth_two_levi : Depth2Levi := depth2Levi
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem depth_last_iff : DepthLastIff := depthLastIff
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem depth_two_duality : Depth2Dual := depth2Dual
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem d_n_shift : DnShift := dnShift
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem d_n_last_independent : DnLastIndep := dnLastIndep
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lemma_d_last_graded_rank_two : LemmaDLastGraded_rank2 := lemmaDLastGraded_rank2
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem peel_bound_last : PeelBoundLast := peelBoundLast
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem peel_rows : PeelRows := peelRows
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem block_induction' : BlockStep := blockStep
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem application_steps : ApplicationSteps := applicationSteps

end Formalism.CohomologicalDescent.LD
