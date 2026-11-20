import Formalism.HermitianCurvature.StatementWd

namespace Formalism.FourierDecayAlt.P.Wd2

open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd

section Units

variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]

/- English proof (translation)
Use extensionality with `x z`. Rewrite using `[Matrix.mul_apply]`. Distinguish the cases in `hjk : j = k`. Substitute `hjk` using the available equality. Rewrite using `[if_pos rfl, Finset.sum_eq_single (Function.update x a j)]`.

Simplify using `(config := { contextual := true }) only [eU, Matrix.of_apply, Function.update_self, Function.update_apply, true_and, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul]`. Distinguish the cases in `hx : x a = i ∧ z a = l ∧ ∀ b, b ≠ a → x b = z b`. Simplify using `[hx]`. Apply the tactic sequence `rw [if_neg hx] split_ifs <;> simp_all`. Introduce `y _ hy`.

Simplify using `only [eU, Matrix.of_apply]`. Apply the tactic sequence `split_ifs with h1 h2 <;> simp only [mul_one, mul_zero, zero_mul]`. It suffices to derive a contradiction. Apply `hy` to reduce the goal to its premises. Use function extensionality and compare the values at `b`.

Distinguish the cases in `hb : b = a`. Substitute `hb` using the available equality. Rewrite using `[Function.update_self, h1.2.1]`. Rewrite using `[Function.update_of_ne hb, h1.2.2 b hb]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[if_neg hjk, Matrix.zero_apply]`. Use `Finset.sum_eq_zero fun y _ => ?_` and prove the remaining obligations. Simplify using `only [eU, Matrix.of_apply]`. Use `split_ifs with h1 h2`.

Conclude with `absurd (h1.2.1.symm.trans h2.1) hjk`. Apply the tactic sequence `all_goals simp`.
-/
theorem eU_mul (a : S) (i j k l : Fin 2) :
    (eU a i j : SlopeTestRemainingChoices S A) * eU a k l = if j = k then eU a i l else 0 := by
  ext x z
  rw [Matrix.mul_apply]
  by_cases hjk : j = k
  · subst hjk
    rw [if_pos rfl, Finset.sum_eq_single (Function.update x a j)]
    · simp (config := { contextual := true }) only [eU, Matrix.of_apply, Function.update_self,
        Function.update_apply, true_and, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul]
      by_cases hx : x a = i ∧ z a = l ∧ ∀ b, b ≠ a → x b = z b
      · simp [hx]
      · rw [if_neg hx]
        split_ifs <;> simp_all
    · intro y _ hy
      simp only [eU, Matrix.of_apply]
      split_ifs with h1 h2 <;> simp only [mul_one, mul_zero, zero_mul]
      exfalso
      apply hy
      funext b
      by_cases hb : b = a
      · subst hb
        rw [Function.update_self, h1.2.1]
      · rw [Function.update_of_ne hb, h1.2.2 b hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [if_neg hjk, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun y _ => ?_
    simp only [eU, Matrix.of_apply]
    split_ifs with h1 h2
    · exact absurd (h1.2.1.symm.trans h2.1) hjk
    all_goals simp

end Units

section Entries

variable {K B : Type} [CommRing K] [Ring B] [Algebra K B]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Fintype.sum_prod_type]`. Simplify using `[E1, E2]`.
-/
theorem kronecker_E1_E2_apply (M N : Matrix (Fin 2) (Fin 2) B) (i k j l : Fin 2) :
    (E1 M * E2 N) (i, k) (j, l) = M i j * N k l := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [E1, E2]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Fintype.sum_prod_type]`. Simplify using `[E1, E2]`.
-/
theorem kronecker_embed_mul_apply (M N : Matrix (Fin 2) (Fin 2) B) (i k j l : Fin 2) :
    (E2 N * E1 M) (i, k) (j, l) = N k l * M i j := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [E1, E2]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Fintype.sum_prod_type]`. Apply the tactic sequence `fin_cases i <;> fin_cases k <;> simp [Pf]`.
-/
theorem Pf_mul_apply (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) (i k : Fin 2) (p : Fin 2 × Fin 2) :
    (Pf B * X) (i, k) p = X (k, i) p := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  fin_cases i <;> fin_cases k <;> simp [Pf]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Fintype.sum_prod_type]`. Apply the tactic sequence `fin_cases j <;> fin_cases l <;> simp [Pf]`.
-/
theorem mul_Pf_apply (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) (p : Fin 2 × Fin 2) (j l : Fin 2) :
    (X * Pf B) p (j, l) = X p (l, j) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  fin_cases j <;> fin_cases l <;> simp [Pf]

/- English proof (translation)
Establish `h` using `congrFun (congrFun H (i, k)) (j, l)`. Rewrite `h` using `[mul_assoc, sub_mul, mul_sub, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]`. Simplify using `only [Matrix.sub_apply, Matrix.smul_apply, Pf_mul_apply, mul_Pf_apply, kronecker_E1_E2_apply, kronecker_embed_mul_apply] at h`. Conclude with `h`.
-/
theorem rtt_entry (M N : Matrix (Fin 2) (Fin 2) B) (D : K)
    (H : (D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B) * E1 M * E2 N =
      E2 N * E1 M * (D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B))
    (i j k l : Fin 2) :
    D • (M i j * N k l) - M k j * N i l = D • (N k l * M i j) - N k j * M i l := by
  have h := congrFun (congrFun H (i, k)) (j, l)
  rw [mul_assoc, sub_mul, mul_sub, smul_mul_assoc, one_mul, mul_smul_comm, mul_one] at h
  simp only [Matrix.sub_apply, Matrix.smul_apply, Pf_mul_apply, mul_Pf_apply, kronecker_E1_E2_apply,
    kronecker_embed_mul_apply] at h
  exact h

end Entries

section Slots

variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]

/- English proof (translation)
Unfold `ins`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.of_apply, ← mul_assoc, ← mul_assoc, (hx i j).eq]`.
-/
theorem free_mul_ins (a : S) (x : SlopeTestRemainingChoices S A) (hx : FreeOf a x) (N : M2 (SlopeTestRemainingChoices S A)) :
    x * ins a N = ins a (Matrix.of fun k l => x * N k l) := by
  unfold ins
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.of_apply, ← mul_assoc, ← mul_assoc, (hx i j).eq]

/- English proof (translation)
Unfold `ins`. Rewrite using `[Finset.mul_sum, Finset.sum_eq_single i]`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, eU_mul, if_pos rfl]`.

Introduce `k _ hk`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, eU_mul, if_neg (Ne.symm hk), zero_mul]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem eU_mul_ins (a : S) (m i : Fin 2) (N : M2 (SlopeTestRemainingChoices S A)) :
    eU a m i * ins a N = ∑ l, eU a m l * N i l := by
  unfold ins
  rw [Finset.mul_sum, Finset.sum_eq_single i]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← mul_assoc, eU_mul, if_pos rfl]
  · intro k _ hk
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← mul_assoc, eU_mul, if_neg (Ne.symm hk), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Unfold `ins`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul, Finset.sum_eq_single j]`. Rewrite using `[mul_assoc, ← (hN k j j m).eq, ← mul_assoc, eU_mul, if_pos rfl]`.

Introduce `l _ hl`. Rewrite using `[mul_assoc, ← (hN k l j m).eq, ← mul_assoc, eU_mul, if_neg hl, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem ins_mul_eU (a : S) (N : M2 (SlopeTestRemainingChoices S A)) (hN : FreeOf2 a N) (j m : Fin 2) :
    ins a N * eU a j m = ∑ k, eU a k m * N k j := by
  unfold ins
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul, Finset.sum_eq_single j]
  · rw [mul_assoc, ← (hN k j j m).eq, ← mul_assoc, eU_mul, if_pos rfl]
  · intro l _ hl
    rw [mul_assoc, ← (hN k l j m).eq, ← mul_assoc, eU_mul, if_neg hl, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Establish `hins : ∀ (c : S) (X : M2 (SlopeTestRemainingChoices S A)), ins c X = ∑ k, ∑ l, eU c k l * X k l` using `fun _ _ => rfl`. Establish `hdm : ∀ (c : SlopeTestRemainingChoices S A) (X : M2 (SlopeTestRemainingChoices S A)) (i j : Fin 2), (d0 c * X) i j = c * X i j` using `fun c X i j => by simp [d0, Matrix.diagonal_mul]`. Establish `hmd : ∀ (c : SlopeTestRemainingChoices S A) (X : M2 (SlopeTestRemainingChoices S A)) (i j : Fin 2), (X * d0 c) i j = X i j * c` using `fun c X i j => by simp [d0, Matrix.mul_diagonal]`. Establish `hR : ∀ x : SlopeTestRemainingChoices S A, ins a N * x = ins a (Matrix.of fun k l => N k l * x)`. Introduce `x`.

Unfold `ins`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.of_apply, mul_assoc]`. Simplify using `only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]`. Use extensionality with `i j : 1`. Simplify using `only [Matrix.sub_apply, Matrix.smul_apply, hmd, hdm]`. Rewrite using `[Matrix.mul_apply (M := P0 a) (N := M), Matrix.mul_apply (M := d0 (ins a N) * M) (N := P0 a)]`.

Simplify using `only [hdm, P0, Matrix.of_apply, Finset.sum_mul]`. Establish `e1 : ∀ p, eU a p i * M p j * ins a N = ∑ l, eU a p l * (M p j * N i l)`. Introduce `p`. Rewrite using `[mul_assoc, free_mul_ins a (M p j) (hM p j) N, eU_mul_ins]`. Simplify using `only [Matrix.of_apply]`.

Establish `e2 : ∀ p, ins a N * M i p * eU a j p = ∑ k, eU a k p * (N k j * M i p)`. Introduce `p`. Establish `hF : FreeOf2 a (Matrix.of fun k l => N k l * M i p)` using `fun k l c d => by`. Simplify using `only [Matrix.of_apply]`. Conclude with `(hN k l c d).mul_right (hM i p c d)`.

Rewrite using `[hR (M i p), ins_mul_eU a _ hF]`. Simplify using `only [Matrix.of_apply]`. Establish `e3 : ∑ p, ∑ k, eU a k p * (N k j * M i p) = ∑ k, ∑ l, eU a k l * (N k j * M i l)` using `Finset.sum_comm`. Simplify using `only [e1, e2]`. Rewrite using `[e3]`.

Establish `hX : M i j * ins a N = ∑ k, ∑ l, eU a k l * (M i j * N k l)` using `(free_mul_ins a (M i j) (hM i j) N).trans rfl`. Establish `hY : ins a N * M i j = ∑ k, ∑ l, eU a k l * (N k l * M i j)` using `(hR (M i j)).trans rfl`. Establish `key : ∀ f g : Fin 2 → Fin 2 → SlopeTestRemainingChoices S A, D • (∑ k, ∑ l, eU a k l * f k l) - ∑ k, ∑ l, eU a k l * g k l = ∑ k, ∑ l, eU a k l * (D • f k l - g k l)`. Introduce `f g`. Simplify using `only [Finset.smul_sum, ← mul_smul_comm, ← Finset.sum_sub_distrib, mul_sub]`.

Rewrite using `[hX, hY]`. Use `(key (fun k l => M i j * N k l) (fun k l => M k j * N i l)).trans (Eq.trans ?_ (key (fun k l => N k l * M i j) (fun k l => N k j * M i l)).symm)` and prove the remaining obligations. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Conclude with `congrArg (eU a k l * ·) (H i j k l)`.
-/
theorem position_plus_core (a : S) (M N : M2 (SlopeTestRemainingChoices S A)) (D : K) (hM : FreeOf2 a M) (hN : FreeOf2 a N)
    (H : ∀ i j k l, D • (M i j * N k l) - M k j * N i l = D • (N k l * M i j) - N k j * M i l) :
    (D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) * M * d0 (ins a N) =
      d0 (ins a N) * M * (D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) := by
  have hins : ∀ (c : S) (X : M2 (SlopeTestRemainingChoices S A)), ins c X = ∑ k, ∑ l, eU c k l * X k l :=
    fun _ _ => rfl
  have hdm : ∀ (c : SlopeTestRemainingChoices S A) (X : M2 (SlopeTestRemainingChoices S A)) (i j : Fin 2), (d0 c * X) i j = c * X i j :=
    fun c X i j => by simp [d0, Matrix.diagonal_mul]
  have hmd : ∀ (c : SlopeTestRemainingChoices S A) (X : M2 (SlopeTestRemainingChoices S A)) (i j : Fin 2), (X * d0 c) i j = X i j * c :=
    fun c X i j => by simp [d0, Matrix.mul_diagonal]
  have hR : ∀ x : SlopeTestRemainingChoices S A, ins a N * x = ins a (Matrix.of fun k l => N k l * x) := by
    intro x
    unfold ins
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.of_apply, mul_assoc]
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  ext i j : 1
  simp only [Matrix.sub_apply, Matrix.smul_apply, hmd, hdm]
  rw [Matrix.mul_apply (M := P0 a) (N := M), Matrix.mul_apply (M := d0 (ins a N) * M) (N := P0 a)]
  simp only [hdm, P0, Matrix.of_apply, Finset.sum_mul]
  have e1 : ∀ p, eU a p i * M p j * ins a N = ∑ l, eU a p l * (M p j * N i l) := by
    intro p
    rw [mul_assoc, free_mul_ins a (M p j) (hM p j) N, eU_mul_ins]
    simp only [Matrix.of_apply]
  have e2 : ∀ p, ins a N * M i p * eU a j p = ∑ k, eU a k p * (N k j * M i p) := by
    intro p
    have hF : FreeOf2 a (Matrix.of fun k l => N k l * M i p) := fun k l c d => by
      simp only [Matrix.of_apply]
      exact (hN k l c d).mul_right (hM i p c d)
    rw [hR (M i p), ins_mul_eU a _ hF]
    simp only [Matrix.of_apply]
  have e3 : ∑ p, ∑ k, eU a k p * (N k j * M i p) = ∑ k, ∑ l, eU a k l * (N k j * M i l) :=
    Finset.sum_comm
  simp only [e1, e2]
  rw [e3]
  have hX : M i j * ins a N = ∑ k, ∑ l, eU a k l * (M i j * N k l) :=
    (free_mul_ins a (M i j) (hM i j) N).trans rfl
  have hY : ins a N * M i j = ∑ k, ∑ l, eU a k l * (N k l * M i j) := (hR (M i j)).trans rfl
  have key : ∀ f g : Fin 2 → Fin 2 → SlopeTestRemainingChoices S A, D • (∑ k, ∑ l, eU a k l * f k l) -
      ∑ k, ∑ l, eU a k l * g k l = ∑ k, ∑ l, eU a k l * (D • f k l - g k l) := by
    intro f g
    simp only [Finset.smul_sum, ← mul_smul_comm, ← Finset.sum_sub_distrib, mul_sub]
  rw [hX, hY]
  refine (key (fun k l => M i j * N k l) (fun k l => M k j * N i l)).trans
    (Eq.trans ?_ (key (fun k l => N k l * M i j) (fun k l => N k j * M i l)).symm)
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  exact congrArg (eU a k l * ·) (H i j k l)

/- English proof (translation)
Establish `hins : ∀ (c : S) (X : M2 (SlopeTestRemainingChoices S A)), ins c X = ∑ k, ∑ l, eU c k l * X k l` using `fun _ _ => rfl`. Establish `hdm : ∀ (c : SlopeTestRemainingChoices S A) (X : M2 (SlopeTestRemainingChoices S A)) (i j : Fin 2), (d0 c * X) i j = c * X i j` using `fun c X i j => by simp [d0, Matrix.diagonal_mul]`. Establish `hmd : ∀ (c : SlopeTestRemainingChoices S A) (X : M2 (SlopeTestRemainingChoices S A)) (i j : Fin 2), (X * d0 c) i j = X i j * c` using `fun c X i j => by simp [d0, Matrix.mul_diagonal]`. Establish `hNT : FreeOf2 b Nᵀ` using `fun k l => hN l k`. Establish `hR : ∀ x : SlopeTestRemainingChoices S A, ins b Nᵀ * x = ins b (Matrix.of fun k l => Nᵀ k l * x)`.

Introduce `x`. Unfold `ins`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.of_apply, mul_assoc]`. Simplify using `only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]`. Use extensionality with `i j : 1`. Simplify using `only [Matrix.sub_apply, Matrix.smul_apply, hmd, hdm]`.

Rewrite using `[Matrix.mul_apply (M := d0 (ins b Nᵀ) * Q0 b) (N := M), Matrix.mul_apply (M := M) (N := Q0 b)]`. Simplify using `only [hdm, Q0, Matrix.of_apply, Finset.sum_mul]`. Establish `e1 : ∀ p, ins b Nᵀ * eU b i p * M p j = ∑ k, eU b k p * (N i k * M p j)`. Introduce `p`. Rewrite using `[ins_mul_eU b _ hNT, Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, Matrix.transpose_apply]`. Establish `e2 : ∀ p, M i p * eU b p j * ins b Nᵀ = ∑ l, eU b p l * (M i p * N l j)`. Introduce `p`. Rewrite using `[← (hM i p p j).eq, mul_assoc, free_mul_ins b (M i p) (hM i p) Nᵀ, eU_mul_ins]`.

Simplify using `only [Matrix.of_apply, Matrix.transpose_apply]`. Establish `e3 : ∑ p, ∑ k, eU b k p * (N i k * M p j) = ∑ k, ∑ l, eU b k l * (N i k * M l j)` using `Finset.sum_comm`. Simplify using `only [e1, e2]`. Rewrite using `[e3]`. Establish `hX : ins b Nᵀ * M i j = ∑ k, ∑ l, eU b k l * (N l k * M i j)` using `(hR (M i j)).trans rfl`.

Establish `hY : M i j * ins b Nᵀ = ∑ k, ∑ l, eU b k l * (M i j * N l k)` using `(free_mul_ins b (M i j) (hM i j) Nᵀ).trans rfl`. Establish `key : ∀ f g : Fin 2 → Fin 2 → SlopeTestRemainingChoices S A, d • (∑ k, ∑ l, eU b k l * f k l) - ∑ k, ∑ l, eU b k l * g k l = ∑ k, ∑ l, eU b k l * (d • f k l - g k l)`. Introduce `f g`. Simplify using `only [Finset.smul_sum, ← mul_smul_comm, ← Finset.sum_sub_distrib, mul_sub]`. Rewrite using `[hX, hY]`.

Use `(key (fun k l => N l k * M i j) (fun k l => N i k * M l j)).trans (Eq.trans ?_ (key (fun k l => M i j * N l k) (fun k l => M i k * N l j)).symm)` and prove the remaining obligations. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Conclude with `congrArg (eU b k l * ·) (H l k i j)`.
-/
theorem position_minus_core (b : S) (M N : M2 (SlopeTestRemainingChoices S A)) (d : K) (hM : FreeOf2 b M) (hN : FreeOf2 b N)
    (H : ∀ i j k l, d • (N i j * M k l) - N k j * M i l = d • (M k l * N i j) - M k j * N i l) :
    d0 (ins b Nᵀ) * (d • (1 : M2 (SlopeTestRemainingChoices S A)) - Q0 b) * M =
      M * (d • (1 : M2 (SlopeTestRemainingChoices S A)) - Q0 b) * d0 (ins b Nᵀ) := by
  have hins : ∀ (c : S) (X : M2 (SlopeTestRemainingChoices S A)), ins c X = ∑ k, ∑ l, eU c k l * X k l :=
    fun _ _ => rfl
  have hdm : ∀ (c : SlopeTestRemainingChoices S A) (X : M2 (SlopeTestRemainingChoices S A)) (i j : Fin 2), (d0 c * X) i j = c * X i j :=
    fun c X i j => by simp [d0, Matrix.diagonal_mul]
  have hmd : ∀ (c : SlopeTestRemainingChoices S A) (X : M2 (SlopeTestRemainingChoices S A)) (i j : Fin 2), (X * d0 c) i j = X i j * c :=
    fun c X i j => by simp [d0, Matrix.mul_diagonal]
  have hNT : FreeOf2 b Nᵀ := fun k l => hN l k
  have hR : ∀ x : SlopeTestRemainingChoices S A, ins b Nᵀ * x = ins b (Matrix.of fun k l => Nᵀ k l * x) := by
    intro x
    unfold ins
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.of_apply, mul_assoc]
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  ext i j : 1
  simp only [Matrix.sub_apply, Matrix.smul_apply, hmd, hdm]
  rw [Matrix.mul_apply (M := d0 (ins b Nᵀ) * Q0 b) (N := M), Matrix.mul_apply (M := M) (N := Q0 b)]
  simp only [hdm, Q0, Matrix.of_apply, Finset.sum_mul]
  have e1 : ∀ p, ins b Nᵀ * eU b i p * M p j = ∑ k, eU b k p * (N i k * M p j) := by
    intro p
    rw [ins_mul_eU b _ hNT, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, Matrix.transpose_apply]
  have e2 : ∀ p, M i p * eU b p j * ins b Nᵀ = ∑ l, eU b p l * (M i p * N l j) := by
    intro p
    rw [← (hM i p p j).eq, mul_assoc, free_mul_ins b (M i p) (hM i p) Nᵀ, eU_mul_ins]
    simp only [Matrix.of_apply, Matrix.transpose_apply]
  have e3 : ∑ p, ∑ k, eU b k p * (N i k * M p j) = ∑ k, ∑ l, eU b k l * (N i k * M l j) :=
    Finset.sum_comm
  simp only [e1, e2]
  rw [e3]
  have hX : ins b Nᵀ * M i j = ∑ k, ∑ l, eU b k l * (N l k * M i j) := (hR (M i j)).trans rfl
  have hY : M i j * ins b Nᵀ = ∑ k, ∑ l, eU b k l * (M i j * N l k) :=
    (free_mul_ins b (M i j) (hM i j) Nᵀ).trans rfl
  have key : ∀ f g : Fin 2 → Fin 2 → SlopeTestRemainingChoices S A, d • (∑ k, ∑ l, eU b k l * f k l) -
      ∑ k, ∑ l, eU b k l * g k l = ∑ k, ∑ l, eU b k l * (d • f k l - g k l) := by
    intro f g
    simp only [Finset.smul_sum, ← mul_smul_comm, ← Finset.sum_sub_distrib, mul_sub]
  rw [hX, hY]
  refine (key (fun k l => N l k * M i j) (fun k l => N i k * M l j)).trans
    (Eq.trans ?_ (key (fun k l => M i j * N l k) (fun k l => M i k * N l j)).symm)
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  exact congrArg (eU b k l * ·) (H l k i j)

end Slots

section Start

variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]

/- English proof (translation)
Use extensionality with `x y`. Simplify using `only [io, Matrix.scalar_apply, Matrix.smul_apply, Matrix.diagonal_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem io_smul (c : K) (x : A) : (io (c • x) : SlopeTestRemainingChoices S A) = c • io x := by
  ext x y
  simp only [io, Matrix.scalar_apply, Matrix.smul_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

/- English proof (translation)
Use extensionality with `x y`. Simplify using `only [io, Matrix.scalar_apply, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply, Pi.algebraMap_apply]`.
-/
theorem io_algebraMap (c : K) : (io (algebraMap K A c) : SlopeTestRemainingChoices S A) = algebraMap K (SlopeTestRemainingChoices S A) c := by
  ext x y
  simp only [io, Matrix.scalar_apply, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply,
    Pi.algebraMap_apply]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem liftMatrix_eq_map_scalar (M : M2 A) : (lift0 M : M2 (SlopeTestRemainingChoices S A)) = M.map (Matrix.scalar (Ix S)) := rfl

/- English proof (translation)
Use extensionality with `p q`. Simplify using `only [E1, lift0, io, Matrix.of_apply, Matrix.map_apply, Matrix.map_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem firstEmbed_liftMatrix (M : M2 A) :
    E1 (lift0 M : M2 (SlopeTestRemainingChoices S A)) = (E1 M).map (Matrix.scalar (Ix S)) := by
  ext p q
  simp only [E1, lift0, io, Matrix.of_apply, Matrix.map_apply, Matrix.map_apply]
  split_ifs <;> simp

/- English proof (translation)
Use extensionality with `p q`. Simplify using `only [E2, lift0, io, Matrix.of_apply, Matrix.map_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem secondEmbed_liftMatrix (M : M2 A) :
    E2 (lift0 M : M2 (SlopeTestRemainingChoices S A)) = (E2 M).map (Matrix.scalar (Ix S)) := by
  ext p q
  simp only [E2, lift0, io, Matrix.of_apply, Matrix.map_apply]
  split_ifs <;> simp

/- English proof (translation)
Establish `hsc : ∀ x : A, Matrix.scalar (Ix S) (c • x) = c • Matrix.scalar (Ix S) x` using `io_smul c`. Use extensionality with `p q : 1`. Simplify using `only [Pf, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply]`. Apply the tactic sequence `split_ifs <;> simp [map_sub, map_neg, hsc]`.
-/
theorem core_map (c : K) :
    c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (SlopeTestRemainingChoices S A)) - Pf (SlopeTestRemainingChoices S A) =
      (c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A).map (Matrix.scalar (Ix S)) := by
  have hsc : ∀ x : A, Matrix.scalar (Ix S) (c • x) = c • Matrix.scalar (Ix S) x := io_smul c
  ext p q : 1
  simp only [Pf, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.of_apply]
  split_ifs <;> simp [map_sub, map_neg, hsc]

/- English proof (translation)
Use extensionality with `i j : 1`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [YangianSpanCharacter.T.J] <;> (try (ext x y; simp only [Matrix.neg_apply, Matrix.one_apply, Matrix.diagonal_apply, Matrix.smul_apply]; split_ifs <;> simp))`.
-/
theorem J_map : YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) = (YangianSpanCharacter.T.J A).map (Matrix.scalar (Ix S)) := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [YangianSpanCharacter.T.J] <;>
    (try (ext x y; simp only [Matrix.neg_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.smul_apply]; split_ifs <;> simp))

/- English proof (translation)
Establish `hsc : ∀ x : A, Matrix.scalar (Ix S) (c • x) = c • Matrix.scalar (Ix S) x` using `io_smul c`. Use extensionality with `i j : 1`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [YangianSpanCharacter.T.J, Algebra.algebraMap_eq_smul_one, hsc] <;> (try (ext x y; simp only [Matrix.neg_apply, Matrix.one_apply, Matrix.diagonal_apply, Matrix.smul_apply]; split_ifs <;> simp))`.
-/
theorem smulJ_map (c : K) :
    algebraMap K (SlopeTestRemainingChoices S A) c • YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) =
      (algebraMap K A c • YangianSpanCharacter.T.J A).map (Matrix.scalar (Ix S)) := by
  have hsc : ∀ x : A, Matrix.scalar (Ix S) (c • x) = c • Matrix.scalar (Ix S) x := io_smul c
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [YangianSpanCharacter.T.J, Algebra.algebraMap_eq_smul_one, hsc] <;>
    (try (ext x y; simp only [Matrix.neg_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.smul_apply]; split_ifs <;> simp))

/- English proof (translation)
Rewrite using `[core_map, firstEmbed_liftMatrix, secondEmbed_liftMatrix, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, H]`.
-/
theorem rtt_lift0 (M N : M2 A) (c : K)
    (H : (c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A) * E1 M * E2 N =
      E2 N * E1 M * (c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A)) :
    (c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (SlopeTestRemainingChoices S A)) - Pf (SlopeTestRemainingChoices S A)) *
        E1 (lift0 M) * E2 (lift0 N) =
      E2 (lift0 N) * E1 (lift0 M) *
        (c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (SlopeTestRemainingChoices S A)) - Pf (SlopeTestRemainingChoices S A)) := by
  rw [core_map, firstEmbed_liftMatrix, secondEmbed_liftMatrix, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul,
    ← Matrix.map_mul, H]

/- English proof (translation)
Rewrite using `[smulJ_map, liftMatrix_eq_map_scalar, liftMatrix_eq_map_scalar, J_map, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, H]`.
-/
theorem det_lift0 (M M' : M2 A) (c : K) (H : M'ᵀ * YangianSpanCharacter.T.J A * M = algebraMap K A c • YangianSpanCharacter.T.J A) :
    (lift0 M' : M2 (SlopeTestRemainingChoices S A))ᵀ * YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) * lift0 M = algebraMap K (SlopeTestRemainingChoices S A) c • YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) := by
  rw [smulJ_map, liftMatrix_eq_map_scalar, liftMatrix_eq_map_scalar, J_map, ← Matrix.transpose_map, ← Matrix.map_mul,
    ← Matrix.map_mul, H]

/- English proof (translation)
Rewrite using `[smulJ_map, liftMatrix_eq_map_scalar, liftMatrix_eq_map_scalar, J_map, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, H]`.
-/
theorem det_lift0' (M M' : M2 A) (c : K) (H : M * YangianSpanCharacter.T.J A * M'ᵀ = algebraMap K A c • YangianSpanCharacter.T.J A) :
    (lift0 M : M2 (SlopeTestRemainingChoices S A)) * YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) * (lift0 M')ᵀ = algebraMap K (SlopeTestRemainingChoices S A) c • YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) := by
  rw [smulJ_map, liftMatrix_eq_map_scalar, liftMatrix_eq_map_scalar, J_map, ← Matrix.transpose_map, ← Matrix.map_mul,
    ← Matrix.map_mul, H]

/- English proof (translation)
Use extensionality with `i j x y`. Simplify using `[lift0, io, Matrix.conjTranspose_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.star_apply]`. Apply the tactic sequence `split_ifs <;> simp_all [@eq_comm _ y x]`.
-/
theorem liftMatrix_conjTranspose [StarRing A] (M : M2 A) :
    (lift0 M : M2 (SlopeTestRemainingChoices S A))ᴴ = lift0 Mᴴ := by
  ext i j x y
  simp [lift0, io, Matrix.conjTranspose_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
    Matrix.star_apply]
  split_ifs <;> simp_all [@eq_comm _ y x]

/- English proof (translation)
Unfold `d0`. Conclude with `Matrix.diagonal_one`.
-/
theorem d0_one : (d0 (1 : SlopeTestRemainingChoices S A)) = 1 := by
  unfold d0
  exact Matrix.diagonal_one

end Start

end Formalism.FourierDecayAlt.P.Wd2

namespace Formalism.FourierDecayAlt.P

open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd

/- English proof (translation)
Introduce `K A S _ _ _ _ _ _ _ _ a M N D hM hN H`. Unfold `Rh0`. Apply the tactic sequence `rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, Formalism.FourierDecayAlt.P.Wd2.position_plus_core a M N D hM hN (Formalism.FourierDecayAlt.P.Wd2.rtt_entry M N D H)]`.
-/
theorem position_RTT_relation_plus : Formalism.FourierDecayAlt.Wd.PositionRTTPlus := by
  intro K A S _ _ _ _ _ _ _ _ a M N D hM hN H
  unfold Rh0
  rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm,
    Formalism.FourierDecayAlt.P.Wd2.position_plus_core a M N D hM hN (Formalism.FourierDecayAlt.P.Wd2.rtt_entry M N D H)]

/- English proof (translation)
Introduce `K A S _ _ _ _ _ _ _ _ b M N d hM hN H`. Unfold `Rht0`. Apply the tactic sequence `rw [mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, Formalism.FourierDecayAlt.P.Wd2.position_minus_core b M N d hM hN (Formalism.FourierDecayAlt.P.Wd2.rtt_entry N M d H)]`.
-/
theorem position_RTT_relation_minus : Formalism.FourierDecayAlt.Wd.PositionRTTMinus := by
  intro K A S _ _ _ _ _ _ _ _ b M N d hM hN H
  unfold Rht0
  rw [mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc,
    Formalism.FourierDecayAlt.P.Wd2.position_minus_core b M N d hM hN (Formalism.FourierDecayAlt.P.Wd2.rtt_entry N M d H)]

/- English proof (translation)
Introduce `K A S _ _ _ _ _ _ _ _ QQ q hS`. Use `⟨star_one _, fun Y _ hY => ?_, fun Y _ Y' _ => ?_, fun Y _ _ => ?_, hS.q_real⟩` and prove the remaining obligations. Rewrite using `[Formalism.FourierDecayAlt.P.Wd2.d0_one, one_mul, Formalism.FourierDecayAlt.P.Wd2.liftMatrix_conjTranspose, hS.herm Y hY]`. Conclude with `Formalism.FourierDecayAlt.P.Wd2.rtt_lift0 (QQ Y') (QQ Y) (Y' - Y) (hS.rtt Y Y')`. Conclude with `⟨Formalism.FourierDecayAlt.P.Wd2.det_lift0 (QQ Y) (QQ (Y + 1)) (q Y) (hS.det Y).1, Formalism.FourierDecayAlt.P.Wd2.det_lift0' (QQ Y) (QQ (Y + 1)) (q Y) (hS.det Y).2⟩`.
-/
theorem initial_module_structure : Formalism.FourierDecayAlt.Wd.StartModule := by
  intro K A S _ _ _ _ _ _ _ _ QQ q hS
  refine ⟨star_one _, fun Y _ hY => ?_, fun Y _ Y' _ => ?_, fun Y _ _ => ?_, hS.q_real⟩
  · rw [Formalism.FourierDecayAlt.P.Wd2.d0_one, one_mul, Formalism.FourierDecayAlt.P.Wd2.liftMatrix_conjTranspose, hS.herm Y hY]
  · exact Formalism.FourierDecayAlt.P.Wd2.rtt_lift0 (QQ Y') (QQ Y) (Y' - Y) (hS.rtt Y Y')
  · exact ⟨Formalism.FourierDecayAlt.P.Wd2.det_lift0 (QQ Y) (QQ (Y + 1)) (q Y) (hS.det Y).1,
      Formalism.FourierDecayAlt.P.Wd2.det_lift0' (QQ Y) (QQ (Y + 1)) (q Y) (hS.det Y).2⟩

end Formalism.FourierDecayAlt.P
