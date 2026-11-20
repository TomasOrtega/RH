import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.NonOpenCell

variable {g : ℕ} [Fact g.Prime] {n : ℕ}

/- English proof (translation)
Establish `h : IsUnit (show Mt g n from fun r j : Fin n => if r = σ j then 1 else 0)`. Use `IsUnit.of_mul_eq_one (show Mt g n from fun r j : Fin n => if j = σ r then 1 else 0) ?_` and prove the remaining obligations. Use extensionality with `r c`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (σ.symm r)]`. Simplify using `[Matrix.one_apply, eq_comm]`.

Introduce `k _ hk`. Establish `: r ≠ σ k` using `fun h => hk (by simp [h])`. Simplify using `[this]`. Simplify using the standard rewrite rules. Unfold `pm toG`.

Rewrite using `[dif_pos h]`. Both sides reduce to the same expression.
-/
theorem pm_val (σ : Equiv.Perm (Fin n)) :
    ((pm g σ : Gn g n) : Mt g n) = fun r j : Fin n => if r = σ j then 1 else 0 := by
  have h : IsUnit (show Mt g n from fun r j : Fin n => if r = σ j then 1 else 0) := by
    refine IsUnit.of_mul_eq_one (show Mt g n from fun r j : Fin n => if j = σ r then 1 else 0) ?_
    ext r c
    rw [Matrix.mul_apply, Finset.sum_eq_single (σ.symm r)]
    · simp [Matrix.one_apply, eq_comm]
    · intro k _ hk
      have : r ≠ σ k := fun h => hk (by simp [h])
      simp [this]
    · simp
  unfold pm toG
  rw [dif_pos h]
  rfl

/- English proof (translation)
Establish `h : ((pm g σ : Gn g n) : Mt g n) * (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n) = (x : Mt g n) * ((pm g σ : Gn g n) : Mt g n)`. Rewrite using `[← Units.val_mul, ← Units.val_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]`. Generalize the expression as in `(((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n) = Y at h ⊢`. Establish `h2` using `congrFun (congrFun h (σ r)) c`. Rewrite `h2` using `[Matrix.mul_apply, Matrix.mul_apply]`.

Establish `h3 : ∀ r j, ((pm g σ : Gn g n) : Mt g n) r j = if r = σ j then 1 else 0` using `fun r j => by`. Rewrite using `[pm_val]`. Simplify `h2` using `[h3]`.
-/
theorem conj_apply (σ : Equiv.Perm (Fin n)) (x : Gn g n) (r c : Fin n) :
    (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n) r c = (x : Mt g n) (σ r) (σ c) := by
  have h : ((pm g σ : Gn g n) : Mt g n) * (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n)
      = (x : Mt g n) * ((pm g σ : Gn g n) : Mt g n) := by
    rw [← Units.val_mul, ← Units.val_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  generalize (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n) = Y at h ⊢
  have h2 := congrFun (congrFun h (σ r)) c
  rw [Matrix.mul_apply, Matrix.mul_apply] at h2
  have h3 : ∀ r j, ((pm g σ : Gn g n) : Mt g n) r j = if r = σ j then 1 else 0 := fun r j => by
    rw [pm_val]
  simpa [h3] using h2

noncomputable def elem (p q : Fin n) (h : p ≠ q) (t : ZMod g) : Gn g n :=
  ⟨Matrix.transvection p q t, Matrix.transvection p q (-t),
    by rw [Matrix.transvection_mul_transvection_same _ _ h]; simp,
    by rw [Matrix.transvection_mul_transvection_same _ _ h]; simp⟩

/- English proof (translation)
Express the relevant statement in the definitionally equal form `((x : Mt g n) * Matrix.transvection p q t) r c = _`. Distinguish the cases in `hc : c = q`. Substitute `hc` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hc]`.
-/
theorem mul_elem_apply (p q : Fin n) (h : p ≠ q) (t : ZMod g) (x : Gn g n) (r c : Fin n) :
    ((x * elem p q h t : Gn g n) : Mt g n) r c
      = (x : Mt g n) r c + if c = q then t * (x : Mt g n) r p else 0 := by
  change ((x : Mt g n) * Matrix.transvection p q t) r c = _
  by_cases hc : c = q
  · subst hc; simp
  · simp [hc]

/- English proof (translation)
Introduce `r c`. Use `⟨fun hc => ?_, fun hc => ?_⟩` and prove the remaining obligations. Rewrite using `[h, (hM r c).1 hc] split_ifs with h1`. Rewrite using `[(hM r p).1 (by subst h1; exact hpq.trans hc)]; simp`. Simplify using the standard rewrite rules.

Rewrite using `[h, (hM r c).2 hc] split_ifs with h1`. Rewrite using `[(hM r p).1 (by subst h1; subst hc; exact hpq)]; simp`. Simplify using the standard rewrite rules.
-/
theorem isUniUp_of_col {M M' : Mt g n} {p q : Fin n} (hpq : p < q) (t : ZMod g)
    (h : ∀ r c, M' r c = M r c + if c = q then t * M r p else 0) (hM : IsUniUp M) : IsUniUp M' := by
  intro r c
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · rw [h, (hM r c).1 hc]
    split_ifs with h1
    · rw [(hM r p).1 (by subst h1; exact hpq.trans hc)]; simp
    · simp
  · rw [h, (hM r c).2 hc]
    split_ifs with h1
    · rw [(hM r p).1 (by subst h1; subst hc; exact hpq)]; simp
    · simp

/- English proof (translation)
Use `⟨isUniUp_of_col hpq (-t) fun r c => ?_, isUniUp_of_col hpq t h⟩` and prove the remaining obligations. Rewrite using `[h r c, h r p, if_neg hpq.ne]`. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem isUniUp_iff_of_col {M M' : Mt g n} {p q : Fin n} (hpq : p < q) (t : ZMod g)
    (h : ∀ r c, M' r c = M r c + if c = q then t * M r p else 0) : IsUniUp M' ↔ IsUniUp M := by
  refine ⟨isUniUp_of_col hpq (-t) fun r c => ?_, isUniUp_of_col hpq t h⟩
  rw [h r c, h r p, if_neg hpq.ne]
  split_ifs <;> ring

/- English proof (translation)
Establish `hq` using `q.2`. Establish `: ∀ k ∈ Finset.Ico 0 (n - 1), entN M' k (k + 1) = entN M k (k + 1) + if k = (p : ℕ) then t else 0`. Introduce `k hk`. Establish `hk' : k < n ∧ k + 1 < n` using `by have := (Finset.mem_Ico.1 hk).2; omega`. Unfold `entN`.

Rewrite using `[dif_pos hk', dif_pos hk', h]`. Use `congr 1`. Distinguish the cases in `hkp : k = (p : ℕ)`. Rewrite using `[if_pos hkp, if_pos (Fin.ext (by simp [hkp, hpq])), (hM _ p).2 (Fin.ext hkp), mul_one]`. Rewrite using `[if_neg hkp, if_neg]`.

Introduce `h1`. Use `congrArg Fin.val h1` as an intermediate fact. Simplify using `only at this`. Use linear arithmetic over natural numbers and integers. Unfold `supFrom`.

Rewrite using `[Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos]`. Rewrite using `[Finset.mem_Ico]`. Use linear arithmetic over natural numbers and integers.
-/
theorem supFrom_of_col {M M' : Mt g n} {p q : Fin n} (hpq : (q : ℕ) = p + 1) (t : ZMod g)
    (h : ∀ r c, M' r c = M r c + if c = q then t * M r p else 0) (hM : IsUniUp M) :
    supFrom 0 M' = supFrom 0 M + t := by
  have hq := q.2
  have : ∀ k ∈ Finset.Ico 0 (n - 1),
      entN M' k (k + 1) = entN M k (k + 1) + if k = (p : ℕ) then t else 0 := by
    intro k hk
    have hk' : k < n ∧ k + 1 < n := by have := (Finset.mem_Ico.1 hk).2; omega
    unfold entN
    rw [dif_pos hk', dif_pos hk', h]
    congr 1
    by_cases hkp : k = (p : ℕ)
    · rw [if_pos hkp, if_pos (Fin.ext (by simp [hkp, hpq])), (hM _ p).2 (Fin.ext hkp), mul_one]
    · rw [if_neg hkp, if_neg]
      intro h1
      have := congrArg Fin.val h1
      simp only at this
      omega
  unfold supFrom
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos]
  rw [Finset.mem_Ico]; omega

/- English proof (translation)
Use `forall_congr' fun r => forall_congr' fun c => forall_congr' fun hc => ?_` and prove the remaining obligations. Rewrite using `[h, if_neg (by rintro rfl; omega), add_zero]`.
-/
theorem inPar_iff_of_col {M M' : Mt g n} {a : ℕ} {i j : Fin n} (hj : a ≤ (j : ℕ)) (t : ZMod g)
    (h : ∀ r c, M' r c = M r c + if c = j then t * M r i else 0) : InPar a M' ↔ InPar a M := by
  refine forall_congr' fun r => forall_congr' fun c => forall_congr' fun hc => ?_
  rw [h, if_neg (by rintro rfl; omega), add_zero]

/- English proof (translation)
Use extensionality with `r c`. Unfold `tl entN`. Use `split_ifs with h1`. Rewrite using `[h, if_neg, add_zero]`. Introduce and unpack `rfl`.

Use `c.2` as an intermediate fact. Simplify using `only at hj`. Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression.
-/
theorem tl_of_col {M M' : Mt g n} {a : ℕ} {i j : Fin n} (hj : a ≤ (j : ℕ)) (t : ZMod g)
    (h : ∀ r c, M' r c = M r c + if c = j then t * M r i else 0) : tl a M' = tl a M := by
  ext r c
  unfold tl entN
  split_ifs with h1
  · rw [h, if_neg, add_zero]
    rintro rfl
    have := c.2
    simp only at hj
    omega
  · rfl

/- English proof (translation)
Use extensionality with `r c`. Unfold `br entN`. Use `split_ifs with h1`. Rewrite using `[h, hM _ i hi (by simp)]; simp`. Both sides reduce to the same expression.
-/
theorem br_of_col {M M' : Mt g n} {a b : ℕ} {i j : Fin n} (hi : (i : ℕ) < a) (t : ZMod g)
    (h : ∀ r c, M' r c = M r c + if c = j then t * M r i else 0) (hM : InPar a M) :
    br a b M' = br a b M := by
  ext r c
  unfold br entN
  split_ifs with h1
  · rw [h, hM _ i hi (by simp)]; simp
  · rfl

/- English proof (translation)
Introduce `g _ ψ hψ a b n σ Φ i j _ hi hj hσ`. Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hψ (by ext t; simpa using hc t)`.

Establish `hlt : σ i < σ j` using `by rw [Fin.lt_def]; omega`. Use `set F : Gn g n → ℂ := fun x => if IsUniUp (x : Mt g n) ∧ InPar a (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n) then (ψ (supFrom 0 (x : Mt g n)))⁻¹ * Φ (toG (tl a (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n))) (toG (br a b (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n))) else 0 wi …`. Establish `key : ∀ x, F (x * elem (σ i) (σ j) hlt.ne t) = (ψ t)⁻¹ * F x`. Introduce `x`. Establish `h1` using `mul_elem_apply (σ i) (σ j) hlt.ne t x`.

Establish `h2 : ∀ r c, (((pm g σ)⁻¹ * (x * elem (σ i) (σ j) hlt.ne t) * pm g σ : Gn g n) : Mt g n) r c = (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n) r c + if c = j then t * (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n) r i else 0`. Introduce `r c`. Rewrite using `[conj_apply, conj_apply, conj_apply, h1]`. Simplify using `only [σ.apply_eq_iff_eq]`. Simplify using `only [hF]`.

Rewrite using `[isUniUp_iff_of_col hlt t h1, inPar_iff_of_col hj t h2]`. Use `split_ifs with hx`. Rewrite using `[supFrom_of_col hσ t h1 hx.1, tl_of_col hj t h2, br_of_col hi t h2 hx.2, AddChar.map_add_eq_mul, mul_inv]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.

Establish `hS : ∑ x, F x = (ψ t)⁻¹ * ∑ x, F x`. Rewrite using `[Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulRight (elem (σ i) (σ j) hlt.ne t)) F]`. Conclude with `Finset.sum_congr rfl fun x _ => key x`. Express the relevant statement in the definitionally equal form `∑ x, F x = 0`. Assume the negation of the conclusion as `hne`.

Apply `ht` to reduce the goal to its premises. Establish `: (ψ t)⁻¹ = 1` using `mul_right_cancel₀ hne (by rw [one_mul]; exact hS.symm)`. Conclude with `inv_eq_one.1 this`.
-/
theorem whittaker_term_eq_zero : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) , ψ ≠ 1 → ∀ (a b n : ℕ) (σ : Equiv.Perm (Fin n)) (Φ : Gn g a → Gn g b → ℂ) (i j : Fin n), n = a + b → (i : ℕ) < a → a ≤ (j : ℕ) → (σ j : ℕ) = σ i + 1 → (∑ x : Gn g n, if IsUniUp (x : Mt g n) ∧ InPar a (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n) then (ψ (supFrom 0 (x : Mt g n)))⁻¹ * Φ (toG (tl a (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n))) (toG (br a b (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n))) else 0) = 0 := by
  intro g _ ψ hψ a b n σ Φ i j _ hi hj hσ
  obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hψ (by ext t; simpa using hc t)
  have hlt : σ i < σ j := by rw [Fin.lt_def]; omega
  set F : Gn g n → ℂ := fun x => if IsUniUp (x : Mt g n) ∧ InPar a (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n) then (ψ (supFrom 0 (x : Mt g n)))⁻¹ * Φ (toG (tl a (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n))) (toG (br a b (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n))) else 0 with hF
  have key : ∀ x, F (x * elem (σ i) (σ j) hlt.ne t) = (ψ t)⁻¹ * F x := by
    intro x
    have h1 := mul_elem_apply (σ i) (σ j) hlt.ne t x
    have h2 : ∀ r c, (((pm g σ)⁻¹ * (x * elem (σ i) (σ j) hlt.ne t) * pm g σ : Gn g n) : Mt g n) r c
        = (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n) r c
          + if c = j then t * (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n) r i else 0 := by
      intro r c
      rw [conj_apply, conj_apply, conj_apply, h1]
      simp only [σ.apply_eq_iff_eq]
    simp only [hF]
    rw [isUniUp_iff_of_col hlt t h1, inPar_iff_of_col hj t h2]
    split_ifs with hx
    · rw [supFrom_of_col hσ t h1 hx.1, tl_of_col hj t h2, br_of_col hi t h2 hx.2, AddChar.map_add_eq_mul,
        mul_inv]
      ring
    · simp
  have hS : ∑ x, F x = (ψ t)⁻¹ * ∑ x, F x := by
    rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulRight (elem (σ i) (σ j) hlt.ne t)) F]
    exact Finset.sum_congr rfl fun x _ => key x
  change ∑ x, F x = 0
  by_contra hne
  apply ht
  have : (ψ t)⁻¹ = 1 := mul_right_cancel₀ hne (by rw [one_mul]; exact hS.symm)
  exact inv_eq_one.1 this

end GlobalTheory.GLm.NonOpenCell
