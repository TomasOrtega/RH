import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic

open Matrix GroundTheory.Automorphic GroundTheory.Automorphic.Iwasawa PositivityTheory.JacquetShalikaLocal

namespace GlobalTheory.CompanionTheory.JSBound.ColumnUnipotent

section Algebra

variable {F : Type} [Field F] {n : ℕ}

/- English proof (translation)
Simplify using `only [cM, Matrix.of_apply]`. Rewrite using `[dif_neg h]`.
-/
theorem cM_eq_zero_of_ne {k : ℕ} (x : Fin (k + 1) → F) {i j : Fin n}
    (h : ¬ ((j : ℕ) = k + 1 ∧ (i : ℕ) < k + 1)) : cM n k x i j = 0 := by
  simp only [cM, Matrix.of_apply]
  rw [dif_neg h]

/- English proof (translation)
Simplify using `only [cM, Matrix.of_apply]`. Rewrite using `[dif_pos ⟨hj, hi⟩]`.
-/
theorem cM_eq_of {k : ℕ} (x : Fin (k + 1) → F) {i j : Fin n} (hj : (j : ℕ) = k + 1)
    (hi : (i : ℕ) < k + 1) : cM n k x i j = x ⟨i, hi⟩ := by
  simp only [cM, Matrix.of_apply]
  rw [dif_pos ⟨hj, hi⟩]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem col_val (k : ℕ) (x : Fin (k + 1) → F) :
    ((col n k x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + cM n k x := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem col_inv_val (k : ℕ) (x : Fin (k + 1) → F) :
    (((col n k x)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 - cM n k x := rfl

/- English proof (translation)
Use `⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Establish `hij' : (j : ℕ) < i` using `hij`. Rewrite using `[col_val, Matrix.add_apply, Matrix.one_apply_ne (by intro e; subst e; omega), cM_eq_zero_of_ne x (by omega), add_zero]`. Rewrite using `[col_val, Matrix.add_apply, Matrix.one_apply_eq, cM_eq_zero_of_ne x (by omega), add_zero]`.
-/
theorem col_mem (k : ℕ) (x : Fin (k + 1) → F) : col n k x ∈ unipotent F n := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hij' : (j : ℕ) < i := hij
    rw [col_val, Matrix.add_apply, Matrix.one_apply_ne (by intro e; subst e; omega),
      cM_eq_zero_of_ne x (by omega), add_zero]
  · rw [col_val, Matrix.add_apply, Matrix.one_apply_eq, cM_eq_zero_of_ne x (by omega), add_zero]

/- English proof (translation)
Unfold `Whittaker.superdiagSum`. Rewrite using `[Finset.sum_eq_single (⟨k, by omega⟩ : Fin n), Finset.sum_eq_single (⟨k + 1, hk⟩ : Fin n)]`. Rewrite using `[if_pos rfl, cM_eq_of x rfl (by simp)]`. Both sides reduce to the same expression. Introduce `j _ hj`.

Rewrite using `[if_neg]`. Introduce `e`. Conclude with `hj (Fin.ext (by simpa using e))`. Simplify using the standard rewrite rules. Introduce `i _ hi`.

Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Use `cM_eq_zero_of_ne x fun h' => hi (Fin.ext ?_)` and prove the remaining obligations. Simplify using `only`. Use linear arithmetic over natural numbers and integers.

Both sides reduce to the same expression. Simplify using the standard rewrite rules.
-/
theorem superdiagSum_cM {k : ℕ} (hk : k + 1 < n) (x : Fin (k + 1) → F) :
    Whittaker.superdiagSum (cM n k x) = x (Fin.last k) := by
  unfold Whittaker.superdiagSum
  rw [Finset.sum_eq_single (⟨k, by omega⟩ : Fin n), Finset.sum_eq_single (⟨k + 1, hk⟩ : Fin n)]
  · rw [if_pos rfl, cM_eq_of x rfl (by simp)]
    rfl
  · intro j _ hj
    rw [if_neg]
    intro e
    exact hj (Fin.ext (by simpa using e))
  · simp
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    split_ifs with h
    · refine cM_eq_zero_of_ne x fun h' => hi (Fin.ext ?_)
      simp only
      omega
    · rfl
  · simp

/- English proof (translation)
Rewrite using `[Whittaker.psiN, col_val, Whittaker.superdiagSum_add, Whittaker.superdiagSum_one, zero_add, superdiagSum_cM hk]`.
-/
theorem psiN_col (ψ : AddChar F ℂ) {k : ℕ} (hk : k + 1 < n) (x : Fin (k + 1) → F) :
    Whittaker.psiN ψ (col n k x) = ψ (x (Fin.last k)) := by
  rw [Whittaker.psiN, col_val, Whittaker.superdiagSum_add, Whittaker.superdiagSum_one, zero_add,
    superdiagSum_cM hk]

/- English proof (translation)
Establish `h : M * cM n k x = 1 * cM n k x`. Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `hl : (l : ℕ) ≤ k`.

Rewrite using `[hM i l hl]`. Rewrite using `[cM_eq_zero_of_ne x (i := l) (j := j) (by omega), mul_zero, mul_zero]`. Rewrite using `[h, one_mul]`.
-/
theorem mul_cM {k : ℕ} {M : Matrix (Fin n) (Fin n) F}
    (hM : ∀ i j : Fin n, (j : ℕ) ≤ k → M i j = (1 : Matrix (Fin n) (Fin n) F) i j)
    (x : Fin (k + 1) → F) : M * cM n k x = cM n k x := by
  have h : M * cM n k x = 1 * cM n k x := by
    ext i j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : (l : ℕ) ≤ k
    · rw [hM i l hl]
    · rw [cM_eq_zero_of_ne x (i := l) (j := j) (by omega), mul_zero, mul_zero]
  rw [h, one_mul]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem conj_expand {M C : Matrix (Fin n) (Fin n) F} (hMC : M * C = C) (hCC : C * C = 0) :
    (1 + C) * M * (1 - C) = M + C * M - C := by
  calc (1 + C) * M * (1 - C) = M + C * M - M * C - C * (M * C) := by noncomm_ring
    _ = M + C * M - C := by rw [hMC, hCC, sub_zero]

end Algebra

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

/- English proof (translation)
Take `⟨hu, hc⟩` from `hg`. Set `x : Fin (k + 1) → F` to `fun i => (g : Matrix (Fin n) (Fin n) F) ⟨i, by omega⟩ ⟨k + 1, hk⟩`. Establish `hv : ((g * (col n k x)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = (g : Matrix (Fin n) (Fin n) F) - cM n k x`. Rewrite using `[Units.val_mul, col_inv_val, mul_sub, mul_one, mul_cM hc]`. Establish `hm : g * (col n k x)⁻¹ ∈ unipotent F n` using `(unipotent F n).mul_mem hu ((unipotent F n).inv_mem (col_mem k x))`.

Use `⟨g * (col n k x)⁻¹, x, ⟨hm, fun i j hj => ?_⟩, (inv_mul_cancel_right _ _).symm, ?_⟩` and prove the remaining obligations. Rewrite using `[hv, Matrix.sub_apply]`. Distinguish the cases in `hjk : (j : ℕ) ≤ k`. Rewrite using `[cM_eq_zero_of_ne x (by omega), sub_zero, hc i j hjk]`. Establish `hj' : (j : ℕ) = k + 1` using `by omega`.

Distinguish the cases in `hi : (i : ℕ) < k + 1`. Establish `hx : x ⟨i, hi⟩ = (g : Matrix (Fin n) (Fin n) F) i j`. Establish `e : j = ⟨k + 1, hk⟩` using `Fin.ext hj'`. Substitute `e` using the available equality. Both sides reduce to the same expression.

Rewrite using `[cM_eq_of x hj' hi, hx, sub_self, Matrix.one_apply_ne (by intro e; subst e; omega)]`. Rewrite using `[cM_eq_zero_of_ne x (by omega), sub_zero]`. Distinguish the cases in `e : i = j`. Substitute `e` using the available equality. Rewrite using `[hu.2, Matrix.one_apply_eq]`.

Establish `hlt : id j < id i`. Establish `: (j : ℕ) < i`. Establish `: (i : ℕ) ≠ j` using `fun h => e (Fin.ext h)`. Use linear arithmetic over natural numbers and integers. Conclude with `this`.

Rewrite using `[hu.1 hlt, Matrix.one_apply_ne e]`. Establish `h : Whittaker.psiN ψ g = Whittaker.psiN ψ (g * (col n k x)⁻¹ * col n k x)`. Rewrite using `[inv_mul_cancel_right]`. Rewrite using `[h, Whittaker.psiN_mul ψ hm (col_mem k x), psiN_col ψ hk]`.
-/
theorem inU_split (ψ : AddChar F ℂ) {k : ℕ} (hk : k + 1 < n) (g : GL (Fin n) F) (hg : inU k g) :
    ∃ (g' : GL (Fin n) F) (x : Fin (k + 1) → F), inU (k + 1) g' ∧ g = g' * col n k x ∧
      Whittaker.psiN ψ g = Whittaker.psiN ψ g' * ψ (x (Fin.last k)) := by
  obtain ⟨hu, hc⟩ := hg
  let x : Fin (k + 1) → F := fun i => (g : Matrix (Fin n) (Fin n) F) ⟨i, by omega⟩ ⟨k + 1, hk⟩
  have hv : ((g * (col n k x)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (g : Matrix (Fin n) (Fin n) F) - cM n k x := by
    rw [Units.val_mul, col_inv_val, mul_sub, mul_one, mul_cM hc]
  have hm : g * (col n k x)⁻¹ ∈ unipotent F n :=
    (unipotent F n).mul_mem hu ((unipotent F n).inv_mem (col_mem k x))
  refine ⟨g * (col n k x)⁻¹, x, ⟨hm, fun i j hj => ?_⟩, (inv_mul_cancel_right _ _).symm, ?_⟩
  · rw [hv, Matrix.sub_apply]
    by_cases hjk : (j : ℕ) ≤ k
    · rw [cM_eq_zero_of_ne x (by omega), sub_zero, hc i j hjk]
    · have hj' : (j : ℕ) = k + 1 := by omega
      by_cases hi : (i : ℕ) < k + 1
      · have hx : x ⟨i, hi⟩ = (g : Matrix (Fin n) (Fin n) F) i j := by
          have e : j = ⟨k + 1, hk⟩ := Fin.ext hj'
          subst e
          rfl
        rw [cM_eq_of x hj' hi, hx, sub_self, Matrix.one_apply_ne (by intro e; subst e; omega)]
      · rw [cM_eq_zero_of_ne x (by omega), sub_zero]
        by_cases e : i = j
        · subst e
          rw [hu.2, Matrix.one_apply_eq]
        · have hlt : id j < id i := by
            have : (j : ℕ) < i := by
              have : (i : ℕ) ≠ j := fun h => e (Fin.ext h)
              omega
            exact this
          rw [hu.1 hlt, Matrix.one_apply_ne e]
  · have h : Whittaker.psiN ψ g = Whittaker.psiN ψ (g * (col n k x)⁻¹ * col n k x) := by
      rw [inv_mul_cancel_right]
    rw [h, Whittaker.psiN_mul ψ hm (col_mem k x), psiN_col ψ hk]

/- English proof (translation)
Take `⟨hu, hc⟩` from `hg`. Establish `hcol : col n k x ∈ unipotent F n` using `col_mem k x`. Establish `hcg` using `(unipotent F n).mul_mem hcol hu`. Establish `hinv` using `(unipotent F n).inv_mem hcol`. Establish `hv : ((col n k x * g * (col n k x)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = (g : Matrix (Fin n) (Fin n) F) + cM n k x * (g : Matrix (Fin n) (Fin n) F) - cM n k x`.

Rewrite using `[Units.val_mul, Units.val_mul, col_val, col_inv_val]`. Conclude with `conj_expand (mul_cM (fun i j hj => hc i j (by omega)) x) (cM_mul k x x)`. Use `⟨col n k x * g * (col n k x)⁻¹, ⟨(unipotent F n).mul_mem hcg hinv, fun i j hj => ?_⟩, (inv_mul_cancel_right _ _).symm, ?_⟩` and prove the remaining obligations. Establish `hC : (cM n k x * (g : Matrix (Fin n) (Fin n) F)) i j = cM n k x i j`. Rewrite using `[Matrix.mul_apply, Finset.sum_congr rfl fun l _ => by rw [hc l j hj], ← Matrix.mul_apply, mul_one]`.

Rewrite using `[hv, Matrix.sub_apply, Matrix.add_apply, hC, hc i j hj, add_sub_cancel_right]`. Establish `h0` using `Whittaker.psiN_ne_zero ψ (col n k x)`. Rewrite using `[Whittaker.psiN_mul ψ hcg hinv, Whittaker.psiN_mul ψ hcol hu, Whittaker.psiN_inv ψ hcol]`. Clear the denominators using the available nonvanishing facts.
-/
theorem inU_conj (ψ : AddChar F ℂ) {k : ℕ} (g : GL (Fin n) F) (hg : inU (k + 1) g)
    (x : Fin (k + 1) → F) :
    ∃ g' : GL (Fin n) F, inU (k + 1) g' ∧ col n k x * g = g' * col n k x ∧
      Whittaker.psiN ψ g' = Whittaker.psiN ψ g := by
  obtain ⟨hu, hc⟩ := hg
  have hcol : col n k x ∈ unipotent F n := col_mem k x
  have hcg := (unipotent F n).mul_mem hcol hu
  have hinv := (unipotent F n).inv_mem hcol
  have hv : ((col n k x * g * (col n k x)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (g : Matrix (Fin n) (Fin n) F) + cM n k x * (g : Matrix (Fin n) (Fin n) F) - cM n k x := by
    rw [Units.val_mul, Units.val_mul, col_val, col_inv_val]
    exact conj_expand (mul_cM (fun i j hj => hc i j (by omega)) x) (cM_mul k x x)
  refine ⟨col n k x * g * (col n k x)⁻¹, ⟨(unipotent F n).mul_mem hcg hinv, fun i j hj => ?_⟩,
    (inv_mul_cancel_right _ _).symm, ?_⟩
  · have hC : (cM n k x * (g : Matrix (Fin n) (Fin n) F)) i j = cM n k x i j := by
      rw [Matrix.mul_apply, Finset.sum_congr rfl fun l _ => by rw [hc l j hj], ← Matrix.mul_apply,
        mul_one]
    rw [hv, Matrix.sub_apply, Matrix.add_apply, hC, hc i j hj, add_sub_cancel_right]
  · have h0 := Whittaker.psiN_ne_zero ψ (col n k x)
    rw [Whittaker.psiN_mul ψ hcg hinv, Whittaker.psiN_mul ψ hcol hu, Whittaker.psiN_inv ψ hcol]
    field_simp

end Local

/- English proof (translation)
Introduce `F _ _ _ _ _ _ μ _ ψ _ n k hk`. Conclude with `⟨fun g hg => inU_split ψ hk g hg, fun g hg x => inU_conj ψ g hg x⟩`.
-/
theorem main : ColumnsUnipotent := by
  intro F _ _ _ _ _ _ μ _ ψ _ n k hk
  exact ⟨fun g hg => inU_split ψ hk g hg, fun g hg x => inU_conj ψ g hg x⟩

end GlobalTheory.CompanionTheory.JSBound.ColumnUnipotent
