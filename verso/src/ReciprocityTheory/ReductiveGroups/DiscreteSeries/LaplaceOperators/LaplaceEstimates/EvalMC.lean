import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.ColAnti
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.HaarRightStatement

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.EvalC

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

section Alg

variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ}

def actU (E : Fin n → Fin n → 𝒰) (X : Matrix (Fin n) (Fin n) ℂ) : 𝒰 := ∑ i, ∑ j, X i j • E i j

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem sum_four_swap_pairs_alt {β : Type*} [AddCommMonoid β] (f : Fin n → Fin n → Fin n → Fin n → β) :
    ∑ k, ∑ l, ∑ i, ∑ j, f i j k l = ∑ i, ∑ j, ∑ k, ∑ l, f i j k l := by
  calc ∑ k, ∑ l, ∑ i, ∑ j, f i j k l = ∑ k, ∑ i, ∑ l, ∑ j, f i j k l :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ l, ∑ j, f i j k l := Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ k, ∑ l, f i j k l := Finset.sum_congr rfl fun i _ =>
        (Finset.sum_congr rfl fun k _ => Finset.sum_comm).trans Finset.sum_comm

/- English proof (translation)
Simplify using `only [actU, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]`. Conclude with `sum_four_swap_pairs_alt (fun i j k l => (X i j * Y k l) • (E i j * E k l))`.
-/
theorem actU_mul (E : Fin n → Fin n → 𝒰) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    actU E X * actU E Y = ∑ i, ∑ j, ∑ k, ∑ l, (X i j * Y k l) • (E i j * E k l) := by
  simp only [actU, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
  exact sum_four_swap_pairs_alt (fun i j k l => (X i j * Y k l) • (E i j * E k l))

/- English proof (translation)
Rewrite using `[actU_mul, actU_mul, ← sum_four_swap_pairs_alt (fun i j k l => (Y i j * X k l) • (E i j * E k l))]`. Simplify using `only [← Finset.sum_sub_distrib]`. Establish `h1 : ∀ i j k l, (X i j * Y k l) • (E i j * E k l) - (Y k l * X i j) • (E k l * E i j) = (X i j * Y k l) • ((if j = k then E i l else 0) - (if l = i then E k j else 0))`. Introduce `i j k l`. Rewrite using `[← hE i j k l, mul_comm (Y k l), smul_sub]`.

Simplify using `only [h1, smul_sub, Finset.sum_sub_distrib, smul_ite, smul_zero]`. Simplify using `only [actU, Matrix.sub_apply, Matrix.mul_apply, sub_smul, Finset.sum_sub_distrib, Finset.sum_smul]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hj : ∀ j, ∑ k, ∑ l, (if j = k then (X i j * Y k l) • E i l else 0) = ∑ l, (X i j * Y j l) • E i l`.

Introduce `j`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_congr rfl fun j _ => hj j, Finset.sum_comm]`.

Establish `hl : ∀ i j k, ∑ l, (if l = i then (X i j * Y k l) • E k j else 0) = (Y k i * X i j) • E k j`. Introduce `i j k`. Simplify using `[mul_comm]`. Simplify using `only [hl]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem actU_bracket (E : Fin n → Fin n → 𝒰) (hE : GlRelR E) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    actU E X * actU E Y - actU E Y * actU E X = actU E (X * Y - Y * X) := by
  rw [actU_mul, actU_mul, ← sum_four_swap_pairs_alt (fun i j k l => (Y i j * X k l) • (E i j * E k l))]
  simp only [← Finset.sum_sub_distrib]
  have h1 : ∀ i j k l, (X i j * Y k l) • (E i j * E k l) - (Y k l * X i j) • (E k l * E i j) =
      (X i j * Y k l) • ((if j = k then E i l else 0) - (if l = i then E k j else 0)) := by
    intro i j k l; rw [← hE i j k l, mul_comm (Y k l), smul_sub]
  simp only [h1, smul_sub, Finset.sum_sub_distrib, smul_ite, smul_zero]
  simp only [actU, Matrix.sub_apply, Matrix.mul_apply, sub_smul, Finset.sum_sub_distrib, Finset.sum_smul]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hj : ∀ j, ∑ k, ∑ l, (if j = k then (X i j * Y k l) • E i l else 0) =
        ∑ l, (X i j * Y j l) • E i l := by
      intro j; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun l _ => ?_; simp
    rw [Finset.sum_congr rfl fun j _ => hj j, Finset.sum_comm]
  · have hl : ∀ i j k, ∑ l, (if l = i then (X i j * Y k l) • E k j else 0) = (Y k i * X i j) • E k j := by
      intro i j k; simp [mul_comm]
    simp only [hl]
    calc ∑ i, ∑ j, ∑ k, (Y k i * X i j) • E k j = ∑ i, ∑ k, ∑ j, (Y k i * X i j) • E k j :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, (Y k i * X i j) • E k j := Finset.sum_comm
      _ = ∑ k, ∑ j, ∑ i, (Y k i * X i j) • E k j := Finset.sum_congr rfl fun k _ => Finset.sum_comm

/- English proof (translation)
Simplify using `[actU, sub_smul, Finset.sum_sub_distrib]`.
-/
theorem actU_sub (E : Fin n → Fin n → 𝒰) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    actU E (X - Y) = actU E X - actU E Y := by
  simp [actU, sub_smul, Finset.sum_sub_distrib]

/- English proof (translation)
Simplify using `[actU, smul_smul, Finset.smul_sum]`.
-/
theorem actU_smul (E : Fin n → Fin n → 𝒰) (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    actU E (c • X) = c • actU E X := by
  simp [actU, smul_smul, Finset.smul_sum]

def frameAB (A B : Matrix (Fin n) (Fin n) ℂ) (E : Fin n → Fin n → 𝒰) (a b : Fin n) : 𝒰 :=
  ∑ i, ∑ j, (A a i * B j b) • E i j

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem frameAB_eq_actU (A B : Matrix (Fin n) (Fin n) ℂ) (E : Fin n → Fin n → 𝒰) (a b : Fin n) :
    frameAB A B E a b = actU E (Matrix.of fun i j => A a i * B j b) := rfl

/- English proof (translation)
Establish `h : ∑ l, A c l * B l b = if b = c then 1 else 0`. Use `congrFun (congrFun hAB c) b` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Matrix.one_apply]`. Rewrite using `[this]`. Distinguish the cases in `hbc : b = c`.

Substitute `hbc` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hbc, Ne.symm hbc]`. Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by rw [h]; ring`.
-/
theorem frameX_mul (A B : Matrix (Fin n) (Fin n) ℂ) (hAB : A * B = 1) (a b c d : Fin n) :
    (Matrix.of fun i j => A a i * B j b) * (Matrix.of fun i j => A c i * B j d) =
      (if b = c then (1 : ℂ) else 0) • (Matrix.of fun i j => A a i * B j d) := by
  have h : ∑ l, A c l * B l b = if b = c then 1 else 0 := by
    have := congrFun (congrFun hAB c) b
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [this]
    by_cases hbc : b = c
    · subst hbc; simp
    · simp [hbc, Ne.symm hbc]
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  calc ∑ l, A a i * B l b * (A c l * B j d) = (A a i * B j d) * ∑ l, A c l * B l b := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun l _ => ?_; ring
    _ = _ := by rw [h]; ring

/- English proof (translation)
Introduce `a b c d`. Simplify using `only [frameAB_eq_actU]`. Rewrite using `[actU_bracket E hE, frameX_mul A B hAB, frameX_mul A B hAB, actU_sub, actU_smul, actU_smul]`. Use `congr 1`. Apply the tactic sequence `split_ifs <;> simp`.

Apply the tactic sequence `split_ifs <;> simp_all`.
-/
theorem frameAB_glRel (A B : Matrix (Fin n) (Fin n) ℂ) (hAB : A * B = 1) (E : Fin n → Fin n → 𝒰)
    (hE : GlRelR E) : GlRelR (frameAB A B E) := by
  intro a b c d
  simp only [frameAB_eq_actU]
  rw [actU_bracket E hE, frameX_mul A B hAB, frameX_mul A B hAB, actU_sub, actU_smul, actU_smul]
  congr 1
  · split_ifs <;> simp
  · split_ifs <;> simp_all

variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ}

/- English proof (translation)
Apply the tactic sequence `have h1 : capEntry (frameAB A B E) x a b = ∑ i, ∑ j, (A a i * B j b) • capEntry E x i j := by`. Simplify using `only [capEntry, frameAB, smul_add, Finset.sum_add_distrib]`. Use `congr 1`. Simplify using `only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite using `[← Finset.sum_smul]`.

Establish `: (∑ i, A a i * B i b) = if a = b then 1 else 0`. Rewrite using `[← Matrix.mul_apply, hAB, Matrix.one_apply]`. Apply the tactic sequence `rw [this]; split_ifs <;> simp`. Rewrite using `[h1]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul]`.
-/
theorem capEntry_frameAB (A B : Matrix (Fin n) (Fin n) ℂ) (hAB : A * B = 1) (E : Fin n → Fin n → 𝒰)
    (x : ℂ) (a b : Fin n) :
    capEntry (frameAB A B E) x a b = ∑ i, A a i • ∑ j, B j b • capEntry E x i j := by
  have h1 : capEntry (frameAB A B E) x a b = ∑ i, ∑ j, (A a i * B j b) • capEntry E x i j := by
    simp only [capEntry, frameAB, smul_add, Finset.sum_add_distrib]
    congr 1
    simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← Finset.sum_smul]
    have : (∑ i, A a i * B i b) = if a = b then 1 else 0 := by
      rw [← Matrix.mul_apply, hAB, Matrix.one_apply]
    rw [this]; split_ifs <;> simp
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]

/- English proof (translation)
Proceed by induction on `p with`. Consider the case `zero => intro c X`. Simplify using the standard rewrite rules. Consider the case `succ p ih`. Introduce `c X`.

Rewrite using `[List.ofFn_succ, List.prod_cons, ih (fun j => c j.succ) (fun j => X j.succ), Finset.sum_mul_sum, ← (Fin.consEquiv fun _ : Fin (p + 1) => κ).sum_comp, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun f _ => ?_` and prove the remaining obligations. Simplify using `only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, List.ofFn_succ, List.prod_cons, smul_mul_smul_comm]`.
-/
theorem prod_ofFn_sum {κ : Type*} [Fintype κ] (p : ℕ) : ∀ (c : Fin p → κ → ℂ) (X : Fin p → κ → 𝒰),
    (List.ofFn fun j => ∑ t, c j t • X j t).prod =
      ∑ f : Fin p → κ, (∏ j, c j (f j)) • (List.ofFn fun j => X j (f j)).prod := by
  induction p with
  | zero => intro c X; simp
  | succ p ih =>
    intro c X
    rw [List.ofFn_succ, List.prod_cons, ih (fun j => c j.succ) (fun j => X j.succ),
      Finset.sum_mul_sum, ← (Fin.consEquiv fun _ : Fin (p + 1) => κ).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun f _ => ?_
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      List.ofFn_succ, List.prod_cons, smul_mul_smul_comm]

def prodIT (E : Fin n → Fin n → 𝒰) {p : ℕ} (x : ℂ) (ι τ : Fin p → Fin n) : 𝒰 :=
  (List.ofFn fun j : Fin p => capEntry E (x - ((j : ℕ) : ℂ)) (ι j) (τ j)).prod

/- English proof (translation)
Unfold `cminor prodIT`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[← Int.cast_smul_eq_zsmul ℂ]`. Both sides reduce to the same expression.
-/
theorem cminor_eq_sum_prodIT (E : Fin n → Fin n → 𝒰) {p : ℕ} (R C : Fin p → Fin n) (x : ℂ) :
    cminor E R C x = ∑ σ : Equiv.Perm (Fin p), ((Equiv.Perm.sign σ : ℤˣ) : ℂ) • prodIT E x (R ∘ σ) C := by
  unfold cminor prodIT
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Int.cast_smul_eq_zsmul ℂ]
  rfl

/- English proof (translation)
Rewrite using `[cminor_eq_sum_prodIT]`. Establish `h1 : ∀ σ : Equiv.Perm (Fin p), prodIT (frameAB A B E) x (R ∘ σ) C = ∑ ι : Fin p → Fin n, ∑ τ : Fin p → Fin n, ((∏ j, A (R (σ j)) (ι j)) * ∏ j, B (τ j) (C j)) • prodIT E x ι τ`. Introduce `σ`. Unfold `prodIT`. Simplify using `only [Function.comp_apply, capEntry_frameAB A B hAB]`.

Rewrite using `[prod_ofFn_sum]`. Use `Finset.sum_congr rfl fun ι _ => ?_` and prove the remaining obligations. Rewrite using `[prod_ofFn_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul]`.

Simplify using `only [h1, Finset.smul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun ι _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Simplify using `only [smul_smul]`. Rewrite using `[← Finset.sum_smul, Matrix.det_apply', Finset.sum_mul]`. Use `congr 1`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.submatrix_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem cminor_frameAB_expand (A B : Matrix (Fin n) (Fin n) ℂ) (hAB : A * B = 1) (E : Fin n → Fin n → 𝒰)
    {p : ℕ} (R C : Fin p → Fin n) (x : ℂ) :
    cminor (frameAB A B E) R C x = ∑ ι : Fin p → Fin n, ∑ τ : Fin p → Fin n,
      ((A.submatrix R ι).det * ∏ j, B (τ j) (C j)) • prodIT E x ι τ := by
  rw [cminor_eq_sum_prodIT]
  have h1 : ∀ σ : Equiv.Perm (Fin p), prodIT (frameAB A B E) x (R ∘ σ) C =
      ∑ ι : Fin p → Fin n, ∑ τ : Fin p → Fin n,
        ((∏ j, A (R (σ j)) (ι j)) * ∏ j, B (τ j) (C j)) • prodIT E x ι τ := by
    intro σ
    unfold prodIT
    simp only [Function.comp_apply, capEntry_frameAB A B hAB]
    rw [prod_ofFn_sum]
    refine Finset.sum_congr rfl fun ι _ => ?_
    rw [prod_ofFn_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [smul_smul]
  simp only [h1, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [smul_smul]
  rw [← Finset.sum_smul, Matrix.det_apply', Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Matrix.submatrix_apply]
  ring

def precompEquiv {p m : ℕ} (σ : Equiv.Perm (Fin p)) : (Fin p → Fin m) ≃ (Fin p → Fin m) where
  toFun ρ := ρ ∘ σ
  invFun ι := ι ∘ σ.symm
  left_inv ρ := by funext j; simp
  right_inv ι := by funext j; simp

/- English proof (translation)
Simplify using `only [cminor_eq_sum_prodIT, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Establish `key : ∀ σ : Equiv.Perm (Fin p), ∑ ρ : Fin p → Fin n, ((A.submatrix R ρ).det * ((Equiv.Perm.sign σ : ℤˣ) : ℂ)) • prodIT E x (ρ ∘ σ) τ = ∑ ι : Fin p → Fin n, (A.submatrix R ι).det • prodIT E x ι τ`. Introduce `σ`. Use `Fintype.sum_equiv (precompEquiv σ) _ _ (fun ρ => ?_)` and prove the remaining obligations.

Establish `: A.submatrix R (ρ ∘ σ) = (A.submatrix R ρ).submatrix id σ` using `rfl`. Simplify using `only [precompEquiv, Equiv.coe_fn_mk, this, Matrix.det_permute']`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl (fun σ _ => key σ), Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun ι _ => ?_` and prove the remaining obligations. Rewrite using `[← Nat.cast_smul_eq_nsmul ℂ, smul_smul]`.
-/
theorem row_collapse (E : Fin n → Fin n → 𝒰) {p : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (R τ : Fin p → Fin n)
    (x : ℂ) :
    ((p.factorial : ℕ) : ℂ) • ∑ ι : Fin p → Fin n, (A.submatrix R ι).det • prodIT E x ι τ =
      ∑ ρ : Fin p → Fin n, (A.submatrix R ρ).det • cminor E ρ τ x := by
  simp only [cminor_eq_sum_prodIT, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have key : ∀ σ : Equiv.Perm (Fin p), ∑ ρ : Fin p → Fin n,
      ((A.submatrix R ρ).det * ((Equiv.Perm.sign σ : ℤˣ) : ℂ)) • prodIT E x (ρ ∘ σ) τ =
      ∑ ι : Fin p → Fin n, (A.submatrix R ι).det • prodIT E x ι τ := by
    intro σ
    refine Fintype.sum_equiv (precompEquiv σ) _ _ (fun ρ => ?_)
    have : A.submatrix R (ρ ∘ σ) = (A.submatrix R ρ).submatrix id σ := rfl
    simp only [precompEquiv, Equiv.coe_fn_mk, this, Matrix.det_permute']
    congr 1; ring
  rw [Finset.sum_congr rfl (fun σ _ => key σ), Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]

/- English proof (translation)
Simplify using `only [Matrix.det_apply', Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Establish `key : ∀ σ : Equiv.Perm (Fin p), ∑ τ : Fin p → Fin n, (((Equiv.Perm.sign σ : ℤˣ) : ℂ) * ∏ l, B.submatrix τ C (σ l) l) • cminor E ρ τ x = ∑ τ : Fin p → Fin n, (∏ j, B (τ j) (C j)) • cminor E ρ τ x`. Introduce `σ`. Use `Fintype.sum_equiv (precompEquiv σ) _ _ (fun τ => ?_)` and prove the remaining obligations.

Simplify using `only [precompEquiv, Equiv.coe_fn_mk, Matrix.submatrix_apply, Function.comp_apply]`. Rewrite using `[cminor_perm_cols E hE ρ τ σ x, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl (fun σ _ => key σ), Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, Nat.cast_smul_eq_nsmul ℂ]`.
-/
theorem col_collapse (E : Fin n → Fin n → 𝒰) (hE : GlRelR E) {p : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (ρ C : Fin p → Fin n) (x : ℂ) :
    ((p.factorial : ℕ) : ℂ) • ∑ τ : Fin p → Fin n, (∏ j, B (τ j) (C j)) • cminor E ρ τ x =
      ∑ τ : Fin p → Fin n, (B.submatrix τ C).det • cminor E ρ τ x := by
  simp only [Matrix.det_apply', Finset.sum_smul]
  rw [Finset.sum_comm]
  have key : ∀ σ : Equiv.Perm (Fin p), ∑ τ : Fin p → Fin n,
      (((Equiv.Perm.sign σ : ℤˣ) : ℂ) * ∏ l, B.submatrix τ C (σ l) l) • cminor E ρ τ x =
      ∑ τ : Fin p → Fin n, (∏ j, B (τ j) (C j)) • cminor E ρ τ x := by
    intro σ
    refine Fintype.sum_equiv (precompEquiv σ) _ _ (fun τ => ?_)
    simp only [precompEquiv, Equiv.coe_fn_mk, Matrix.submatrix_apply, Function.comp_apply]
    rw [cminor_perm_cols E hE ρ τ σ x, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
    congr 1; ring
  rw [Finset.sum_congr rfl (fun σ _ => key σ), Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, Nat.cast_smul_eq_nsmul ℂ]

/- English proof (translation)
Use `set f : ℂ := ((p.factorial : ℕ) : ℂ)`. Establish `h1 : cminor (frameAB A B E) R C x = ∑ τ : Fin p → Fin n, (∏ j, B (τ j) (C j)) • ∑ ι : Fin p → Fin n, (A.submatrix R ι).det • prodIT E x ι τ`. Rewrite using `[cminor_frameAB_expand A B hAB, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun ι _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, mul_comm]`. Establish `h2 : f • cminor (frameAB A B E) R C x = ∑ ρ : Fin p → Fin n, (A.submatrix R ρ).det • ∑ τ : Fin p → Fin n, (∏ j, B (τ j) (C j)) • cminor E ρ τ x`. Rewrite using `[h1, Finset.smul_sum]`. Establish `e1 : ∀ τ : Fin p → Fin n, f • ((∏ j, B (τ j) (C j)) • ∑ ι : Fin p → Fin n, (A.submatrix R ι).det • prodIT E x ι τ) = (∏ j, B (τ j) (C j)) • ∑ ρ : Fin p → Fin n, (A.submatrix R ρ).det • cminor E ρ τ x`.

Introduce `τ`. Rewrite using `[smul_comm, row_collapse]`. Rewrite using `[Finset.sum_congr rfl (fun τ _ => e1 τ)]`. Simplify using `only [Finset.smul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[smul_comm]`. Rewrite using `[mul_smul, h2, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun ρ _ => ?_` and prove the remaining obligations. Rewrite using `[smul_comm, col_collapse E hE B ρ C x, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul]`.
-/
theorem cminor_frameAB_cb (E : Fin n → Fin n → 𝒰) (hE : GlRelR E) (A B : Matrix (Fin n) (Fin n) ℂ)
    (hAB : A * B = 1) {p : ℕ} (R C : Fin p → Fin n) (x : ℂ) :
    (((p.factorial : ℕ) : ℂ) * ((p.factorial : ℕ) : ℂ)) • cminor (frameAB A B E) R C x =
      ∑ ρ : Fin p → Fin n, ∑ τ : Fin p → Fin n,
        ((A.submatrix R ρ).det * (B.submatrix τ C).det) • cminor E ρ τ x := by
  set f : ℂ := ((p.factorial : ℕ) : ℂ)
  have h1 : cminor (frameAB A B E) R C x = ∑ τ : Fin p → Fin n, (∏ j, B (τ j) (C j)) •
      ∑ ι : Fin p → Fin n, (A.submatrix R ι).det • prodIT E x ι τ := by
    rw [cminor_frameAB_expand A B hAB, Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun ι _ => ?_
    rw [smul_smul, mul_comm]
  have h2 : f • cminor (frameAB A B E) R C x = ∑ ρ : Fin p → Fin n, (A.submatrix R ρ).det •
      ∑ τ : Fin p → Fin n, (∏ j, B (τ j) (C j)) • cminor E ρ τ x := by
    rw [h1, Finset.smul_sum]
    have e1 : ∀ τ : Fin p → Fin n, f • ((∏ j, B (τ j) (C j)) •
        ∑ ι : Fin p → Fin n, (A.submatrix R ι).det • prodIT E x ι τ) =
        (∏ j, B (τ j) (C j)) • ∑ ρ : Fin p → Fin n, (A.submatrix R ρ).det • cminor E ρ τ x := by
      intro τ; rw [smul_comm, row_collapse]
    rw [Finset.sum_congr rfl (fun τ _ => e1 τ)]
    simp only [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun τ _ => ?_
    rw [smul_comm]
  rw [mul_smul, h2, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [smul_comm, col_collapse E hE B ρ C x, Finset.smul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [smul_smul]

/- English proof (translation)
Establish `hR : ((m.factorial : ℕ) : ℂ) • ∑ c : Fin (m + 1), F c.succAbove = ∑ q : Fin (m + 1) × Equiv.Perm (Fin m), F (q.1.succAbove ∘ q.2)`. Rewrite using `[Fintype.sum_prod_type, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Simplify using `only [hperm, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]`. Rewrite using `[Nat.cast_smul_eq_nsmul ℂ]`.

Rewrite using `[hR]`. Use `symm`. Use `Finset.sum_bij_ne_zero (fun q _ _ => q.1.succAbove ∘ q.2) (fun _ _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ _ => rfl)` and prove the remaining obligations. Introduce and unpack `⟨c, σ⟩ _ _ ⟨c', σ'⟩ _ _ h`. Establish `hc : c = c'`.

Establish `hr : Set.range (c.succAbove ∘ σ) = Set.range (c'.succAbove ∘ σ')` using `by rw [h]`. Rewrite `hr` using `[Set.range_comp, Set.range_comp, Equiv.range_eq_univ, Equiv.range_eq_univ, Set.image_univ, Set.image_univ, Fin.range_succAbove, Fin.range_succAbove]`. Simplify using `using hr`. Substitute `hc` using the available equality. Establish `hs : σ = σ'`.

Use extensionality with `j`. Use `congrFun h j` as an intermediate fact. Simplify using `only [Function.comp_apply] at this`. Rewrite using `[Fin.succAbove_right_inj.mp this]`. Rewrite using `[hs]`.

Introduce `ρ _ hρ`. Establish `hi : Function.Injective ρ`. Assume the negation of the conclusion as `hni`. Conclude with `hρ (hinj ρ hni)`. Establish `hns : ¬ Function.Surjective ρ`.

Introduce `hs`. Use `Fintype.card_le_of_surjective ρ hs` as an intermediate fact. Simplify using `at this`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c, ∀ j, ρ j ≠ c := by`. Assume the negation of the conclusion as `hcon`.

Use `push Not at hcon`. Conclude with `hns fun c => by obtain ⟨j, hj⟩ := hcon c; exact ⟨j, hj⟩`. Establish `ht : ∀ j, ∃ t : Fin m, c.succAbove t = ρ j` using `fun j => Fin.exists_succAbove_eq (hc j)`. Use `choose t ht using ht`. Establish `tinj : Function.Injective t`.

Introduce `i j hij`. Apply `hi` to reduce the goal to its premises. Rewrite using `[← ht i, ← ht j, hij]`. Establish `tbij : Function.Bijective t` using `Finite.injective_iff_bijective.mp tinj`. Use `⟨(c, Equiv.ofBijective t tbij), Finset.mem_univ _, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [Function.comp_def, Equiv.ofBijective_apply, ht]`. Conclude with `hρ`. Use function extensionality and compare the values at `j`. Simplify using `[ht]`.
-/
theorem sum_symm_inj {X : Type*} [AddCommGroup X] [Module ℂ X] {m : ℕ} (F : (Fin m → Fin (m + 1)) → X)
    (hperm : ∀ ρ (σ : Equiv.Perm (Fin m)), F (ρ ∘ σ) = F ρ)
    (hinj : ∀ ρ, ¬ Function.Injective ρ → F ρ = 0) :
    ∑ ρ : Fin m → Fin (m + 1), F ρ = ((m.factorial : ℕ) : ℂ) • ∑ c : Fin (m + 1), F c.succAbove := by
  have hR : ((m.factorial : ℕ) : ℂ) • ∑ c : Fin (m + 1), F c.succAbove =
      ∑ q : Fin (m + 1) × Equiv.Perm (Fin m), F (q.1.succAbove ∘ q.2) := by
    rw [Fintype.sum_prod_type, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [hperm, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    rw [Nat.cast_smul_eq_nsmul ℂ]
  rw [hR]
  symm
  refine Finset.sum_bij_ne_zero (fun q _ _ => q.1.succAbove ∘ q.2) (fun _ _ _ => Finset.mem_univ _)
    ?_ ?_ (fun _ _ _ => rfl)
  · rintro ⟨c, σ⟩ _ _ ⟨c', σ'⟩ _ _ h
    have hc : c = c' := by
      have hr : Set.range (c.succAbove ∘ σ) = Set.range (c'.succAbove ∘ σ') := by rw [h]
      rw [Set.range_comp, Set.range_comp, Equiv.range_eq_univ, Equiv.range_eq_univ, Set.image_univ,
        Set.image_univ, Fin.range_succAbove, Fin.range_succAbove] at hr
      simpa using hr
    subst hc
    have hs : σ = σ' := by
      ext j
      have := congrFun h j
      simp only [Function.comp_apply] at this
      rw [Fin.succAbove_right_inj.mp this]
    rw [hs]
  · intro ρ _ hρ
    have hi : Function.Injective ρ := by
      by_contra hni; exact hρ (hinj ρ hni)
    have hns : ¬ Function.Surjective ρ := by
      intro hs
      have := Fintype.card_le_of_surjective ρ hs
      simp at this
    obtain ⟨c, hc⟩ : ∃ c, ∀ j, ρ j ≠ c := by
      by_contra hcon
      push Not at hcon
      exact hns fun c => by obtain ⟨j, hj⟩ := hcon c; exact ⟨j, hj⟩
    have ht : ∀ j, ∃ t : Fin m, c.succAbove t = ρ j := fun j => Fin.exists_succAbove_eq (hc j)
    choose t ht using ht
    have tinj : Function.Injective t := by
      intro i j hij
      apply hi
      rw [← ht i, ← ht j, hij]
    have tbij : Function.Bijective t := Finite.injective_iff_bijective.mp tinj
    refine ⟨(c, Equiv.ofBijective t tbij), Finset.mem_univ _, ?_, ?_⟩
    · simp only [Function.comp_def, Equiv.ofBijective_apply, ht]
      exact hρ
    · funext j
      simp [ht]

end Alg

end ReciprocityTheory.ChartRestriction.DS.Lap.EvalC
