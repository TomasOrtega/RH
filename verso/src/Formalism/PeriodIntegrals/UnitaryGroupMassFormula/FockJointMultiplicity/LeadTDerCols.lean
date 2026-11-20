import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.PurElim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.ExistGen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.ExistWt

noncomputable section

open MvPolynomial

namespace PI.FJMX

section Gen

variable {A : Type*} [CommRing A] [Algebra ℂ A] {m k : ℕ}

/- English proof (translation)
Unfold `PI.FJM.leadT`. Use `split_ifs with hh`. Apply `deriv_det_eq_zero_rows` to reduce the goal to its premises. Introduce `i`. Break down `h (Fin.castLE hh.1 i) (by simp) with h0 | ⟨i₁, hi₁, hne, e, he⟩` into its components or cases.

Use `left`. Introduce `j`. Simplify using `only [Matrix.submatrix_apply]`. Conclude with `h0 _ (by simp)`. Use `right`.

Use `⟨⟨i₁.val, hi₁⟩, ?_, e, ?_⟩` and prove the remaining obligations. Introduce `hc`. Apply `hne` to reduce the goal to its premises. Use `ext`. Simplify using `[← hc]`.

Introduce `j`. Simplify using `only [Matrix.submatrix_apply]`. Rewrite using `[he _ (by simp)]`. Both sides reduce to the same expression. Simplify using the standard rewrite rules.
-/
theorem leadT_der_rows' (D : Derivation ℂ A A) (M : Matrix (Fin m) (Fin k) A) (t : ℕ)
    (h : ∀ i₀ : Fin m, i₀.val < t → (∀ j : Fin k, j.val < t → D (M i₀ j) = 0) ∨
      ∃ i₁ : Fin m, i₁.val < t ∧ i₁ ≠ i₀ ∧ ∃ e : A, ∀ j : Fin k, j.val < t → D (M i₀ j) = e * M i₁ j) :
    D (PI.FJM.leadT M t) = 0 := by
  unfold PI.FJM.leadT
  split_ifs with hh
  · apply deriv_det_eq_zero_rows
    intro i
    rcases h (Fin.castLE hh.1 i) (by simp) with h0 | ⟨i₁, hi₁, hne, e, he⟩
    · left
      intro j
      simp only [Matrix.submatrix_apply]
      exact h0 _ (by simp)
    · right
      refine ⟨⟨i₁.val, hi₁⟩, ?_, e, ?_⟩
      · intro hc
        apply hne
        ext
        simp [← hc]
      · intro j
        simp only [Matrix.submatrix_apply]
        rw [he _ (by simp)]
        rfl
  · simp

/- English proof (translation)
Unfold `PI.FJM.leadT`. Use `split_ifs with hh`. Apply `deriv_det_eq_zero` to reduce the goal to its premises. Introduce `j`. Break down `h (Fin.castLE hh.2 j) (by simp) with h0 | ⟨j₁, hj₁, hne, e, he⟩` into its components or cases.

Use `left`. Introduce `i`. Simplify using `only [Matrix.submatrix_apply]`. Conclude with `h0 _ (by simp)`. Use `right`.

Use `⟨⟨j₁.val, hj₁⟩, ?_, e, ?_⟩` and prove the remaining obligations. Introduce `hc`. Apply `hne` to reduce the goal to its premises. Use `ext`. Simplify using `[← hc]`.

Introduce `i`. Simplify using `only [Matrix.submatrix_apply]`. Rewrite using `[he _ (by simp)]`. Both sides reduce to the same expression. Simplify using the standard rewrite rules.
-/
theorem leadT_der_cols' (D : Derivation ℂ A A) (M : Matrix (Fin m) (Fin k) A) (t : ℕ)
    (h : ∀ j₀ : Fin k, j₀.val < t → (∀ i : Fin m, i.val < t → D (M i j₀) = 0) ∨
      ∃ j₁ : Fin k, j₁.val < t ∧ j₁ ≠ j₀ ∧ ∃ e : A, ∀ i : Fin m, i.val < t → D (M i j₀) = e * M i j₁) :
    D (PI.FJM.leadT M t) = 0 := by
  unfold PI.FJM.leadT
  split_ifs with hh
  · apply deriv_det_eq_zero
    intro j
    rcases h (Fin.castLE hh.2 j) (by simp) with h0 | ⟨j₁, hj₁, hne, e, he⟩
    · left
      intro i
      simp only [Matrix.submatrix_apply]
      exact h0 _ (by simp)
    · right
      refine ⟨⟨j₁.val, hj₁⟩, ?_, e, ?_⟩
      · intro hc
        apply hne
        ext
        simp [← hc]
      · intro i
        simp only [Matrix.submatrix_apply]
        rw [he _ (by simp)]
        rfl
  · simp

/- English proof (translation)
Unfold `PI.FJM.shapeProd`. Apply `deriv_prod_eq_zero` to reduce the goal to its premises. Introduce `t _`. Conclude with `deriv_pow_eq_zero _ _ _ (h _)`.
-/
theorem shapeProd_der' (D : Derivation ℂ A A) (M : Matrix (Fin m) (Fin k) A) (α : List ℕ)
    (h : ∀ t, D (PI.FJM.leadT M t) = 0) : D (PI.FJM.shapeProd M α) = 0 := by
  unfold PI.FJM.shapeProd
  apply deriv_prod_eq_zero
  intro t _
  exact deriv_pow_eq_zero _ _ _ (h _)

end Gen

section Block

variable {σ : Type*} {m n : ℕ}

/- English proof (translation)
Rewrite using `[← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]`. Both sides reduce to the same expression.
-/
theorem derSum_apply {ι : Type*} (t : Finset ι) (D : ι → Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (f : MvPolynomial σ ℂ) : (∑ c ∈ t, D c) f = ∑ c ∈ t, D c f := by
  rw [← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
  rfl

def rowD (ι : Fin m × Fin n → σ) (a b : Fin m) : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ) :=
  ∑ k : Fin n, (X (ι (a, k)) : MvPolynomial σ ℂ) • pderiv (ι (b, k))

def colD (ι : Fin m × Fin n → σ) (c d : Fin n) : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ) :=
  ∑ i : Fin m, (X (ι (i, c)) : MvPolynomial σ ℂ) • pderiv (ι (i, d))

/- English proof (translation)
Rewrite using `[PI.FJM.bRow, rowD, derSum_apply, LinearMap.sum_apply]`. Both sides reduce to the same expression.
-/
theorem bRow_eq_rowD (ι : Fin m × Fin n → σ) (a b : Fin m) (f : MvPolynomial σ ℂ) :
    PI.FJM.bRow ι a b f = rowD ι a b f := by
  rw [PI.FJM.bRow, rowD, derSum_apply, LinearMap.sum_apply]
  rfl

/- English proof (translation)
Rewrite using `[PI.FJM.bCol, colD, derSum_apply, LinearMap.sum_apply]`. Both sides reduce to the same expression.
-/
theorem bCol_eq_colD (ι : Fin m × Fin n → σ) (c d : Fin n) (f : MvPolynomial σ ℂ) :
    PI.FJM.bCol ι c d f = colD ι c d f := by
  rw [PI.FJM.bCol, colD, derSum_apply, LinearMap.sum_apply]
  rfl

/- English proof (translation)
Rewrite using `[rowD, derSum_apply, Finset.sum_eq_single j]`. Distinguish the cases in `h : i = b`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Establish `: ι (i, j) ≠ ι (b, j)` using `fun e => h (by have := hι e; simp at this; exact this)`.

Simplify using `[h, pderiv_X_of_ne this]`. Introduce `k _ hk`. Establish `: ι (i, j) ≠ ι (b, k)` using `fun e => hk (by have := hι e; simp at this; exact this.2.symm)`. Simplify using `[pderiv_X_of_ne this]`. Simplify using the standard rewrite rules.
-/
theorem rowD_X (ι : Fin m × Fin n → σ) (hι : Function.Injective ι) (a b i : Fin m) (j : Fin n) :
    rowD ι a b (X (ι (i, j))) = if i = b then X (ι (a, j)) else 0 := by
  classical
  rw [rowD, derSum_apply, Finset.sum_eq_single j]
  · by_cases h : i = b
    · subst h; simp
    · have : ι (i, j) ≠ ι (b, j) := fun e => h (by have := hι e; simp at this; exact this)
      simp [h, pderiv_X_of_ne this]
  · intro k _ hk
    have : ι (i, j) ≠ ι (b, k) := fun e => hk (by have := hι e; simp at this; exact this.2.symm)
    simp [pderiv_X_of_ne this]
  · simp

/- English proof (translation)
Rewrite using `[colD, derSum_apply, Finset.sum_eq_single i]`. Distinguish the cases in `h : j = d`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Establish `: ι (i, j) ≠ ι (i, d)` using `fun e => h (by have := hι e; simp at this; exact this)`.

Simplify using `[h, pderiv_X_of_ne this]`. Introduce `k _ hk`. Establish `: ι (i, j) ≠ ι (k, d)` using `fun e => hk (by have := hι e; simp at this; exact this.1.symm)`. Simplify using `[pderiv_X_of_ne this]`. Simplify using the standard rewrite rules.
-/
theorem colD_X (ι : Fin m × Fin n → σ) (hι : Function.Injective ι) (c d : Fin n) (i : Fin m) (j : Fin n) :
    colD ι c d (X (ι (i, j))) = if j = d then X (ι (i, c)) else 0 := by
  classical
  rw [colD, derSum_apply, Finset.sum_eq_single i]
  · by_cases h : j = d
    · subst h; simp
    · have : ι (i, j) ≠ ι (i, d) := fun e => h (by have := hι e; simp at this; exact this)
      simp [h, pderiv_X_of_ne this]
  · intro k _ hk
    have : ι (i, j) ≠ ι (k, d) := fun e => hk (by have := hι e; simp at this; exact this.1.symm)
    simp [pderiv_X_of_ne this]
  · simp

abbrev blkM (ι : Fin m × Fin n → σ) : Matrix (Fin m) (Fin n) (MvPolynomial σ ℂ) :=
  Matrix.of fun i k => (X (ι (i, k)) : MvPolynomial σ ℂ)

/- English proof (translation)
Use `⟨fun a b hab => ?_, fun c d hcd => ?_⟩` and prove the remaining obligations. Rewrite using `[bRow_eq_rowD]`. Apply `shapeProd_der'` to reduce the goal to its premises. Introduce `t`. Apply `leadT_der_rows'` to reduce the goal to its premises.

Introduce `i₀ hi₀`. Distinguish the cases in `hb : i₀ = b`. Use `right`. Substitute `hb` using the available equality. Use `⟨a, by omega, ne_of_lt hab, 1, fun j _ => ?_⟩` and prove the remaining obligations.

Simplify using `[blkM, rowD_X ι hι]`. Use `left`. Introduce `j _`. Simplify using `[blkM, rowD_X ι hι, hb]`. Rewrite using `[bCol_eq_colD]`.

Apply `shapeProd_der'` to reduce the goal to its premises. Introduce `t`. Apply `leadT_der_cols'` to reduce the goal to its premises. Introduce `j₀ hj₀`. Distinguish the cases in `hd : j₀ = d`.

Use `right`. Substitute `hd` using the available equality. Use `⟨c, by omega, ne_of_lt hcd, 1, fun i _ => ?_⟩` and prove the remaining obligations. Simplify using `[blkM, colD_X ι hι]`. Use `left`.

Introduce `i _`. Simplify using `[blkM, colD_X ι hι, hd]`.
-/
theorem shapeProd_hwb (ι : Fin m × Fin n → σ) (hι : Function.Injective ι) (α : List ℕ) :
    PI.FJMB.HWB ι (PI.FJM.shapeProd (blkM ι) α) := by
  refine ⟨fun a b hab => ?_, fun c d hcd => ?_⟩
  · rw [bRow_eq_rowD]
    apply shapeProd_der'
    intro t
    apply leadT_der_rows'
    intro i₀ hi₀
    by_cases hb : i₀ = b
    · right
      subst hb
      refine ⟨a, by omega, ne_of_lt hab, 1, fun j _ => ?_⟩
      simp [blkM, rowD_X ι hι]
    · left
      intro j _
      simp [blkM, rowD_X ι hι, hb]
  · rw [bCol_eq_colD]
    apply shapeProd_der'
    intro t
    apply leadT_der_cols'
    intro j₀ hj₀
    by_cases hd : j₀ = d
    · right
      subst hd
      refine ⟨c, by omega, ne_of_lt hcd, 1, fun i _ => ?_⟩
      simp [blkM, colD_X ι hι]
    · left
      intro i _
      simp [blkM, colD_X ι hι, hd]

end Block

section Diag

variable {σ : Type*} {m : ℕ}

/- English proof (translation)
Establish `e1 : ∏ i : Fin m, g i ^ (if i.val < t then 1 else 0) = ∏ i : Fin m, (if i.val < t then g i else 1)`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `i _`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[e1, ← Finset.prod_filter]`.

Establish `e2 : (Finset.univ.filter fun i : Fin m => i.val < t) = Finset.univ.map (Fin.castLEEmb h)`. Use extensionality with `x`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Conclude with `⟨⟨x.val, hx⟩, Fin.ext rfl⟩`. Introduce and unpack `⟨a, -, rfl⟩`. Simplify using the standard rewrite rules. Rewrite using `[e2, Finset.prod_map]`. Both sides reduce to the same expression.
-/
theorem prod_castLE_eq {M : Type*} [CommMonoid M] {t : ℕ} (h : t ≤ m) (g : Fin m → M) :
    ∏ i : Fin t, g (Fin.castLE h i) = ∏ i : Fin m, g i ^ (if i.val < t then 1 else 0) := by
  classical
  have e1 : ∏ i : Fin m, g i ^ (if i.val < t then 1 else 0) =
      ∏ i : Fin m, (if i.val < t then g i else 1) := by
    apply Finset.prod_congr rfl
    intro i _
    split_ifs <;> simp
  rw [e1, ← Finset.prod_filter]
  have e2 : (Finset.univ.filter fun i : Fin m => i.val < t) = Finset.univ.map (Fin.castLEEmb h) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb]
    constructor
    · intro hx
      exact ⟨⟨x.val, hx⟩, Fin.ext rfl⟩
    · rintro ⟨a, -, rfl⟩
      simp
  rw [e2, Finset.prod_map]
  rfl

/- English proof (translation)
Unfold `PI.FJM.leadT`. Rewrite using `[dif_pos ⟨ht, ht⟩, AlgHom.map_det]`. Establish `hD : (aeval (PI.FJMB.killS (PI.FJMB.offD ι))).mapMatrix ((blkM ι).submatrix (Fin.castLE ht) (Fin.castLE ht)) = Matrix.diagonal (fun i : Fin t => (X (ι (Fin.castLE ht i, Fin.castLE ht i)) : MvPolynomial σ ℂ))`. Use extensionality with `i j`. Simplify using `only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, blkM, Matrix.of_apply, aeval_X, Matrix.diagonal_apply]`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Establish `: ι (Fin.castLE ht i, Fin.castLE ht i) ∉ PI.FJMB.offD ι`. Introduce and unpack `⟨i', k', he, hne⟩`. Use `hι he` as an intermediate fact.

Simplify using `only [Prod.mk.injEq] at this`. Apply `hne` to reduce the goal to its premises. Rewrite using `[this.1, this.2]`. Simplify using `[PI.FJMB.killS, this]`. Establish `: ι (Fin.castLE ht i, Fin.castLE ht j) ∈ PI.FJMB.offD ι`.

Use `⟨Fin.castLE ht i, Fin.castLE ht j, rfl, ?_⟩` and prove the remaining obligations. Simplify using `only [Fin.coe_castLE]`. Conclude with `fun h => hij (Fin.ext h)`. Simplify using `[PI.FJMB.killS, this, hij]`. Rewrite using `[hD, Matrix.det_diagonal]`.

Conclude with `prod_castLE_eq ht (fun i => (X (ι (i, i)) : MvPolynomial σ ℂ))`.
-/
theorem leadT_diag (ι : Fin m × Fin m → σ) (hι : Function.Injective ι) (t : ℕ) (ht : t ≤ m) :
    aeval (PI.FJMB.killS (PI.FJMB.offD ι)) (PI.FJM.leadT (blkM ι) t) =
      ∏ i : Fin m, X (ι (i, i)) ^ (if i.val < t then 1 else 0) := by
  classical
  unfold PI.FJM.leadT
  rw [dif_pos ⟨ht, ht⟩, AlgHom.map_det]
  have hD : (aeval (PI.FJMB.killS (PI.FJMB.offD ι))).mapMatrix ((blkM ι).submatrix (Fin.castLE ht) (Fin.castLE ht)) =
      Matrix.diagonal (fun i : Fin t => (X (ι (Fin.castLE ht i, Fin.castLE ht i)) : MvPolynomial σ ℂ)) := by
    ext i j
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, blkM, Matrix.of_apply, aeval_X,
      Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      have : ι (Fin.castLE ht i, Fin.castLE ht i) ∉ PI.FJMB.offD ι := by
        rintro ⟨i', k', he, hne⟩
        have := hι he
        simp only [Prod.mk.injEq] at this
        apply hne
        rw [this.1, this.2]
      simp [PI.FJMB.killS, this]
    · have : ι (Fin.castLE ht i, Fin.castLE ht j) ∈ PI.FJMB.offD ι := by
        refine ⟨Fin.castLE ht i, Fin.castLE ht j, rfl, ?_⟩
        simp only [Fin.coe_castLE]
        exact fun h => hij (Fin.ext h)
      simp [PI.FJMB.killS, this, hij]
  rw [hD, Matrix.det_diagonal]
  exact prod_castLE_eq ht (fun i => (X (ι (i, i)) : MvPolynomial σ ℂ))

/- English proof (translation)
Establish `hpw : (List.ofFn α).Pairwise (· ≥ ·)`. Rewrite using `[List.pairwise_ofFn]`. Introduce `i j hij`. Conclude with `hα hij.le`. Unfold `PI.FJM.shapeProd`.

Rewrite using `[map_prod]`. Establish `e1 : ∀ t ∈ Finset.range (List.ofFn α).length, aeval (PI.FJMB.killS (PI.FJMB.offD ι)) (PI.FJM.leadT (blkM ι) (t + 1) ^ ((List.ofFn α).getD t 0 - (List.ofFn α).getD (t + 1) 0)) = ∏ i : Fin m, X (ι (i, i)) ^ ((if i.val < t + 1 then 1 else 0) * ((List.ofFn α).getD t 0 - (List.ofFn α) …`. Introduce `t ht`. Simplify using `only [List.length_ofFn, Finset.mem_range] at ht`. Rewrite using `[map_pow, leadT_diag ι hι (t + 1) (by omega), ← Finset.prod_pow]`.

Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[pow_mul]`. Rewrite using `[Finset.prod_congr rfl e1, Finset.prod_comm]`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises.

Introduce `i _`. Rewrite using `[Finset.prod_pow_eq_pow_sum]`. Use `congr 1`. Simplify using `only [List.length_ofFn]`. Use `shape_sum (List.ofFn α) hpw i.val` as an intermediate fact.

Rewrite `this` using `[List.length_ofFn]`. Simplify using `only [smul_eq_mul] at this`. Rewrite using `[show (∑ t ∈ Finset.range m, (if i.val < t + 1 then 1 else 0) * ((List.ofFn α).getD t 0 - (List.ofFn α).getD (t + 1) 0)) = ∑ t ∈ Finset.range m, ((List.ofFn α).getD t 0 - (List.ofFn α).getD (t + 1) 0) * (if i.val < t + 1 then 1 else 0) from Finset.sum_congr rfl (fun _ _ => mul_co …`. Simplify using the standard rewrite rules.
-/
theorem shapeProd_diag (ι : Fin m × Fin m → σ) (hι : Function.Injective ι) (α : Fin m → ℕ) (hα : Antitone α) :
    aeval (PI.FJMB.killS (PI.FJMB.offD ι)) (PI.FJM.shapeProd (blkM ι) (List.ofFn α)) =
      ∏ i, X (ι (i, i)) ^ α i := by
  classical
  have hpw : (List.ofFn α).Pairwise (· ≥ ·) := by
    rw [List.pairwise_ofFn]
    intro i j hij
    exact hα hij.le
  unfold PI.FJM.shapeProd
  rw [map_prod]
  have e1 : ∀ t ∈ Finset.range (List.ofFn α).length,
      aeval (PI.FJMB.killS (PI.FJMB.offD ι)) (PI.FJM.leadT (blkM ι) (t + 1) ^
        ((List.ofFn α).getD t 0 - (List.ofFn α).getD (t + 1) 0)) =
      ∏ i : Fin m, X (ι (i, i)) ^ ((if i.val < t + 1 then 1 else 0) *
        ((List.ofFn α).getD t 0 - (List.ofFn α).getD (t + 1) 0)) := by
    intro t ht
    simp only [List.length_ofFn, Finset.mem_range] at ht
    rw [map_pow, leadT_diag ι hι (t + 1) (by omega), ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    rw [pow_mul]
  rw [Finset.prod_congr rfl e1, Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  simp only [List.length_ofFn]
  have := shape_sum (List.ofFn α) hpw i.val
  rw [List.length_ofFn] at this
  simp only [smul_eq_mul] at this
  rw [show (∑ t ∈ Finset.range m, (if i.val < t + 1 then 1 else 0) *
      ((List.ofFn α).getD t 0 - (List.ofFn α).getD (t + 1) 0)) =
      ∑ t ∈ Finset.range m, ((List.ofFn α).getD t 0 - (List.ofFn α).getD (t + 1) 0) *
        (if i.val < t + 1 then 1 else 0) from Finset.sum_congr rfl (fun _ _ => mul_comm _ _), this]
  simp

end Diag

end PI.FJMX
