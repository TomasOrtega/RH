import Mathlib

open MvPolynomial

namespace GlobalTheory.RowDet

/- English proof (translation)
Rewrite using `[Matrix.det_apply']`. Conclude with `S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.prod_mem fun i _ => h _ _)`.
-/
theorem det_mem_subalgebra {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {m : Type*} [Fintype m] [DecidableEq m] (S : Subalgebra R A) (M : Matrix m m A)
    (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply']
  exact S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.prod_mem fun i _ => h _ _)

/- English proof (translation)
Establish `: M.det ∈ supported R ({a}ᶜ : Set σ)`. Use `det_mem_subalgebra _ _ fun i j => ?_` and prove the remaining obligations. Rewrite using `[mem_supported]`. Introduce `b hb hba`. Rewrite `hba` using `[Set.mem_singleton_iff]`.

Conclude with `h i j (hba ▸ hb)`. Rewrite `this` using `[mem_supported]`. Introduce `ha`. Conclude with `this ha rfl`.
-/
theorem notMem_vars_det {R σ : Type*} [CommRing R] {m : Type*} [Fintype m] [DecidableEq m]
    (a : σ) (M : Matrix m m (MvPolynomial σ R)) (h : ∀ i j, a ∉ (M i j).vars) :
    a ∉ M.det.vars := by
  have : M.det ∈ supported R ({a}ᶜ : Set σ) := by
    refine det_mem_subalgebra _ _ fun i j => ?_
    rw [mem_supported]
    intro b hb hba
    rw [Set.mem_singleton_iff] at hba
    exact h i j (hba ▸ hb)
  rw [mem_supported] at this
  intro ha
  exact this ha rfl

/- English proof (translation)
Rewrite using `[Matrix.det_succ_row _ (Fin.last n), Finset.sum_eq_single (Fin.last n)]`. Establish `: (-1 : A) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ)) = 1`. Rewrite using `[← two_mul, pow_mul]`. Simplify using the standard rewrite rules. Rewrite using `[this, Matrix.updateRow_self, Pi.single_eq_same, one_mul, one_mul, Fin.succAbove_last]`.

Use `congr 1`. Use extensionality with `i j`. Simplify using `[Matrix.updateRow_ne (Fin.castSucc_lt_last i).ne]`. Introduce `j _ hj`. Simplify using `[Pi.single_eq_of_ne hj]`.

Simplify using the standard rewrite rules.
-/
theorem det_updateRow_single {A : Type*} [CommRing A] {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) A) :
    (M.updateRow (Fin.last n) (Pi.single (Fin.last n) 1)).det =
      (M.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row _ (Fin.last n), Finset.sum_eq_single (Fin.last n)]
  · have : (-1 : A) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ)) = 1 := by
      rw [← two_mul, pow_mul]; simp
    rw [this, Matrix.updateRow_self, Pi.single_eq_same, one_mul, one_mul, Fin.succAbove_last]
    congr 1
    ext i j
    simp [Matrix.updateRow_ne (Fin.castSucc_lt_last i).ne]
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

/- English proof (translation)
Introduce `h`. Set `w : Matrix (Fin (n + 2)) (Fin (n + 2)) R` to `(1 : Matrix (Fin (n + 2)) (Fin (n + 2)) R).submatrix (Equiv.swap 0 (Fin.last (n + 1))) id`. Set `v : σ → R` to `Function.extend e (fun p => w p.1 p.2) 0`. Establish `hv : ∀ i k, v (e (i, k)) = w i k` using `fun i k => he.extend_apply _ _ _`. Establish `h2` using `map_dvd (eval v) h`.

Rewrite `h2` using `[RingHom.map_det, RingHom.map_det]`. Establish `e1 : (eval v).mapMatrix (Matrix.of fun i k : Fin (n + 2) => (X (e (i, k)) : MvPolynomial σ R)) = w`. Use extensionality with `i k`. Simplify using `[hv]`. Establish `e2 : ((eval v).mapMatrix ((Matrix.of fun i k : Fin (n + 2) => (X (e (i, k)) : MvPolynomial σ R)).submatrix Fin.castSucc Fin.castSucc)).det = 0`.

Use `Matrix.det_eq_zero_of_row_eq_zero 0 fun j => ?_` and prove the remaining obligations. Simplify using `[hv, w, Matrix.one_apply, (Fin.castSucc_lt_last j).ne']`. Rewrite `h2` using `[e1, e2, zero_dvd_iff]`. Establish `hu : IsUnit w.det`. Rewrite using `[Matrix.det_permute, Matrix.det_one, mul_one]`.

Conclude with `(Units.isUnit _).map (Int.castRingHom R)`. Conclude with `hu.ne_zero h2`.
-/
theorem minor_not_dvd {R σ : Type*} [CommRing R] [Nontrivial R] {n : ℕ}
    (e : Fin (n + 2) × Fin (n + 2) → σ) (he : Function.Injective e) :
    ¬ ((Matrix.of fun i k : Fin (n + 2) => (X (e (i, k)) : MvPolynomial σ R)).submatrix
        Fin.castSucc Fin.castSucc).det ∣
      (Matrix.of fun i k : Fin (n + 2) => (X (e (i, k)) : MvPolynomial σ R)).det := by
  classical
  intro h
  let w : Matrix (Fin (n + 2)) (Fin (n + 2)) R :=
    (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) R).submatrix (Equiv.swap 0 (Fin.last (n + 1))) id
  let v : σ → R := Function.extend e (fun p => w p.1 p.2) 0
  have hv : ∀ i k, v (e (i, k)) = w i k := fun i k => he.extend_apply _ _ _
  have h2 := map_dvd (eval v) h
  rw [RingHom.map_det, RingHom.map_det] at h2
  have e1 : (eval v).mapMatrix
      (Matrix.of fun i k : Fin (n + 2) => (X (e (i, k)) : MvPolynomial σ R)) = w := by
    ext i k; simp [hv]
  have e2 : ((eval v).mapMatrix ((Matrix.of fun i k : Fin (n + 2) =>
      (X (e (i, k)) : MvPolynomial σ R)).submatrix Fin.castSucc Fin.castSucc)).det = 0 := by
    refine Matrix.det_eq_zero_of_row_eq_zero 0 fun j => ?_
    simp [hv, w, Matrix.one_apply, (Fin.castSucc_lt_last j).ne']
  rw [e1, e2, zero_dvd_iff] at h2
  have hu : IsUnit w.det := by
    rw [Matrix.det_permute, Matrix.det_one, mul_one]
    exact (Units.isUnit _).map (Int.castRingHom R)
  exact hu.ne_zero h2

/- English proof (translation)
Use `set A := (Matrix.of fun i k : Fin (n + 1) => (X (e (i, k)) : MvPolynomial σ R)) with hA`. Set `r : Fin (n + 1) → MvPolynomial σ R` to `fun k => if k = Fin.last n then 0 else A (Fin.last n) k`. Establish `hD : A.det = (A.submatrix Fin.castSucc Fin.castSucc).det * X (e (Fin.last n, Fin.last n)) + (A.updateRow (Fin.last n) r).det`. Rewrite using `[← det_updateRow_single, mul_comm, ← Matrix.det_updateRow_smul, ← Matrix.det_updateRow_add]`. Use `congr 1`.

Rewrite using `[eq_comm]`. Use `Matrix.updateRow_eq_self A (Fin.last n)` and compare the differences between its conclusion and the goal. Use `ext1 k`. Distinguish the cases in `hk : k = Fin.last n`. Substitute `hk` using the available equality.

Simplify using `[r, A]`. Simplify using `[r, hk]`. Rewrite `h`, the goal using `[hD]`. Use `irreducible_mul_X_add _ _ _ h0 ?_ ?_ ?_` and prove the remaining obligations. Use `notMem_vars_det _ _ fun i j => ?_` and prove the remaining obligations.

Simplify using `[A, vars_X, he.eq_iff, (Fin.castSucc_lt_last j).ne']`. Use `notMem_vars_det _ _ fun i j => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i = Fin.last n`. Substitute `hi` using the available equality. Distinguish the cases in `hj : j = Fin.last n`.

Simplify using `[r, hj]`. Simplify using `[r, hj, A, vars_X, he.eq_iff, Ne.symm hj]`. Simplify using `[Matrix.updateRow_ne hi, A, vars_X, he.eq_iff, Ne.symm hi]`. Introduce `c hc1 hc2`. Conclude with `h hc1 (dvd_add (hc1.mul_right _) hc2)`.
-/
theorem irreducible_det_of_isRelPrime {R σ : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (e : Fin (n + 1) × Fin (n + 1) → σ) (he : Function.Injective e)
    (h0 : ((Matrix.of fun i k : Fin (n + 1) => (X (e (i, k)) : MvPolynomial σ R)).submatrix
        Fin.castSucc Fin.castSucc).det ≠ 0)
    (h : IsRelPrime ((Matrix.of fun i k : Fin (n + 1) =>
        (X (e (i, k)) : MvPolynomial σ R)).submatrix Fin.castSucc Fin.castSucc).det
      (Matrix.of fun i k : Fin (n + 1) => (X (e (i, k)) : MvPolynomial σ R)).det) :
    Irreducible (Matrix.of fun i k : Fin (n + 1) => (X (e (i, k)) : MvPolynomial σ R)).det := by
  classical
  set A := (Matrix.of fun i k : Fin (n + 1) => (X (e (i, k)) : MvPolynomial σ R)) with hA
  let r : Fin (n + 1) → MvPolynomial σ R := fun k => if k = Fin.last n then 0 else A (Fin.last n) k
  have hD : A.det = (A.submatrix Fin.castSucc Fin.castSucc).det * X (e (Fin.last n, Fin.last n))
      + (A.updateRow (Fin.last n) r).det := by
    rw [← det_updateRow_single, mul_comm, ← Matrix.det_updateRow_smul,
      ← Matrix.det_updateRow_add]
    congr 1
    rw [eq_comm]
    convert Matrix.updateRow_eq_self A (Fin.last n)
    ext1 k
    by_cases hk : k = Fin.last n
    · subst hk; simp [r, A]
    · simp [r, hk]
  rw [hD] at h ⊢
  refine irreducible_mul_X_add _ _ _ h0 ?_ ?_ ?_
  · refine notMem_vars_det _ _ fun i j => ?_
    simp [A, vars_X, he.eq_iff, (Fin.castSucc_lt_last j).ne']
  · refine notMem_vars_det _ _ fun i j => ?_
    by_cases hi : i = Fin.last n
    · subst hi
      by_cases hj : j = Fin.last n
      · simp [r, hj]
      · simp [r, hj, A, vars_X, he.eq_iff, Ne.symm hj]
    · simp [Matrix.updateRow_ne hi, A, vars_X, he.eq_iff, Ne.symm hi]
  · intro c hc1 hc2
    exact h hc1 (dvd_add (hc1.mul_right _) hc2)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `e he`. Use `irreducible_det_of_isRelPrime e he ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.

Rewrite using `[Matrix.det_isEmpty]`. Conclude with `isRelPrime_one_left`. Consider the case `succ n ih`. Introduce `e he`. Establish `h` using `ih (fun p => e (p.1.castSucc, p.2.castSucc)) (fun p q hpq => by`.

Use `he hpq` as an intermediate fact. Simplify using `only [Prod.mk.injEq, Fin.castSucc_inj] at this`. Conclude with `Prod.ext this.1 this.2)`. Conclude with `irreducible_det_of_isRelPrime e he h.ne_zero (h.isRelPrime_iff_not_dvd.2 (minor_not_dvd e he))`.
-/
theorem irreducible_det {R σ : Type*} [CommRing R] [IsDomain R] (n : ℕ) :
    ∀ (e : Fin (n + 1) × Fin (n + 1) → σ), Function.Injective e →
    Irreducible (Matrix.of fun i k : Fin (n + 1) => (X (e (i, k)) : MvPolynomial σ R)).det := by
  induction n with
  | zero =>
    intro e he
    refine irreducible_det_of_isRelPrime e he ?_ ?_
    · simp
    · rw [Matrix.det_isEmpty]; exact isRelPrime_one_left
  | succ n ih =>
    intro e he
    have h := ih (fun p => e (p.1.castSucc, p.2.castSucc)) (fun p q hpq => by
      have := he hpq
      simp only [Prod.mk.injEq, Fin.castSucc_inj] at this
      exact Prod.ext this.1 this.2)
    exact irreducible_det_of_isRelPrime e he h.ne_zero
      (h.isRelPrime_iff_not_dvd.2 (minor_not_dvd e he))

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero => rw [Matrix.det_isEmpty]`. Conclude with `⟨one_ne_zero, isRelPrime_one_left⟩`. Consider the case `succ n`. Establish `h` using `irreducible_det (R := R) n (fun p => e (p.1.castSucc, p.2.castSucc)) (fun p q hpq => by`.

Use `he hpq` as an intermediate fact. Simplify using `only [Prod.mk.injEq, Fin.castSucc_inj] at this`. Conclude with `Prod.ext this.1 this.2)`. Conclude with `⟨h.ne_zero, h.isRelPrime_iff_not_dvd.2 (minor_not_dvd e he)⟩`.
-/
theorem minor_isRelPrime {R σ : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (e : Fin (n + 1) × Fin (n + 1) → σ) (he : Function.Injective e) :
    ((Matrix.of fun i k : Fin (n + 1) => (X (e (i, k)) : MvPolynomial σ R)).submatrix
        Fin.castSucc Fin.castSucc).det ≠ 0 ∧
    IsRelPrime ((Matrix.of fun i k : Fin (n + 1) =>
        (X (e (i, k)) : MvPolynomial σ R)).submatrix Fin.castSucc Fin.castSucc).det
      (Matrix.of fun i k : Fin (n + 1) => (X (e (i, k)) : MvPolynomial σ R)).det := by
  cases n with
  | zero => rw [Matrix.det_isEmpty]; exact ⟨one_ne_zero, isRelPrime_one_left⟩
  | succ n =>
    have h := irreducible_det (R := R) n (fun p => e (p.1.castSucc, p.2.castSucc))
      (fun p q hpq => by
        have := he hpq
        simp only [Prod.mk.injEq, Fin.castSucc_inj] at this
        exact Prod.ext this.1 this.2)
    exact ⟨h.ne_zero, h.isRelPrime_iff_not_dvd.2 (minor_not_dvd e he)⟩

end GlobalTheory.RowDet
