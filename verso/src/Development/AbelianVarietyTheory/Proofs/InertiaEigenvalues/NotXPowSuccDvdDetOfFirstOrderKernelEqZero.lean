import Mathlib
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Take `⟨L, L', D, h⟩` from `Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal A`. Conclude with `⟨_, _, D, Matrix.TransvectionStruct.det_toMatrix_prod L, Matrix.TransvectionStruct.det_toMatrix_prod L', h⟩`.
-/
theorem exists_det_one_mul_mul_eq_diagonal {K : Type} [Field K] {a : ℕ}
    (A : Matrix (Fin a) (Fin a) K) :
    ∃ (P Q : Matrix (Fin a) (Fin a) K) (D : Fin a → K),
      P.det = 1 ∧ Q.det = 1 ∧ P * A * Q = Matrix.diagonal D := by
  obtain ⟨L, L', D, h⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal A
  exact ⟨_, _, D, Matrix.TransvectionStruct.det_toMatrix_prod L,
    Matrix.TransvectionStruct.det_toMatrix_prod L', h⟩

/- English proof (translation)
Introduce `K _ a m Ψ hker hm hdvd`. Use `set A := Ψ.map fun p => p.coeff 0 with hA`. Use `set B := Ψ.map fun p => p.coeff 1 with hB`. Establish `hker' : ∀ x0 x1 : Fin a → K, A.mulVec x0 = 0 → B.mulVec x0 + A.mulVec x1 = 0 → x0 = 0`. Introduce `x0 x1 h0 h1`.

Assume the negation of the conclusion as `hne`. Use `hker (fun _ => x0) (fun _ => x1) (fun _ => ⟨h0, h1⟩) ?_` and prove the remaining obligations. Conclude with `(linearIndependent_unique_iff (v := fun _ : Fin 1 => x0)).2 hne`. Take `⟨P, Q, D, hP, hQ, hD⟩` from `exists_det_one_mul_mul_eq_diagonal A`. Establish `hPu : IsUnit P.det` using `hP ▸ isUnit_one`.

Establish `hQu : IsUnit Q.det` using `hQ ▸ isUnit_one`. Establish `hPinj : ∀ v : Fin a → K, P.mulVec v = 0 → v = 0` using `fun v hv => Matrix.eq_zero_of_mulVec_eq_zero hPu.ne_zero hv`. Establish `hQinj : ∀ v : Fin a → K, Q.mulVec v = 0 → v = 0` using `fun v hv => Matrix.eq_zero_of_mulVec_eq_zero hQu.ne_zero hv`. Establish `hcard : (Finset.univ.filter fun i => D i = 0).card ≤ m`. Establish `h1 : A.rank = Fintype.card {i // D i ≠ 0}`.

Rewrite using `[← Matrix.rank_diagonal, ← hD, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hQu, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hPu]`. Establish `h2` using `LinearMap.finrank_range_add_finrank_ker A.mulVecLin`. Establish `h3 : Fintype.card {i // D i ≠ 0} = a - Fintype.card {i // D i = 0}`. Rewrite using `[Fintype.card_subtype_compl]`. Simplify using the standard rewrite rules.

Establish `h4 : Fintype.card {i // D i = 0} = (Finset.univ.filter fun i => D i = 0).card` using `Fintype.card_subtype _`. Establish `h5 : Fintype.card {i // D i = 0} ≤ a`. Simplify using `using Fintype.card_subtype_le (fun i => D i = 0)`. Rewrite `h1` using `[Matrix.rank]`. Simplify using `only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h2`.

Use linear arithmetic over natural numbers and integers. Establish `hAQ : ∀ v : Fin a → K, P.mulVec (A.mulVec (Q.mulVec v)) = fun i => D i * v i`. Introduce `v`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hD]`. Use extensionality with `i`.

Rewrite using `[Matrix.mulVec_diagonal]`. Establish `hcol : ∀ i j, D j = 0 → (A * Q) i j = 0`. Introduce `i j hj`. Establish `h1 : A.mulVec (Q.mulVec (Pi.single j 1)) = 0`. Apply `hPinj` to reduce the goal to its premises.

Rewrite using `[hAQ]`. Use extensionality with `k`. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Simplify using `[hj]`.

Simplify using `[hk]`. Rewrite `h1` using `[Matrix.mulVec_mulVec, Matrix.mulVec_single_one]`. Conclude with `congrFun h1 i`. Use `set Θ : Matrix (Fin a) (Fin a) K[X] := Ψ * Q.map C with hΘ`. Establish `hΘ0 : ∀ i j, (Θ i j).coeff 0 = (A * Q) i j`.

Introduce `i j`. Simplify using `[hΘ, hA, Matrix.mul_apply, Polynomial.finset_sum_coeff]`. Establish `hΘ1 : ∀ i j, (Θ i j).coeff 1 = (B * Q) i j`. Introduce `i j`. Simplify using `[hΘ, hB, Matrix.mul_apply, Polynomial.finset_sum_coeff]`.

Use `set Θ' : Matrix (Fin a) (Fin a) K[X] := Matrix.of fun i j => if D j = 0 then (Θ i j).divX else Θ i j with hΘ'`. Establish `hfac : Θ = Θ' * Matrix.diagonal fun j => if D j = 0 then (X : K[X]) else 1` using `by ext1 i j`. Rewrite using `[Matrix.mul_diagonal]`. Distinguish the cases in `hj : D j = 0`. Use `Polynomial.divX_mul_X_add (Θ i j)` as an intermediate fact.

Rewrite `this` using `[hΘ0, hcol i j hj]`. Simplify `this.symm` using `[hΘ', hj]`. Simplify using `[hΘ', hj]`. Establish `hdetΘ : Θ.det = Ψ.det`. Establish `: (Q.map C).det = (1 : K[X])`.

Use `RingHom.map_det (C : K →+* K[X]) Q` as an intermediate fact. Rewrite `this` using `[hQ, map_one]`. Conclude with `this.symm`. Rewrite using `[hΘ, Matrix.det_mul, this, mul_one]`. Establish `hdet : Ψ.det = Θ'.det * X ^ (Finset.univ.filter fun i => D i = 0).card`.

Rewrite using `[← hdetΘ]`. Use `conv_lhs => rw [hfac]`. Rewrite using `[Matrix.det_mul, Matrix.det_diagonal, Finset.prod_ite]`. Simplify using the standard rewrite rules. Use `set T : Matrix (Fin a) (Fin a) K := Θ'.map fun p => p.coeff 0 with hT`.

Establish `hTinj : ∀ y : Fin a → K, T.mulVec y = 0 → y = 0`. Introduce `y hy`. Use `set y0 : Fin a → K := fun j => if D j = 0 then y j else 0 with hy0`. Use `set y1 : Fin a → K := fun j => if D j = 0 then 0 else y j with hy1`. Establish `e0 : A.mulVec (Q.mulVec y0) = 0`.

Apply `hPinj` to reduce the goal to its premises. Rewrite using `[hAQ]`. Use extensionality with `k`. Apply the tactic sequence `by_cases hk : D k = 0 <;> simp [hy0, hk]`. Establish `e1 : B.mulVec (Q.mulVec y0) + A.mulVec (Q.mulVec y1) = 0`.

Rewrite using `[← hy, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`. Use extensionality with `i`. Simplify using `only [Pi.add_apply, Matrix.mulVec, dotProduct, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj : D j = 0`.

Simplify using `[hT, hΘ', hy0, hy1, hj, Polynomial.coeff_divX, hΘ1]`. Simplify using `[hT, hΘ', hy0, hy1, hj, hΘ0]`. Establish `z0 : y0 = 0` using `hQinj _ (hker' _ _ e0 e1)`. Rewrite `e1` using `[z0, Matrix.mulVec_zero, Matrix.mulVec_zero, zero_add]`. Establish `z1` using `hAQ y1`.

Rewrite `z1` using `[e1, Matrix.mulVec_zero]`. Use extensionality with `k`. Distinguish the cases in `hk : D k = 0`. Simplify `congrFun z0 k` using `[hy0, hk]`. Simplify `(congrFun z1 k).symm` using `[hy1, hk]`.

Establish `hTdet : T.det ≠ 0`. Introduce `h`. Take `⟨v, hv, hv0⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h`. Conclude with `hv (hTinj v hv0)`. Apply `hTdet` to reduce the goal to its premises.

Establish `hc : T.det = Θ'.det.coeff 0`. Use `RingHom.map_det (Polynomial.constantCoeff : K[X] →+* K) Θ'` as an intermediate fact. Conclude with `this.symm`. Rewrite using `[hc, ← Polynomial.X_dvd_iff]`. Use `set ν := (Finset.univ.filter fun i => D i = 0).card`.

Establish `h1 : (X : K[X]) * X ^ ν ∣ Θ'.det * X ^ ν`. Rewrite using `[← hdet, ← pow_succ']`. Conclude with `(pow_dvd_pow _ (by omega)).trans hdvd`. Conclude with `(mul_dvd_mul_iff_right (pow_ne_zero _ Polynomial.X_ne_zero)).1 h1`.
-/
theorem not_X_pow_succ_dvd_det_of_first_order_kernel_eq_zero :
    ∀ (K : Type) [Field K] (a m : ℕ) (Ψ : Matrix (Fin a) (Fin a) (Polynomial K)), (∀ x0 x1 : Fin (0 + 1) → Fin a → K, (∀ j, (Ψ.map fun p => p.coeff 0).mulVec (x0 j) = 0 ∧ (Ψ.map fun p => p.coeff 1).mulVec (x0 j) + (Ψ.map fun p => p.coeff 0).mulVec (x1 j) = 0) → ¬ LinearIndependent K x0) → Module.finrank K (LinearMap.ker (Ψ.map fun p => p.coeff 0).mulVecLin) ≤ m → ¬ (Polynomial.X : Polynomial K) ^ (m + 1) ∣ Ψ.det := by
  classical
  intro K _ a m Ψ hker hm hdvd
  set A := Ψ.map fun p => p.coeff 0 with hA
  set B := Ψ.map fun p => p.coeff 1 with hB
  have hker' : ∀ x0 x1 : Fin a → K, A.mulVec x0 = 0 → B.mulVec x0 + A.mulVec x1 = 0 → x0 = 0 := by
    intro x0 x1 h0 h1
    by_contra hne
    refine hker (fun _ => x0) (fun _ => x1) (fun _ => ⟨h0, h1⟩) ?_
    exact (linearIndependent_unique_iff (v := fun _ : Fin 1 => x0)).2 hne
  obtain ⟨P, Q, D, hP, hQ, hD⟩ := exists_det_one_mul_mul_eq_diagonal A
  have hPu : IsUnit P.det := hP ▸ isUnit_one
  have hQu : IsUnit Q.det := hQ ▸ isUnit_one
  have hPinj : ∀ v : Fin a → K, P.mulVec v = 0 → v = 0 := fun v hv =>
    Matrix.eq_zero_of_mulVec_eq_zero hPu.ne_zero hv
  have hQinj : ∀ v : Fin a → K, Q.mulVec v = 0 → v = 0 := fun v hv =>
    Matrix.eq_zero_of_mulVec_eq_zero hQu.ne_zero hv

  have hcard : (Finset.univ.filter fun i => D i = 0).card ≤ m := by
    have h1 : A.rank = Fintype.card {i // D i ≠ 0} := by
      rw [← Matrix.rank_diagonal, ← hD, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hQu,
        Matrix.rank_mul_eq_right_of_isUnit_det _ _ hPu]
    have h2 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    have h3 : Fintype.card {i // D i ≠ 0} = a - Fintype.card {i // D i = 0} := by
      rw [Fintype.card_subtype_compl]; simp
    have h4 : Fintype.card {i // D i = 0} = (Finset.univ.filter fun i => D i = 0).card :=
      Fintype.card_subtype _
    have h5 : Fintype.card {i // D i = 0} ≤ a := by
      simpa using Fintype.card_subtype_le (fun i => D i = 0)
    rw [Matrix.rank] at h1
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h2
    omega
  have hAQ : ∀ v : Fin a → K, P.mulVec (A.mulVec (Q.mulVec v)) = fun i => D i * v i := by
    intro v
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hD]
    ext i
    rw [Matrix.mulVec_diagonal]
  have hcol : ∀ i j, D j = 0 → (A * Q) i j = 0 := by
    intro i j hj
    have h1 : A.mulVec (Q.mulVec (Pi.single j 1)) = 0 := by
      apply hPinj
      rw [hAQ]
      ext k
      by_cases hk : k = j
      · subst hk; simp [hj]
      · simp [hk]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h1
    exact congrFun h1 i
  set Θ : Matrix (Fin a) (Fin a) K[X] := Ψ * Q.map C with hΘ
  have hΘ0 : ∀ i j, (Θ i j).coeff 0 = (A * Q) i j := by
    intro i j
    simp [hΘ, hA, Matrix.mul_apply, Polynomial.finset_sum_coeff]
  have hΘ1 : ∀ i j, (Θ i j).coeff 1 = (B * Q) i j := by
    intro i j
    simp [hΘ, hB, Matrix.mul_apply, Polynomial.finset_sum_coeff]
  set Θ' : Matrix (Fin a) (Fin a) K[X] :=
    Matrix.of fun i j => if D j = 0 then (Θ i j).divX else Θ i j with hΘ'
  have hfac : Θ = Θ' * Matrix.diagonal fun j => if D j = 0 then (X : K[X]) else 1 := by
    ext1 i j
    rw [Matrix.mul_diagonal]
    by_cases hj : D j = 0
    · have := Polynomial.divX_mul_X_add (Θ i j)
      rw [hΘ0, hcol i j hj] at this
      simpa [hΘ', hj] using this.symm
    · simp [hΘ', hj]
  have hdetΘ : Θ.det = Ψ.det := by
    have : (Q.map C).det = (1 : K[X]) := by
      have := RingHom.map_det (C : K →+* K[X]) Q
      rw [hQ, map_one] at this
      exact this.symm
    rw [hΘ, Matrix.det_mul, this, mul_one]
  have hdet : Ψ.det = Θ'.det * X ^ (Finset.univ.filter fun i => D i = 0).card := by
    rw [← hdetΘ]
    conv_lhs => rw [hfac]
    rw [Matrix.det_mul, Matrix.det_diagonal, Finset.prod_ite]
    simp
  set T : Matrix (Fin a) (Fin a) K := Θ'.map fun p => p.coeff 0 with hT
  have hTinj : ∀ y : Fin a → K, T.mulVec y = 0 → y = 0 := by
    intro y hy
    set y0 : Fin a → K := fun j => if D j = 0 then y j else 0 with hy0
    set y1 : Fin a → K := fun j => if D j = 0 then 0 else y j with hy1
    have e0 : A.mulVec (Q.mulVec y0) = 0 := by
      apply hPinj
      rw [hAQ]
      ext k
      by_cases hk : D k = 0 <;> simp [hy0, hk]
    have e1 : B.mulVec (Q.mulVec y0) + A.mulVec (Q.mulVec y1) = 0 := by
      rw [← hy, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      ext i
      simp only [Pi.add_apply, Matrix.mulVec, dotProduct, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : D j = 0
      · simp [hT, hΘ', hy0, hy1, hj, Polynomial.coeff_divX, hΘ1]
      · simp [hT, hΘ', hy0, hy1, hj, hΘ0]
    have z0 : y0 = 0 := hQinj _ (hker' _ _ e0 e1)
    rw [z0, Matrix.mulVec_zero, Matrix.mulVec_zero, zero_add] at e1
    have z1 := hAQ y1
    rw [e1, Matrix.mulVec_zero] at z1
    ext k
    by_cases hk : D k = 0
    · simpa [hy0, hk] using congrFun z0 k
    · simpa [hy1, hk] using (congrFun z1 k).symm
  have hTdet : T.det ≠ 0 := by
    intro h
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    exact hv (hTinj v hv0)
  apply hTdet
  have hc : T.det = Θ'.det.coeff 0 := by
    have := RingHom.map_det (Polynomial.constantCoeff : K[X] →+* K) Θ'
    exact this.symm
  rw [hc, ← Polynomial.X_dvd_iff]
  set ν := (Finset.univ.filter fun i => D i = 0).card
  have h1 : (X : K[X]) * X ^ ν ∣ Θ'.det * X ^ ν := by
    rw [← hdet, ← pow_succ']
    exact (pow_dvd_pow _ (by omega)).trans hdvd
  exact (mul_dvd_mul_iff_right (pow_ne_zero _ Polynomial.X_ne_zero)).1 h1

end GlobalTheory
