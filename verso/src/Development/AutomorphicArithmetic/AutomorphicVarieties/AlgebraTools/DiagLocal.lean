import Mathlib

open Polynomial Matrix IsLocalRing TensorProduct

namespace UpperTheory.V.AlgebraTools

private def DGood {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι R) : Prop :=
  ∃ P : Matrix ι ι R, IsUnit P.det ∧ (Pᵀ * H * P).IsDiag

/- English proof (translation)
Take `⟨P, hP, hD⟩` from `h`. Use `⟨Q * P, by rw [det_mul]; exact hQ.mul hP, ?_⟩` and prove the remaining obligations. Rewrite using `[transpose_mul]`. Simplify `hD` using `only [Matrix.mul_assoc]`.
-/
private theorem dgood_congr {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (H Q : Matrix ι ι R) (hQ : IsUnit Q.det) (h : DGood (Qᵀ * H * Q)) : DGood H := by
  obtain ⟨P, hP, hD⟩ := h
  refine ⟨Q * P, by rw [det_mul]; exact hQ.mul hP, ?_⟩
  rw [transpose_mul]
  simpa only [Matrix.mul_assoc] using hD

/- English proof (translation)
Take `⟨P, hP, hD⟩` from `h`. Use `⟨P.submatrix e.symm e.symm, by rw [det_submatrix_equiv_self]; exact hP, ?_⟩` and prove the remaining obligations. Establish `key : (P.submatrix e.symm e.symm)ᵀ * H * P.submatrix e.symm e.symm = (Pᵀ * H.submatrix e e * P).submatrix e.symm e.symm`. Rewrite using `[← submatrix_mul_equiv _ _ _ e.symm _, ← submatrix_mul_equiv _ _ _ e.symm _, transpose_submatrix, submatrix_submatrix]`. Simplify using the standard rewrite rules.

Rewrite using `[key]`. Conclude with `hD.submatrix e.symm.injective`.
-/
private theorem dgood_reindex {R : Type} [CommRing R] {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : κ ≃ ι)
    (H : Matrix ι ι R) (h : DGood (H.submatrix e e)) : DGood H := by
  obtain ⟨P, hP, hD⟩ := h
  refine ⟨P.submatrix e.symm e.symm, by rw [det_submatrix_equiv_self]; exact hP, ?_⟩
  have key : (P.submatrix e.symm e.symm)ᵀ * H * P.submatrix e.symm e.symm
      = (Pᵀ * H.submatrix e e * P).submatrix e.symm e.symm := by
    rw [← submatrix_mul_equiv _ _ _ e.symm _, ← submatrix_mul_equiv _ _ _ e.symm _,
      transpose_submatrix, submatrix_submatrix]
    simp
  rw [key]
  exact hD.submatrix e.symm.injective

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, IsUnit (H i j) := by`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `key : ∑ j, H i j * adjugate H j i = H.det`. Use `congrFun (congrFun (mul_adjugate H) i) i` as an intermediate fact.

Simplify `this` using `[Matrix.mul_apply]`. Establish `hm : ∑ j, H i j * adjugate H j i ∈ maximalIdeal R` using `Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (by rw [mem_maximalIdeal, mem_nonunits_iff]; exact hne j)`. Rewrite `hm` using `[key, mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `hm hd`. Distinguish the cases in `hij : j = i`.

Substitute `hij` using the available equality. Conclude with `⟨1, by simp, by simpa using hj⟩`. Establish `hji : H j i = H i j`. Use `congrFun (congrFun hs i) j` as an intermediate fact. Simplify using `using this`.

Establish `hent : ∀ c : R, ((transvection j i c)ᵀ * H * transvection j i c) i i = H i i + 2 * c * H i j + c * c * H j j`. Introduce `c`. Simplify using `[transvection, Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite, Ne.symm hij, hij, hji]`. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `hp : IsUnit (H i i + 2 * 1 * H i j + 1 * 1 * H j j)`.

Conclude with `⟨transvection j i 1, by rw [det_transvection_of_ne j i hij]; exact isUnit_one, by rw [hent]; exact hp⟩`. Use `⟨transvection j i (-1), by rw [det_transvection_of_ne j i hij]; exact isUnit_one, ?_⟩` and prove the remaining obligations. Rewrite using `[hent]`. Assume the negation of the conclusion as `hm`. Establish `hx : (H i i + 2 * 1 * H i j + 1 * 1 * H j j) - (H i i + 2 * (-1) * H i j + (-1) * (-1) * H j j) ∈ maximalIdeal R` using `Ideal.sub_mem _ ((mem_maximalIdeal _).2 hp) ((mem_maximalIdeal _).2 hm)`.

Establish `e4 : (H i i + 2 * 1 * H i j + 1 * 1 * H j j) - (H i i + 2 * (-1) * H i j + (-1) * (-1) * H j j) = 2 * 2 * H i j` using `by ring`. Rewrite `hx` using `[e4, mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `hx ((h2.mul h2).mul hj)`.
-/
private theorem pivot {R : Type} [CommRing R] [IsLocalRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι R) (h2 : IsUnit (2 : R)) (hs : Hᵀ = H) (hd : IsUnit H.det) (i : ι) :
    ∃ Q : Matrix ι ι R, IsUnit Q.det ∧ IsUnit ((Qᵀ * H * Q) i i) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, IsUnit (H i j) := by
    by_contra hne
    push_neg at hne
    have key : ∑ j, H i j * adjugate H j i = H.det := by
      have := congrFun (congrFun (mul_adjugate H) i) i
      simpa [Matrix.mul_apply] using this
    have hm : ∑ j, H i j * adjugate H j i ∈ maximalIdeal R :=
      Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _
        (by rw [mem_maximalIdeal, mem_nonunits_iff]; exact hne j)
    rw [key, mem_maximalIdeal, mem_nonunits_iff] at hm
    exact hm hd
  by_cases hij : j = i
  · subst hij
    exact ⟨1, by simp, by simpa using hj⟩
  · have hji : H j i = H i j := by
      have := congrFun (congrFun hs i) j
      simpa using this
    have hent : ∀ c : R, ((transvection j i c)ᵀ * H * transvection j i c) i i
        = H i i + 2 * c * H i j + c * c * H j j := by
      intro c
      simp [transvection, Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
        add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite, Ne.symm hij, hij, hji]
      ring
    by_cases hp : IsUnit (H i i + 2 * 1 * H i j + 1 * 1 * H j j)
    · exact ⟨transvection j i 1, by rw [det_transvection_of_ne j i hij]; exact isUnit_one,
        by rw [hent]; exact hp⟩
    · refine ⟨transvection j i (-1), by rw [det_transvection_of_ne j i hij]; exact isUnit_one, ?_⟩
      rw [hent]
      by_contra hm
      have hx : (H i i + 2 * 1 * H i j + 1 * 1 * H j j)
          - (H i i + 2 * (-1) * H i j + (-1) * (-1) * H j j) ∈ maximalIdeal R :=
        Ideal.sub_mem _ ((mem_maximalIdeal _).2 hp) ((mem_maximalIdeal _).2 hm)
      have e4 : (H i i + 2 * 1 * H i j + 1 * 1 * H j j)
          - (H i i + 2 * (-1) * H i j + (-1) * (-1) * H j j) = 2 * 2 * H i j := by ring
      rw [e4, mem_maximalIdeal, mem_nonunits_iff] at hx
      exact hx ((h2.mul h2).mul hj)

/- English proof (translation)
Establish `hH : H = fromBlocks (H (Sum.inl ()) (Sum.inl ()) • (1 : Matrix Unit Unit R)) H.toBlocks₁₂ H.toBlocks₁₂ᵀ H.toBlocks₂₂`. Use extensionality with `(⟨⟩ | k) (⟨⟩ | l)`. Simplify using the standard rewrite rules. Simplify using `[toBlocks₁₂]`. Use `congrFun (congrFun hs (Sum.inl ())) (Sum.inr k)` as an intermediate fact.

Simplify using `only [transpose_apply] at this`. Simplify using `[toBlocks₁₂, this]`. Simplify using `[toBlocks₂₂]`. Generalize the expression as in `H (Sum.inl ()) (Sum.inl ()) = a at hH h0`. Generalize the expression as in `H.toBlocks₁₂ = B at hH`.

Generalize the expression as in `H.toBlocks₂₂ = D at hH`. Substitute `hH` using the available equality. Establish `hDs : Dᵀ = D`. Use `hs` as an intermediate fact. Rewrite `this` using `[fromBlocks_transpose]`.

Conclude with `(fromBlocks_inj.1 this).2.2.2`. Take `⟨b, hab⟩` from `h0.exists_right_inv`. Establish `hba : b * a = 1` using `by rw [mul_comm]; exact hab`. Establish `hE : (fromBlocks 1 (-(b • B)) 0 1 : Matrix (Unit ⊕ κ) (Unit ⊕ κ) R)ᵀ * fromBlocks (a • 1) B Bᵀ D * fromBlocks 1 (-(b • B)) 0 1 = fromBlocks (a • 1) 0 0 (D - b • (Bᵀ * B))`. Simplify using `[fromBlocks_transpose, fromBlocks_multiply, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hba, hab, sub_eq_neg_add]`.

Establish `hQ : IsUnit (fromBlocks 1 (-(b • B)) 0 1 : Matrix (Unit ⊕ κ) (Unit ⊕ κ) R).det`. Rewrite using `[det_fromBlocks_zero₂₁]`. Simplify using the standard rewrite rules. Apply `dgood_congr _ _ hQ` to reduce the goal to its premises. Rewrite using `[hE]`.

Establish `hSs : (D - b • (Bᵀ * B))ᵀ = D - b • (Bᵀ * B)`. Rewrite using `[transpose_sub, transpose_smul, transpose_mul, transpose_transpose, hDs]`. Establish `hSd : IsUnit (D - b • (Bᵀ * B)).det`. Establish `h1 : IsUnit (fromBlocks (a • 1) 0 0 (D - b • (Bᵀ * B)) : Matrix (Unit ⊕ κ) (Unit ⊕ κ) R).det`. Rewrite using `[← hE, det_mul, det_mul, det_transpose]`.

Conclude with `(hQ.mul hd).mul hQ`. Rewrite `h1` using `[det_fromBlocks_zero₂₁]`. Conclude with `isUnit_of_mul_isUnit_right h1`. Take `⟨P₀, hP₀, hP₀d⟩` from `ih _ hSs hSd`. Use `⟨fromBlocks 1 0 0 P₀, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[det_fromBlocks_zero₂₁, det_one, one_mul]`. Conclude with `hP₀`. Establish `hF : (fromBlocks 1 0 0 P₀ : Matrix (Unit ⊕ κ) (Unit ⊕ κ) R)ᵀ * fromBlocks (a • 1) 0 0 (D - b • (Bᵀ * B)) * fromBlocks 1 0 0 P₀ = fromBlocks (a • 1) 0 0 (P₀ᵀ * (D - b • (Bᵀ * B)) * P₀)`. Simplify using `[fromBlocks_transpose, fromBlocks_multiply]`. Rewrite using `[hF]`.

Conclude with `IsDiag.fromBlocks (fun i j h => absurd (Subsingleton.elim i j) h) hP₀d`.
-/
private theorem step {R : Type} [CommRing R] {κ : Type} [Fintype κ] [DecidableEq κ]
    (ih : ∀ H : Matrix κ κ R, Hᵀ = H → IsUnit H.det → DGood H)
    (H : Matrix (Unit ⊕ κ) (Unit ⊕ κ) R) (hs : Hᵀ = H) (hd : IsUnit H.det)
    (h0 : IsUnit (H (Sum.inl ()) (Sum.inl ()))) : DGood H := by
  classical
  have hH : H = fromBlocks (H (Sum.inl ()) (Sum.inl ()) • (1 : Matrix Unit Unit R))
      H.toBlocks₁₂ H.toBlocks₁₂ᵀ H.toBlocks₂₂ := by
    ext (⟨⟩ | k) (⟨⟩ | l)
    · simp
    · simp [toBlocks₁₂]
    · have := congrFun (congrFun hs (Sum.inl ())) (Sum.inr k)
      simp only [transpose_apply] at this
      simp [toBlocks₁₂, this]
    · simp [toBlocks₂₂]
  generalize H (Sum.inl ()) (Sum.inl ()) = a at hH h0
  generalize H.toBlocks₁₂ = B at hH
  generalize H.toBlocks₂₂ = D at hH
  subst hH
  have hDs : Dᵀ = D := by
    have := hs
    rw [fromBlocks_transpose] at this
    exact (fromBlocks_inj.1 this).2.2.2
  obtain ⟨b, hab⟩ := h0.exists_right_inv
  have hba : b * a = 1 := by rw [mul_comm]; exact hab
  have hE : (fromBlocks 1 (-(b • B)) 0 1 : Matrix (Unit ⊕ κ) (Unit ⊕ κ) R)ᵀ
      * fromBlocks (a • 1) B Bᵀ D * fromBlocks 1 (-(b • B)) 0 1
      = fromBlocks (a • 1) 0 0 (D - b • (Bᵀ * B)) := by
    simp [fromBlocks_transpose, fromBlocks_multiply, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      hba, hab, sub_eq_neg_add]
  have hQ : IsUnit (fromBlocks 1 (-(b • B)) 0 1 : Matrix (Unit ⊕ κ) (Unit ⊕ κ) R).det := by
    rw [det_fromBlocks_zero₂₁]; simp
  apply dgood_congr _ _ hQ
  rw [hE]
  have hSs : (D - b • (Bᵀ * B))ᵀ = D - b • (Bᵀ * B) := by
    rw [transpose_sub, transpose_smul, transpose_mul, transpose_transpose, hDs]
  have hSd : IsUnit (D - b • (Bᵀ * B)).det := by
    have h1 : IsUnit (fromBlocks (a • 1) 0 0 (D - b • (Bᵀ * B)) :
        Matrix (Unit ⊕ κ) (Unit ⊕ κ) R).det := by
      rw [← hE, det_mul, det_mul, det_transpose]
      exact (hQ.mul hd).mul hQ
    rw [det_fromBlocks_zero₂₁] at h1
    exact isUnit_of_mul_isUnit_right h1
  obtain ⟨P₀, hP₀, hP₀d⟩ := ih _ hSs hSd
  refine ⟨fromBlocks 1 0 0 P₀, ?_, ?_⟩
  · rw [det_fromBlocks_zero₂₁, det_one, one_mul]; exact hP₀
  · have hF : (fromBlocks 1 0 0 P₀ : Matrix (Unit ⊕ κ) (Unit ⊕ κ) R)ᵀ
        * fromBlocks (a • 1) 0 0 (D - b • (Bᵀ * B)) * fromBlocks 1 0 0 P₀
        = fromBlocks (a • 1) 0 0 (P₀ᵀ * (D - b • (Bᵀ * B)) * P₀) := by
      simp [fromBlocks_transpose, fromBlocks_multiply]
    rw [hF]
    exact IsDiag.fromBlocks (fun i j h => absurd (Subsingleton.elim i j) h) hP₀d

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `H _ _`. Conclude with `⟨1, by simp, fun i => Fin.elim0 i⟩`. Consider the case `succ n ih`.

Introduce `H hs hd`. Establish `e : Unit ⊕ Fin n ≃ Fin (n + 1)` using `Fintype.equivFinOfCardEq (by simp [add_comm])`. Take `⟨Q, hQ, hQi⟩` from `pivot H h2 hs hd (e (Sum.inl ()))`. Apply `dgood_congr H Q hQ` to reduce the goal to its premises. Apply `dgood_reindex e` to reduce the goal to its premises.

Apply `step ih` to reduce the goal to its premises. Simplify using `[transpose_submatrix, transpose_mul, hs, Matrix.mul_assoc]`. Rewrite using `[det_submatrix_equiv_self, det_mul, det_mul, det_transpose]`. Conclude with `(hQ.mul hd).mul hQ`. Conclude with `hQi`.
-/
private theorem dgood_fin {R : Type} [CommRing R] [IsLocalRing R] (h2 : IsUnit (2 : R)) (n : ℕ) :
    ∀ H : Matrix (Fin n) (Fin n) R, Hᵀ = H → IsUnit H.det → DGood H := by
  induction n with
  | zero =>
    intro H _ _
    exact ⟨1, by simp, fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro H hs hd
    have e : Unit ⊕ Fin n ≃ Fin (n + 1) := Fintype.equivFinOfCardEq (by simp [add_comm])
    obtain ⟨Q, hQ, hQi⟩ := pivot H h2 hs hd (e (Sum.inl ()))
    apply dgood_congr H Q hQ
    apply dgood_reindex e
    apply step ih
    · simp [transpose_submatrix, transpose_mul, hs, Matrix.mul_assoc]
    · rw [det_submatrix_equiv_self, det_mul, det_mul, det_transpose]
      exact (hQ.mul hd).mul hQ
    · exact hQi

end UpperTheory.V.AlgebraTools

/- English proof (translation)
Introduce `R _ _ n H h2 hs hd`. Take `⟨P, hP, hD⟩` from `UpperTheory.V.AlgebraTools.dgood_fin h2 n H hs hd`. Establish `hDu : IsUnit (Pᵀ * H * P).det`. Rewrite using `[det_mul, det_mul, det_transpose]`. Conclude with `(hP.mul hd).mul hP`.

Establish `hdiag : ∀ i, IsUnit ((Pᵀ * H * P) i i)`. Introduce `i`. Rewrite `hDu` using `[← hD.diagonal_diag, det_diagonal]`. Conclude with `isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (Pᵀ * H * P).diag (Finset.mem_univ i)) hDu`. Use `⟨((isUnit_iff_isUnit_det P).2 hP).unit, fun i => (hdiag i).unit, ?_⟩` and prove the remaining obligations.

Simplify using `only [IsUnit.unit_spec]`. Conclude with `hD.diagonal_diag.symm`.
-/
theorem UpperTheory.V.AlgebraTools.diag_local :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] {n : ℕ} (H : Matrix (Fin n) (Fin n) R), IsUnit (2 : R) → Hᵀ = H → IsUnit H.det → ∃ (P : GL (Fin n) R) (c : Fin n → Rˣ), (P : Matrix (Fin n) (Fin n) R)ᵀ * H * P = diagonal fun i => (c i : R) := by
  intro R _ _ n H h2 hs hd
  obtain ⟨P, hP, hD⟩ := UpperTheory.V.AlgebraTools.dgood_fin h2 n H hs hd
  have hDu : IsUnit (Pᵀ * H * P).det := by
    rw [det_mul, det_mul, det_transpose]
    exact (hP.mul hd).mul hP
  have hdiag : ∀ i, IsUnit ((Pᵀ * H * P) i i) := by
    intro i
    rw [← hD.diagonal_diag, det_diagonal] at hDu
    exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (Pᵀ * H * P).diag (Finset.mem_univ i)) hDu
  refine ⟨((isUnit_iff_isUnit_det P).2 hP).unit, fun i => (hdiag i).unit, ?_⟩
  simp only [IsUnit.unit_spec]
  exact hD.diagonal_diag.symm
