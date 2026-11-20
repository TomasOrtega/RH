import Mathlib
open IsDedekindDomain NumberField

namespace GlobalTheory.SmithBetween

open Matrix

open IsDedekindDomain NumberField in
open Matrix in

/- English proof (translation)
Establish `hinj : Function.Injective M.mulVecLin` using `Matrix.mulVec_injective_of_det_ne_zero hM`. Take `⟨m, snf⟩` from `Submodule.smithNormalForm (Pi.basisFun R n) (LinearMap.range M.mulVecLin)`. Establish `hm : m = Fintype.card n`. Establish `h1` using `Module.finrank_eq_card_basis snf.bN`. Rewrite `h1` using `[LinearMap.finrank_range_of_inj hinj]`.

Simplify using `using h1.symm`. Establish `hf : Function.Bijective snf.f`. Rewrite using `[Fintype.bijective_iff_injective_and_card]`. Conclude with `⟨snf.f.injective, by simp [hm]⟩`. Set `g : Fin m ≃ n` to `Equiv.ofBijective snf.f hf`.

Set `eN` to `LinearEquiv.ofInjective M.mulVecLin hinj`. Set `bQ : Module.Basis n R (n → R)` to `(snf.bN.map eN.symm).reindex g`. Use `letI := (Pi.basisFun R n).invertibleToMatrix snf.bM`. Use `letI := (Pi.basisFun R n).invertibleToMatrix bQ`. Use `⟨(Pi.basisFun R n).toMatrix snf.bM, (Pi.basisFun R n).toMatrix bQ, ?_, ?_, fun j => snf.a (g.symm j), ?_⟩` and prove the remaining obligations.

Conclude with `isUnit_det_of_invertible _`. Conclude with `isUnit_det_of_invertible _`. Use extensionality with `i j`. Establish `key : M *ᵥ bQ j = snf.a (g.symm j) • snf.bM j`. Establish `h2` using `snf.snf (g.symm j)`.

Establish `h3 : snf.f (g.symm j) = j` using `g.apply_symm_apply j`. Rewrite `h2` using `[h3]`. Rewrite using `[← h2]`. Simplify using `only [bQ, Module.Basis.reindex_apply, Module.Basis.map_apply]`. Establish `h4 : ((eN (eN.symm (snf.bN (g.symm j)))) : n → R) = M.mulVecLin (eN.symm (snf.bN (g.symm j)))` using `rfl`.

Rewrite `h4` using `[LinearEquiv.apply_symm_apply]`. Rewrite using `[← Matrix.mulVecLin_apply, ← h4]`. Use `congrFun key i` as an intermediate fact. Simplify using `only [Matrix.mul_diagonal, Module.Basis.toMatrix_apply, Pi.basisFun_repr]`. Rewrite using `[Matrix.mul_apply]`.

Simplify using `[Matrix.mulVec, dotProduct] at this`. Simplify `this` using `[mul_comm, Module.Basis.toMatrix_apply]`.
-/
theorem _root_.GlobalTheory.SmithBetween.exists_mul_eq_mul_diagonal {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n R) (hM : M.det ≠ 0) :
    ∃ P Q : Matrix n n R, IsUnit P.det ∧ IsUnit Q.det ∧ ∃ c : n → R,
      M * Q = P * Matrix.diagonal c := by
  have hinj : Function.Injective M.mulVecLin := Matrix.mulVec_injective_of_det_ne_zero hM
  obtain ⟨m, snf⟩ := Submodule.smithNormalForm (Pi.basisFun R n) (LinearMap.range M.mulVecLin)
  have hm : m = Fintype.card n := by
    have h1 := Module.finrank_eq_card_basis snf.bN
    rw [LinearMap.finrank_range_of_inj hinj] at h1
    simpa using h1.symm
  have hf : Function.Bijective snf.f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨snf.f.injective, by simp [hm]⟩
  let g : Fin m ≃ n := Equiv.ofBijective snf.f hf
  let eN := LinearEquiv.ofInjective M.mulVecLin hinj
  let bQ : Module.Basis n R (n → R) := (snf.bN.map eN.symm).reindex g
  letI := (Pi.basisFun R n).invertibleToMatrix snf.bM
  letI := (Pi.basisFun R n).invertibleToMatrix bQ
  refine ⟨(Pi.basisFun R n).toMatrix snf.bM, (Pi.basisFun R n).toMatrix bQ, ?_, ?_,
    fun j => snf.a (g.symm j), ?_⟩
  · exact isUnit_det_of_invertible _
  · exact isUnit_det_of_invertible _
  · ext i j
    have key : M *ᵥ bQ j = snf.a (g.symm j) • snf.bM j := by
      have h2 := snf.snf (g.symm j)
      have h3 : snf.f (g.symm j) = j := g.apply_symm_apply j
      rw [h3] at h2
      rw [← h2]
      simp only [bQ, Module.Basis.reindex_apply, Module.Basis.map_apply]
      have h4 : ((eN (eN.symm (snf.bN (g.symm j)))) : n → R) =
          M.mulVecLin (eN.symm (snf.bN (g.symm j))) := rfl
      rw [LinearEquiv.apply_symm_apply] at h4
      rw [← Matrix.mulVecLin_apply, ← h4]
    have := congrFun key i
    simp only [Matrix.mul_diagonal, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [Matrix.mul_apply]
    simp [Matrix.mulVec, dotProduct] at this
    simpa [mul_comm, Module.Basis.toMatrix_apply] using this

open IsDedekindDomain NumberField in
open Matrix in
/- English proof (translation)
Establish `hM0 : M.det ≠ 0`. Rewrite using `[hdet.ne_zero_iff]`. Conclude with `pow_ne_zero _ hϖ.ne_zero`. Take `⟨P, Q, hP, hQ, c, hMQ⟩` from `_root_.GlobalTheory.SmithBetween.exists_mul_eq_mul_diagonal M hM0`. Establish `hdvd : ∀ j, c j ∣ ϖ`.

Introduce `j`. Establish `hD : Matrix.diagonal c = P⁻¹ * M * Q`. Rewrite using `[Matrix.mul_assoc, hMQ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul]`. Establish `hX : Matrix.diagonal c * (Q⁻¹ * M' * P) = ϖ • (1 : Matrix (Fin n) (Fin n) R)`. Rewrite using `[hD]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = ϖ • (1 : Matrix (Fin n) (Fin n) R) := by`. Rewrite using `[Matrix.mul_nonsing_inv _ hQ, Matrix.mul_one, hMM, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.nonsing_inv_mul _ hP]`. Use `congrFun (congrFun hX j) j` as an intermediate fact.

Simplify using `only [Matrix.diagonal_mul, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at this`. Conclude with `⟨_, this.symm⟩`. Set `d : Fin n → R` to `fun j => if IsUnit (c j) then 1 else ϖ`. Establish `hu : ∀ j, ∃ u : Rˣ, c j = d j * u`. Introduce `j`.

Distinguish the cases in `h : IsUnit (c j)`. Conclude with `⟨h.unit, by simp [d, h]⟩`. Take `⟨b, hb⟩` from `hdvd j`. Break down `hϖ.isUnit_or_isUnit hb with h' | h'` into its components or cases. Conclude with `absurd h' h`.

Use `⟨h'.unit⁻¹, ?_⟩` and prove the remaining obligations. Simplify using `only [d, h, if_false, hb]`. Rewrite using `[mul_assoc, IsUnit.mul_val_inv, mul_one]`. Use `choose u hu using hu`. Use `set s := (Finset.univ.filter fun j => ¬IsUnit (c j)).card with hs`.

Establish `hprod : ∏ j, d j = ϖ ^ s`. Simplify using `only [d]`. Rewrite using `[Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]`. Establish `hsk : s = k`. Establish `h1 : M.det * Q.det = P.det * ∏ j, c j`.

Rewrite using `[← Matrix.det_mul, hMQ, Matrix.det_mul, Matrix.det_diagonal]`. Establish `h2 : ∏ j, c j = ϖ ^ s * ∏ j, (u j : R)`. Rewrite using `[← hprod, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun j _ => hu j`. Establish `h3 : Associated (ϖ ^ s) M.det`.

Establish `hA : Associated (M.det * Q.det) M.det` using `(associated_mul_isUnit_left_iff hQ).2 (Associated.refl _)`. Establish `hv : IsUnit (P.det * ∏ j, (u j : R))` using `hP.mul (by rw [← Units.coe_prod]; exact Units.isUnit _)`. Establish `hB : Associated (ϖ ^ s) (P.det * ∏ j, c j)`. Rewrite using `[h2, mul_left_comm]`. Conclude with `associated_mul_unit_right _ _ hv`.

Rewrite `hB` using `[← h1]`. Conclude with `hB.trans hA`. Establish `h4 : Associated (ϖ ^ s) (ϖ ^ k)` using `h3.trans hdet`. Conclude with `le_antisymm ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h4.dvd) ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h4.symm.dvd)`. Set `P'` to `P * Matrix.diagonal fun j => (u j : R)`.

Establish `hP' : IsUnit P'.det`. Simplify using `only [P', Matrix.det_mul, Matrix.det_diagonal]`. Conclude with `hP.mul (by rw [← Units.coe_prod]; exact Units.isUnit _)`. Establish `hMQ' : M * Q = P' * Matrix.diagonal d`. Rewrite using `[hMQ, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]`.

Use `congr 2`. Use function extensionality and compare the values at `j`. Rewrite using `[hu j, mul_comm]`. Establish `hcard1 : Fintype.card {j // ¬IsUnit (c j)} = Fintype.card {i : Fin n // ¬i.1 < n - k}`. Rewrite using `[Fintype.card_subtype, ← hs, hsk, Fintype.card_subtype_compl, Fintype.card_subtype, Fin.card_filter_val_lt, Fintype.card_fin]`.

Use linear arithmetic over natural numbers and integers. Establish `hcard0 : Fintype.card {j // IsUnit (c j)} = Fintype.card {i : Fin n // i.1 < n - k}`. Establish `h` using `Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (p := fun j => IsUnit (c j))`. Rewrite using `[Fintype.card_subtype, Fintype.card_subtype, Fin.card_filter_val_lt]`. Rewrite `h` using `[← hs, hsk, Finset.card_univ, Fintype.card_fin]`.

Use linear arithmetic over natural numbers and integers. Set `τ : Equiv.Perm (Fin n)` to `Equiv.subtypeCongr (Fintype.equivOfCardEq hcard0) (Fintype.equivOfCardEq hcard1)`. Establish `hτ : ∀ j, (τ j).1 < n - k ↔ IsUnit (c j)`. Introduce `j`. Distinguish the cases in `h : IsUnit (c j)`.

Establish `e1 : (Equiv.sumCompl fun x => IsUnit (c x)).symm j = Sum.inl ⟨j, h⟩` using `Equiv.sumCompl_symm_apply_of_pos (p := fun x => IsUnit (c x)) (a := j) h`. Simplify using `only [τ, Equiv.subtypeCongr, Equiv.trans_apply, Equiv.sumCongr_apply, e1, Sum.map_inl, Equiv.sumCompl_apply_inl, h, iff_true]`. Conclude with `(Fintype.equivOfCardEq hcard0 ⟨j, h⟩).2`. Establish `e1 : (Equiv.sumCompl fun x => IsUnit (c x)).symm j = Sum.inr ⟨j, h⟩` using `Equiv.sumCompl_symm_apply_of_neg (p := fun x => IsUnit (c x)) (a := j) h`. Simplify using `only [τ, Equiv.subtypeCongr, Equiv.trans_apply, Equiv.sumCongr_apply, e1, Sum.map_inr, Equiv.sumCompl_apply_inr, h, iff_false]`.

Conclude with `(Fintype.equivOfCardEq hcard1 ⟨j, h⟩).2`. Establish `hsign : ∀ A : Matrix (Fin n) (Fin n) R, IsUnit A.det → IsUnit (A.submatrix id τ.symm).det`. Introduce `A hA`. Rewrite using `[Matrix.det_permute']`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign τ.symm) with h | h <;> simp [h, hA]`.

Use `⟨P'.submatrix id τ.symm, Q.submatrix id τ.symm, hsign P' hP', hsign Q hQ, ?_⟩` and prove the remaining obligations. Establish `h1 : M * Q.submatrix id τ.symm = (M * Q).submatrix id τ.symm`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply]`. Rewrite using `[h1, hMQ', ← Matrix.submatrix_mul_equiv P' (Matrix.diagonal d) id τ.symm τ.symm, Matrix.submatrix_diagonal_equiv]`.

Use `congr 2`. Use function extensionality and compare the values at `i`. Use `hτ (τ.symm i)` as an intermediate fact. Rewrite `this` using `[Equiv.apply_symm_apply]`. Simplify using `only [Function.comp_apply, d]`.

Distinguish the cases in `hi : i.1 < n - k`. Simplify using `[hi, this.1 hi]`. Simplify using `[hi, mt this.2 hi]`.
-/
theorem _root_.GlobalTheory.SmithBetween.smith_between (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R)
    (hϖ : Irreducible ϖ) (n k : ℕ) (hk : k ≤ n) (M M' : Matrix (Fin n) (Fin n) R)
    (hMM : M * M' = ϖ • (1 : Matrix (Fin n) (Fin n) R)) (hdet : Associated M.det (ϖ ^ k)) :
    ∃ P Q : Matrix (Fin n) (Fin n) R, IsUnit P.det ∧ IsUnit Q.det ∧
      M * Q = P * Matrix.diagonal (fun i : Fin n => if i.1 < n - k then (1 : R) else ϖ) := by
  classical
  have hM0 : M.det ≠ 0 := by
    rw [hdet.ne_zero_iff]; exact pow_ne_zero _ hϖ.ne_zero
  obtain ⟨P, Q, hP, hQ, c, hMQ⟩ := _root_.GlobalTheory.SmithBetween.exists_mul_eq_mul_diagonal M hM0
  have hdvd : ∀ j, c j ∣ ϖ := by
    intro j
    have hD : Matrix.diagonal c = P⁻¹ * M * Q := by
      rw [Matrix.mul_assoc, hMQ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul]
    have hX : Matrix.diagonal c * (Q⁻¹ * M' * P) = ϖ • (1 : Matrix (Fin n) (Fin n) R) := by
      rw [hD]
      calc P⁻¹ * M * Q * (Q⁻¹ * M' * P) = P⁻¹ * (M * (Q * Q⁻¹) * M') * P := by
            simp only [Matrix.mul_assoc]
        _ = ϖ • (1 : Matrix (Fin n) (Fin n) R) := by
            rw [Matrix.mul_nonsing_inv _ hQ, Matrix.mul_one, hMM, Matrix.mul_smul, Matrix.mul_one,
              Matrix.smul_mul, Matrix.nonsing_inv_mul _ hP]
    have := congrFun (congrFun hX j) j
    simp only [Matrix.diagonal_mul, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      mul_one] at this
    exact ⟨_, this.symm⟩
  let d : Fin n → R := fun j => if IsUnit (c j) then 1 else ϖ
  have hu : ∀ j, ∃ u : Rˣ, c j = d j * u := by
    intro j
    by_cases h : IsUnit (c j)
    · exact ⟨h.unit, by simp [d, h]⟩
    · obtain ⟨b, hb⟩ := hdvd j
      rcases hϖ.isUnit_or_isUnit hb with h' | h'
      · exact absurd h' h
      · refine ⟨h'.unit⁻¹, ?_⟩
        simp only [d, h, if_false, hb]
        rw [mul_assoc, IsUnit.mul_val_inv, mul_one]
  choose u hu using hu

  set s := (Finset.univ.filter fun j => ¬IsUnit (c j)).card with hs
  have hprod : ∏ j, d j = ϖ ^ s := by
    simp only [d]
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  have hsk : s = k := by
    have h1 : M.det * Q.det = P.det * ∏ j, c j := by
      rw [← Matrix.det_mul, hMQ, Matrix.det_mul, Matrix.det_diagonal]
    have h2 : ∏ j, c j = ϖ ^ s * ∏ j, (u j : R) := by
      rw [← hprod, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun j _ => hu j
    have h3 : Associated (ϖ ^ s) M.det := by
      have hA : Associated (M.det * Q.det) M.det := (associated_mul_isUnit_left_iff hQ).2 (Associated.refl _)
      have hv : IsUnit (P.det * ∏ j, (u j : R)) :=
        hP.mul (by rw [← Units.coe_prod]; exact Units.isUnit _)
      have hB : Associated (ϖ ^ s) (P.det * ∏ j, c j) := by
        rw [h2, mul_left_comm]
        exact associated_mul_unit_right _ _ hv
      rw [← h1] at hB
      exact hB.trans hA
    have h4 : Associated (ϖ ^ s) (ϖ ^ k) := h3.trans hdet
    exact le_antisymm ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h4.dvd)
      ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h4.symm.dvd)
  let P' := P * Matrix.diagonal fun j => (u j : R)
  have hP' : IsUnit P'.det := by
    simp only [P', Matrix.det_mul, Matrix.det_diagonal]
    exact hP.mul (by rw [← Units.coe_prod]; exact Units.isUnit _)
  have hMQ' : M * Q = P' * Matrix.diagonal d := by
    rw [hMQ, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
    congr 2
    funext j
    rw [hu j, mul_comm]

  have hcard1 : Fintype.card {j // ¬IsUnit (c j)} = Fintype.card {i : Fin n // ¬i.1 < n - k} := by
    rw [Fintype.card_subtype, ← hs, hsk, Fintype.card_subtype_compl, Fintype.card_subtype,
      Fin.card_filter_val_lt, Fintype.card_fin]
    omega
  have hcard0 : Fintype.card {j // IsUnit (c j)} = Fintype.card {i : Fin n // i.1 < n - k} := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (p := fun j => IsUnit (c j))
    rw [Fintype.card_subtype, Fintype.card_subtype, Fin.card_filter_val_lt]
    rw [← hs, hsk, Finset.card_univ, Fintype.card_fin] at h
    omega
  let τ : Equiv.Perm (Fin n) :=
    Equiv.subtypeCongr (Fintype.equivOfCardEq hcard0) (Fintype.equivOfCardEq hcard1)
  have hτ : ∀ j, (τ j).1 < n - k ↔ IsUnit (c j) := by
    intro j
    by_cases h : IsUnit (c j)
    · have e1 : (Equiv.sumCompl fun x => IsUnit (c x)).symm j = Sum.inl ⟨j, h⟩ :=
        Equiv.sumCompl_symm_apply_of_pos (p := fun x => IsUnit (c x)) (a := j) h
      simp only [τ, Equiv.subtypeCongr, Equiv.trans_apply, Equiv.sumCongr_apply, e1, Sum.map_inl,
        Equiv.sumCompl_apply_inl, h, iff_true]
      exact (Fintype.equivOfCardEq hcard0 ⟨j, h⟩).2
    · have e1 : (Equiv.sumCompl fun x => IsUnit (c x)).symm j = Sum.inr ⟨j, h⟩ :=
        Equiv.sumCompl_symm_apply_of_neg (p := fun x => IsUnit (c x)) (a := j) h
      simp only [τ, Equiv.subtypeCongr, Equiv.trans_apply, Equiv.sumCongr_apply, e1, Sum.map_inr,
        Equiv.sumCompl_apply_inr, h, iff_false]
      exact (Fintype.equivOfCardEq hcard1 ⟨j, h⟩).2
  have hsign : ∀ A : Matrix (Fin n) (Fin n) R, IsUnit A.det → IsUnit (A.submatrix id τ.symm).det := by
    intro A hA
    rw [Matrix.det_permute']
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ.symm) with h | h <;> simp [h, hA]
  refine ⟨P'.submatrix id τ.symm, Q.submatrix id τ.symm, hsign P' hP', hsign Q hQ, ?_⟩
  have h1 : M * Q.submatrix id τ.symm = (M * Q).submatrix id τ.symm := by
    ext i j; simp [Matrix.mul_apply]
  rw [h1, hMQ', ← Matrix.submatrix_mul_equiv P' (Matrix.diagonal d) id τ.symm τ.symm,
    Matrix.submatrix_diagonal_equiv]
  congr 2
  funext i
  have := hτ (τ.symm i)
  rw [Equiv.apply_symm_apply] at this
  simp only [Function.comp_apply, d]
  by_cases hi : i.1 < n - k
  · simp [hi, this.1 hi]
  · simp [hi, mt this.2 hi]

end GlobalTheory.SmithBetween
