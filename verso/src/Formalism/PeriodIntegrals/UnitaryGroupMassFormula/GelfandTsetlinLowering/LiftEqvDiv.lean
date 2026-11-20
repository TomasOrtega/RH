import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftDefs
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Wlocal

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

section SlopeTestRemainingChoices

def tvU {r : ℕ} (a b : Fin r) (hab : a ≠ b) (t : ℂ) : GL (Fin r) ℂ where
  val := Formalism.UG.P.wlocal_E a b t
  inv := Formalism.UG.P.wlocal_E a b (-t)
  val_inv := by
    rw [Formalism.UG.P.wlocal_E_mul_E, if_neg hab, add_neg_cancel, add_zero, Formalism.UG.P.wlocal_E_zero]
  inv_val := by
    rw [Formalism.UG.P.wlocal_E_mul_E, if_neg hab, neg_add_cancel, add_zero, Formalism.UG.P.wlocal_E_zero]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Formalism.UG.P.wlocal_E, Matrix.transvection, Matrix.one_apply]`. Rewrite using `[Matrix.single_apply]`. Apply the tactic sequence `exact if_congr (by constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1.symm, h2.symm⟩) rfl rfl`.
-/
lemma wlocal_E_eq_tv {r : ℕ} (a b : Fin r) (t : ℂ) :
    Formalism.UG.P.wlocal_E a b t = Matrix.transvection a b t := by
  ext i j
  simp [Formalism.UG.P.wlocal_E, Matrix.transvection, Matrix.one_apply]
  rw [Matrix.single_apply]
  exact if_congr (by constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1.symm, h2.symm⟩) rfl rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.transpose_apply, Formalism.UG.P.wlocal_E]`. Use `congr 1`. Conclude with `if_congr eq_comm rfl rfl`. Conclude with `if_congr and_comm rfl rfl`.
-/
lemma wlocal_E_transpose {r : ℕ} (a b : Fin r) (t : ℂ) :
    (Formalism.UG.P.wlocal_E a b t).transpose = Formalism.UG.P.wlocal_E b a t := by
  ext i j
  simp only [Matrix.transpose_apply, Formalism.UG.P.wlocal_E]
  congr 1
  · exact if_congr eq_comm rfl rfl
  · exact if_congr and_comm rfl rfl

/- English proof (translation)
Establish `hdet : Matrix.GeneralLinearGroup.det u = 1`. Use `ext`. Simplify using `[Matrix.GeneralLinearGroup.val_det_apply, hu, wlocal_E_eq_tv, Matrix.det_transvection_of_ne _ _ hab]`. Unfold `sqAct detPow`. Rewrite using `[hdet, one_zpow, Units.val_one, one_smul, hu, wlocal_E_transpose]`.

Proceed by induction on `f using MvPolynomial.induction_on`. Use `next c => simp [Formalism.GradedWeylDivisibility.rowAct, Formalism.GradedWeylDivisibility.rowGen]`. Use `next p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]`. Use `next p v hp =>`. Rewrite using `[map_mul, map_mul, Polynomial.eval_mul, hp]`.

Use `congr 1`. Take `⟨i, j⟩` from `v`. Simplify using `only [Formalism.GradedWeylDivisibility.rowAct, Formalism.GradedWeylDivisibility.rowGen, MvPolynomial.aeval_X]`. Distinguish the cases in `hi : i = b`. Substitute `hi` using the available equality.

Simplify using `[Formalism.UG.P.wlocal_E, add_mul, Finset.sum_add_distrib, ite_and]`. Rewrite using `[Finset.sum_eq_single a (fun x _ hx => by simp [hx]) (by simp), if_pos rfl, mul_comm]`. Simplify using `[Formalism.UG.P.wlocal_E, add_mul, Finset.sum_add_distrib, hi]`.
-/
lemma sqAct_tv {r : ℕ} (ν : DomWeight r) (a b : Fin r) (hab : a ≠ b) (t : ℂ) (u : GL (Fin r) ℂ)
    (hu : (u : Matrix (Fin r) (Fin r) ℂ) = Formalism.UG.P.wlocal_E a b t) (f : MvPolynomial (Fin r × Fin r) ℂ) :
    sqAct ℂ r ν u f = Polynomial.eval (C t) (rowGen ℂ a b f) := by
  have hdet : Matrix.GeneralLinearGroup.det u = 1 := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, hu, wlocal_E_eq_tv,
      Matrix.det_transvection_of_ne _ _ hab]
  unfold sqAct detPow
  rw [hdet, one_zpow, Units.val_one, one_smul, hu, wlocal_E_transpose]
  induction f using MvPolynomial.induction_on
  next c => simp [Formalism.GradedWeylDivisibility.rowAct, Formalism.GradedWeylDivisibility.rowGen]
  next p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  next p v hp =>
    rw [map_mul, map_mul, Polynomial.eval_mul, hp]
    congr 1
    obtain ⟨i, j⟩ := v
    simp only [Formalism.GradedWeylDivisibility.rowAct, Formalism.GradedWeylDivisibility.rowGen, MvPolynomial.aeval_X]
    by_cases hi : i = b
    · subst hi
      simp [Formalism.UG.P.wlocal_E, add_mul, Finset.sum_add_distrib, ite_and]
      rw [Finset.sum_eq_single a (fun x _ hx => by simp [hx]) (by simp), if_pos rfl, mul_comm]
    · simp [Formalism.UG.P.wlocal_E, add_mul, Finset.sum_add_distrib, hi]

/- English proof (translation)
Substitute `h` using the available equality. Establish `he : ∀ x : Fin n, eRow (rfl : n + 1 = n + 1) x = Fin.castSucc x` using `fun x => Fin.ext rfl`. Establish `hl : ∀ x : Fin n, (Fin.last n = Fin.castSucc x) ↔ False` using `fun x => ⟨fun e => (Fin.castSucc_lt_last x).ne' e, False.elim⟩`. Use extensionality with `i j`. Simplify using `only [he]`.

Simplify using `[PI.embGL, PI.blkHom, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, tvU]`. Apply the tactic sequence `refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>`. Simplify using `[Formalism.UG.P.wlocal_E, hl]`.
-/
lemma embGL_tv {n N : ℕ} (h : n + 1 = N) (a b : Fin n) (hab : a ≠ b) (t : ℂ) :
    ((PI.embGL ℂ n N h (tvU a b hab t) : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      Formalism.UG.P.wlocal_E (eRow h a) (eRow h b) t := by
  subst h
  have he : ∀ x : Fin n, eRow (rfl : n + 1 = n + 1) x = Fin.castSucc x := fun x => Fin.ext rfl
  have hl : ∀ x : Fin n, (Fin.last n = Fin.castSucc x) ↔ False :=
    fun x => ⟨fun e => (Fin.castSucc_lt_last x).ne' e, False.elim⟩
  ext i j
  simp only [he]
  simp [PI.embGL, PI.blkHom, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, tvU]
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [Formalism.UG.P.wlocal_E, hl]

end SlopeTestRemainingChoices

/- English proof (translation)
Take `⟨d, hdP, hdQ⟩ : ∃ d, P.natDegree < d ∧ Q.natDegree < d` from `⟨P.natDegree + Q.natDegree + 1, by omega, by omega⟩`. Establish `hP : ∀ t : ℂ, P.eval (C t) = ∑ i ∈ Finset.range d, t ^ i • P.coeff i`. Introduce `t`. Rewrite using `[Polynomial.eval_eq_sum_range' hdP]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[MvPolynomial.smul_eq_C_mul, map_pow, mul_comm]`. Establish `hQ : ∀ t : ℂ, Q.eval (C t) = ∑ i ∈ Finset.range d, t ^ i • Q.coeff i`. Introduce `t`. Rewrite using `[Polynomial.eval_eq_sum_range' hdQ]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[MvPolynomial.smul_eq_C_mul, map_pow, mul_comm]`. Distinguish the cases in `hk : k < d`. Use `MvPolynomial.ext _ _ fun m => ?_` and prove the remaining obligations. Set `p : Polynomial ℂ` to `∑ i ∈ Finset.range d, Polynomial.monomial i (MvPolynomial.coeff m (φ (P.coeff i)))`. Set `q : Polynomial ℂ` to `∑ i ∈ Finset.range d, Polynomial.monomial i (MvPolynomial.coeff m (Q.coeff i))`.

Establish `hpq : p = q`. Apply `Polynomial.funext` to reduce the goal to its premises. Introduce `t`. Establish `e` using `congrArg (MvPolynomial.coeff m) (hPQ t)`. Rewrite `e` using `[hP t, hQ t, map_sum]`.

Simplify using `only [map_smul, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul] at e`. Simplify using `only [p, q, Polynomial.eval_finset_sum, Polynomial.eval_monomial]`. Simplify `e` using `[mul_comm]`. Establish `e2` using `congrArg (fun r => Polynomial.coeff r k) hpq`. Simplify `e2` using `[p, q, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, hk]`.

Establish `h1 : P.coeff k = 0` using `Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)`. Establish `h2 : Q.coeff k = 0` using `Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)`. Rewrite using `[h1, h2, map_zero]`.
-/
private theorem coeff_eq_of_eval_lemma {σ τ : Type*}
    (φ : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial τ ℂ)
    (P : Polynomial (MvPolynomial σ ℂ)) (Q : Polynomial (MvPolynomial τ ℂ))
    (hPQ : ∀ t : ℂ, φ (P.eval (C t)) = Q.eval (C t)) (k : ℕ) :
    φ (P.coeff k) = Q.coeff k := by
  obtain ⟨d, hdP, hdQ⟩ : ∃ d, P.natDegree < d ∧ Q.natDegree < d :=
    ⟨P.natDegree + Q.natDegree + 1, by omega, by omega⟩
  have hP : ∀ t : ℂ, P.eval (C t) = ∑ i ∈ Finset.range d, t ^ i • P.coeff i := by
    intro t
    rw [Polynomial.eval_eq_sum_range' hdP]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, map_pow, mul_comm]
  have hQ : ∀ t : ℂ, Q.eval (C t) = ∑ i ∈ Finset.range d, t ^ i • Q.coeff i := by
    intro t
    rw [Polynomial.eval_eq_sum_range' hdQ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, map_pow, mul_comm]
  by_cases hk : k < d
  · refine MvPolynomial.ext _ _ fun m => ?_
    let p : Polynomial ℂ :=
      ∑ i ∈ Finset.range d, Polynomial.monomial i (MvPolynomial.coeff m (φ (P.coeff i)))
    let q : Polynomial ℂ :=
      ∑ i ∈ Finset.range d, Polynomial.monomial i (MvPolynomial.coeff m (Q.coeff i))
    have hpq : p = q := by
      apply Polynomial.funext
      intro t
      have e := congrArg (MvPolynomial.coeff m) (hPQ t)
      rw [hP t, hQ t, map_sum] at e
      simp only [map_smul, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul] at e
      simp only [p, q, Polynomial.eval_finset_sum, Polynomial.eval_monomial]
      simpa [mul_comm] using e
    have e2 := congrArg (fun r => Polynomial.coeff r k) hpq
    simpa [p, q, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, hk] using e2
  · have h1 : P.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have h2 : Q.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [h1, h2, map_zero]

/- English proof (translation)
Introduce `n N h mu lam φ hφ a b hab k s hs`. Unfold `IsEqv at hφ`. Establish `hab' : eRow h a ≠ eRow h b` using `fun he => hab (Fin.ext (by simpa [eRow] using congrArg Fin.val he))`. Conclude with `coeff_eq_of_eval_lemma φ (rowGen ℂ a b s) (rowGen ℂ (eRow h a) (eRow h b) (φ s)) (fun t => by`. Establish `e1` using `hφ.2 (tvU a b hab t) s hs`.

Rewrite using `[sqAct_tv mu a b hab t _ rfl s, sqAct_tv lam (eRow h a) (eRow h b) hab' t _ (embGL_tv h a b hab t) (φ s)] at e1) k` and apply the resulting hypothesis.
-/
theorem equivariant_divisibility : EqvDiv := by
  intro n N h mu lam φ hφ a b hab k s hs
  unfold IsEqv at hφ
  have hab' : eRow h a ≠ eRow h b := fun he =>
    hab (Fin.ext (by simpa [eRow] using congrArg Fin.val he))
  exact coeff_eq_of_eval_lemma φ (rowGen ℂ a b s) (rowGen ℂ (eRow h a) (eRow h b) (φ s))
    (fun t => by
      have e1 := hφ.2 (tvU a b hab t) s hs
      rwa [sqAct_tv mu a b hab t _ rfl s,
        sqAct_tv lam (eRow h a) (eRow h b) hab' t _ (embGL_tv h a b hab t) (φ s)] at e1) k

end PI.WGL
