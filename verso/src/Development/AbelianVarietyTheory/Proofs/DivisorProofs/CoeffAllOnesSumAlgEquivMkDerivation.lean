import Mathlib
open MvPolynomial

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `q using MvPolynomial.induction_on with`. Consider the case `C a => simp [sumAlgEquiv_C_inl]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p v hp => simp only [map_mul, hp, rename_X, sumAlgEquiv_X_inr]`.
-/
theorem sumAlgEquiv_rename_inr_eq_C {σ : Type} {L : ℕ} (q : MvPolynomial σ ℂ) :
    MvPolynomial.sumAlgEquiv ℂ (Fin L) σ (MvPolynomial.rename Sum.inr q) = MvPolynomial.C q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp [sumAlgEquiv_C_inl]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp => simp only [map_mul, hp, rename_X, sumAlgEquiv_X_inr]

/- English proof (translation)
Proceed by induction on `b using MvPolynomial.induction_on generalizing m with`. Consider the case `C a`. Establish `h1 : (MvPolynomial.C a : MvPolynomial (Fin L ⊕ σ) ℂ) = algebraMap ℂ _ a` using `rfl`. Rewrite using `[h1, Derivation.map_algebraMap, map_zero, coeff_zero, AlgEquiv.commutes]`. Rewrite using `[MvPolynomial.algebraMap_apply, MvPolynomial.coeff_C]`.

Use `split_ifs`. Conclude with `(D.map_algebraMap a).symm`. Simplify using the standard rewrite rules. Consider the case `add p q hp hq => simp only [map_add, coeff_add, hp, hq]`. Consider the case `mul_X p i hp`.

Rewrite using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, map_mul, coeff_add]`. Break down `i with j | v` into its components or cases. Simplify using `only [mkDerivation_X, Sum.elim_inl, map_zero, mul_zero, coeff_zero, zero_add, sumAlgEquiv_X_inl]`. Rewrite using `[mul_comm (X j), coeff_mul_X', coeff_mul_X']`. Use `split_ifs`.

Conclude with `hp _`. Conclude with `(D.map_zero).symm`. Simplify using `only [mkDerivation_X, Sum.elim_inr, sumAlgEquiv_X_inr, sumAlgEquiv_rename_inr_eq_C, coeff_C_mul, hp]`. Rewrite using `[mul_comm ((sumAlgEquiv ℂ (Fin L) σ) p) (C (D (X v))), mul_comm ((sumAlgEquiv ℂ (Fin L) σ) p) (C (X v)), coeff_C_mul, coeff_C_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coeff_sumAlgEquiv_mkDerivation_gen {σ : Type} {L : ℕ}
    (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (b : MvPolynomial (Fin L ⊕ σ) ℂ) (m : Fin L →₀ ℕ) :
    MvPolynomial.coeff m (MvPolynomial.sumAlgEquiv ℂ (Fin L) σ
      (MvPolynomial.mkDerivation ℂ (Sum.elim (fun _ : Fin L => (0 : MvPolynomial (Fin L ⊕ σ) ℂ))
        (fun v : σ => MvPolynomial.rename Sum.inr (D (MvPolynomial.X v)))) b)) =
      D (MvPolynomial.coeff m (MvPolynomial.sumAlgEquiv ℂ (Fin L) σ b)) := by
  induction b using MvPolynomial.induction_on generalizing m with
  | C a =>
    have h1 : (MvPolynomial.C a : MvPolynomial (Fin L ⊕ σ) ℂ) = algebraMap ℂ _ a := rfl
    rw [h1, Derivation.map_algebraMap, map_zero, coeff_zero, AlgEquiv.commutes]
    rw [MvPolynomial.algebraMap_apply, MvPolynomial.coeff_C]
    split_ifs
    · exact (D.map_algebraMap a).symm
    · simp
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq]
  | mul_X p i hp =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, map_mul, coeff_add]
    rcases i with j | v
    · simp only [mkDerivation_X, Sum.elim_inl, map_zero, mul_zero, coeff_zero, zero_add,
        sumAlgEquiv_X_inl]
      rw [mul_comm (X j), coeff_mul_X', coeff_mul_X']
      split_ifs
      · exact hp _
      · exact (D.map_zero).symm
    · simp only [mkDerivation_X, Sum.elim_inr, sumAlgEquiv_X_inr, sumAlgEquiv_rename_inr_eq_C,
        coeff_C_mul, hp]
      rw [mul_comm ((sumAlgEquiv ℂ (Fin L) σ) p) (C (D (X v))),
        mul_comm ((sumAlgEquiv ℂ (Fin L) σ) p) (C (X v)), coeff_C_mul, coeff_C_mul,
        Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      ring

/- English proof (translation)
Introduce `D b` and use `coeff_sumAlgEquiv_mkDerivation_gen D b _`.
-/
theorem coeff_allOnes_sumAlgEquiv_mkDerivation :
    ∀ {σ : Type} {L : ℕ} (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) (b : MvPolynomial (Fin L ⊕ σ) ℂ), MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm fun _ : Fin L => (1 : ℕ)) (MvPolynomial.sumAlgEquiv ℂ (Fin L) σ (MvPolynomial.mkDerivation ℂ (Sum.elim (fun _ : Fin L => (0 : MvPolynomial (Fin L ⊕ σ) ℂ)) (fun v : σ => MvPolynomial.rename Sum.inr (D (MvPolynomial.X v)))) b)) = D (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm fun _ : Fin L => (1 : ℕ)) (MvPolynomial.sumAlgEquiv ℂ (Fin L) σ (b))) :=
  fun D b => coeff_sumAlgEquiv_mkDerivation_gen D b _

end GlobalTheory
