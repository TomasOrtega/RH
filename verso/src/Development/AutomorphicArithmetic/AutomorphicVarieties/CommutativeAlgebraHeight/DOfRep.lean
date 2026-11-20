import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

/- English proof (translation)
Establish `h1 : Det.repS r (Polynomial S) (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S (Polynomial S)) (AlgHom.id A E) y) = (Det.repS r S y).map Polynomial.C`. Proceed by induction on `y with`. Consider the case `zero => simp`. Consider the case `tmul s z => ext1 a b`. Simplify using `[Det.repS_tmul, Polynomial.algebraMap_apply]`.

Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb, map_add, Matrix.map_add _ (map_add _)]`. Express the relevant statement in the definitionally equal form `(Det.repS r (Polynomial S) _).det = _`. Rewrite using `[map_sub, h1, Det.repS_tmul, Matrix.charpoly, Matrix.charmatrix]`. Use `congr 2`. Use `ext1 a b`.

Apply the tactic sequence `by_cases hab : a = b <;> simp [hab, Matrix.one_apply, Matrix.diagonal_apply]`.
-/
private theorem chiS_ofRep {n : ℕ} {A E ι : Type} [CommRing A] [Ring E] [Algebra A E] [Fintype ι] [DecidableEq ι]
    (h : Fintype.card ι = n) (r : E →ₐ[A] Matrix ι ι A) (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] E) :
    (Det.ofRep h r).chiS S y = (Det.repS r S y).charpoly := by
  have h1 : Det.repS r (Polynomial S)
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S (Polynomial S)) (AlgHom.id A E) y) =
      (Det.repS r S y).map Polynomial.C := by
    induction y with
    | zero => simp
    | tmul s z => ext1 a b; simp [Det.repS_tmul, Polynomial.algebraMap_apply]
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, Matrix.map_add _ (map_add _)]
  change (Det.repS r (Polynomial S) _).det = _
  rw [map_sub, h1, Det.repS_tmul, Matrix.charpoly, Matrix.charmatrix]
  congr 2
  ext1 a b
  by_cases hab : a = b <;> simp [hab, Matrix.one_apply, Matrix.diagonal_apply]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(Det.repS r (Polynomial A) _).det = _`. Rewrite using `[map_sub, Det.repS_tmul, Det.repS_tmul, Matrix.charpoly, Matrix.charmatrix]`. Use `congr 2`. Use `ext1 a b`. Apply the tactic sequence `by_cases hab : a = b <;> simp [hab, Matrix.one_apply, Matrix.diagonal_apply]`.

Use `ext1 a b`. Simplify using the standard rewrite rules.
-/
private theorem chi_ofRep {n : ℕ} {A E ι : Type} [CommRing A] [Ring E] [Algebra A E] [Fintype ι] [DecidableEq ι]
    (h : Fintype.card ι = n) (r : E →ₐ[A] Matrix ι ι A) (x : E) :
    (Det.ofRep h r).chi x = (r x).charpoly := by
  change (Det.repS r (Polynomial A) _).det = _
  rw [map_sub, Det.repS_tmul, Det.repS_tmul, Matrix.charpoly, Matrix.charmatrix]
  congr 2
  · ext1 a b
    by_cases hab : a = b <;> simp [hab, Matrix.one_apply, Matrix.diagonal_apply]
  · ext1 a b
    simp

/- English proof (translation)
Proceed by induction on `z with`. Consider the case `zero => ext a b`. Simplify using the standard rewrite rules. Consider the case `tmul s z`. Use extensionality with `a b`.

Simplify using `only [Det.repS_tmul, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, MvPolynomial.algebraMap_eq]`. Rewrite using `[mul_comm s, MvPolynomial.coeff_C_mul]`. Simplify using `[mul_comm]`. Consider the case `add a b ha hb`. Rewrite using `[map_add, map_add, map_add, ha, hb, map_add, Matrix.map_add _ (MvPolynomial.coeff_add α)]`.
-/
private theorem coeff_repS {σ A E ι : Type} [CommRing A] [Ring E] [Algebra A E] [Fintype ι] [DecidableEq ι]
    (r : E →ₐ[A] Matrix ι ι A) (α : σ →₀ ℕ) (z : MvPolynomial σ A ⊗[A] E) :
    r (TensorProduct.lid A E ((MvPolynomial.lcoeff A α).rTensor E z)) =
      (Det.repS r (MvPolynomial σ A) z).map (MvPolynomial.coeff α) := by
  induction z with
  | zero => ext a b; simp
  | tmul s z =>
    ext a b
    simp only [Det.repS_tmul, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, MvPolynomial.algebraMap_eq]
    rw [mul_comm s, MvPolynomial.coeff_C_mul]
    simp [mul_comm]
  | add a b ha hb =>
    rw [map_add, map_add, map_add, ha, hb, map_add, Matrix.map_add _ (MvPolynomial.coeff_add α)]

/- English proof (translation)
Introduce `n A E ι _ _ _ _ _ h r x`. Use `⟨chi_ofRep h r x, ?_, fun hn => ?_, fun hx => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(Det.repS r A (1 ⊗ₜ x)).det = _`. Rewrite using `[Det.repS_tmul]`. Simplify using the standard rewrite rules.

Use `haveI : Nonempty ι := Fintype.card_pos_iff.1 (by omega)`. Rewrite using `[Det.tr, Det.lam, chi_ofRep, Matrix.trace_eq_neg_charpoly_coeff, h]`. Simplify using the standard rewrite rules. Establish `hle : (Det.ofRep h r).CH ≤ TwoSidedIdeal.ker r`. Rewrite using `[Det.CH, TwoSidedIdeal.span_le]`.

Introduce and unpack `z ⟨k, y, α, rfl⟩`. Express the relevant statement in the definitionally equal form `_ ∈ TwoSidedIdeal.ker r`. Rewrite using `[TwoSidedIdeal.mem_ker, Det.chElt, coeff_repS, chiS_ofRep, ← Polynomial.aeval_algHom_apply, Matrix.aeval_self_charpoly]`. Use extensionality with `a b`. Simplify using the standard rewrite rules.

Conclude with `(TwoSidedIdeal.mem_ker r).1 (hle hx)`.
-/
theorem UpperTheory.V.CA.d_ofRep :
    ∀ {n : ℕ} {A E ι : Type} [CommRing A] [Ring E] [Algebra A E] [Fintype ι] [DecidableEq ι] (h : Fintype.card ι = n) (r : E →ₐ[A] Matrix ι ι A) (x : E), (Det.ofRep h r).chi x = (r x).charpoly ∧ (Det.ofRep h r).val x = (r x).det ∧ (1 ≤ n → (Det.ofRep h r).tr x = (r x).trace) ∧ (x ∈ (Det.ofRep h r).CH → r x = 0) := by
  intro n A E ι _ _ _ _ _ h r x
  refine ⟨chi_ofRep h r x, ?_, fun hn => ?_, fun hx => ?_⟩
  · change (Det.repS r A (1 ⊗ₜ x)).det = _
    rw [Det.repS_tmul]
    simp
  · haveI : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    rw [Det.tr, Det.lam, chi_ofRep, Matrix.trace_eq_neg_charpoly_coeff, h]
    simp
  · have hle : (Det.ofRep h r).CH ≤ TwoSidedIdeal.ker r := by
      rw [Det.CH, TwoSidedIdeal.span_le]
      rintro z ⟨k, y, α, rfl⟩
      change _ ∈ TwoSidedIdeal.ker r
      rw [TwoSidedIdeal.mem_ker, Det.chElt, coeff_repS, chiS_ofRep, ← Polynomial.aeval_algHom_apply,
        Matrix.aeval_self_charpoly]
      ext a b
      simp
    exact (TwoSidedIdeal.mem_ker r).1 (hle hx)
