import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TensorCompl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaConstantMulOfCoprimeEllipticPolynomials
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeftMulMatrixTransfer

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.StructP

section Fac

variable {E : Type} [Field E]

abbrev Fac (P : E[X]) : Type := {Q // Q ∈ (UniqueFactorizationMonoid.normalizedFactors P).toFinset}

/- English proof (translation)
The claim follows from `Multiset.mem_toFinset.1 Q.2`.
-/
theorem fac_mem {P : E[X]} (Q : Fac P) : Q.1 ∈ UniqueFactorizationMonoid.normalizedFactors P :=
  Multiset.mem_toFinset.1 Q.2

/- English proof (translation)
The claim follows from `UniqueFactorizationMonoid.irreducible_of_normalized_factor _ (fac_mem Q)`.
-/
theorem fac_irr {P : E[X]} (Q : Fac P) : Irreducible Q.1 :=
  UniqueFactorizationMonoid.irreducible_of_normalized_factor _ (fac_mem Q)

instance factIrr {P : E[X]} (Q : Fac P) : Fact (Irreducible Q.1) := ⟨fac_irr Q⟩

/- English proof (translation)
Establish `h` using `UniqueFactorizationMonoid.normalize_normalized_factor _ (fac_mem Q)`. Rewrite using `[← h]`. Conclude with `Polynomial.monic_normalize (fac_irr Q).ne_zero`.
-/
theorem fac_monic {P : E[X]} (Q : Fac P) : Q.1.Monic := by
  have h := UniqueFactorizationMonoid.normalize_normalized_factor _ (fac_mem Q)
  rw [← h]
  exact Polynomial.monic_normalize (fac_irr Q).ne_zero

/- English proof (translation)
The claim follows from `UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (fac_mem Q)`.
-/
theorem fac_dvd {P : E[X]} (Q : Fac P) : Q.1 ∣ P :=
  UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (fac_mem Q)

/- English proof (translation)
Introduce `Q Q' hne`. Use `(Irreducible.coprime_iff_not_dvd (fac_irr Q)).2 fun hd => hne ?_` and prove the remaining obligations. Conclude with `Subtype.ext (Polynomial.eq_of_monic_of_associated (fac_monic Q) (fac_monic Q') ((fac_irr Q).associated_of_dvd (fac_irr Q') hd))`.
-/
theorem fac_coprime (P : E[X]) : Pairwise (Function.onFun IsCoprime fun Q : Fac P => Q.1) := by
  intro Q Q' hne
  refine (Irreducible.coprime_iff_not_dvd (fac_irr Q)).2 fun hd => hne ?_
  exact Subtype.ext (Polynomial.eq_of_monic_of_associated (fac_monic Q) (fac_monic Q')
    ((fac_irr Q).associated_of_dvd (fac_irr Q') hd))

/- English proof (translation)
The claim follows from `(UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hP.ne_zero).1 hP.squarefree`.
-/
theorem nodup_fac {P : E[X]} (hP : P.Separable) : (UniqueFactorizationMonoid.normalizedFactors P).Nodup :=
  (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hP.ne_zero).1 hP.squarefree

/- English proof (translation)
Rewrite using `[Finset.prod_coe_sort (UniqueFactorizationMonoid.normalizedFactors P).toFinset (fun Q => Q), Finset.prod_eq_multiset_prod, Multiset.toFinset_val, (nodup_fac hP).dedup, Multiset.map_id']`. Establish `hmon : (UniqueFactorizationMonoid.normalizedFactors P).prod.Monic`. Simplify using `using Polynomial.monic_multiset_prod_of_monic (UniqueFactorizationMonoid.normalizedFactors P) (fun Q => Q) (fun Q hQ => fac_monic (⟨Q, Multiset.mem_toFinset.2 hQ⟩ : Fac P))`. Conclude with `Polynomial.eq_of_monic_of_associated hmon hm (UniqueFactorizationMonoid.prod_normalizedFactors hP.ne_zero)`.
-/
theorem prod_fac {P : E[X]} (hm : P.Monic) (hP : P.Separable) : ∏ Q : Fac P, Q.1 = P := by
  rw [Finset.prod_coe_sort (UniqueFactorizationMonoid.normalizedFactors P).toFinset (fun Q => Q),
    Finset.prod_eq_multiset_prod, Multiset.toFinset_val, (nodup_fac hP).dedup, Multiset.map_id']
  have hmon : (UniqueFactorizationMonoid.normalizedFactors P).prod.Monic := by
    simpa using Polynomial.monic_multiset_prod_of_monic (UniqueFactorizationMonoid.normalizedFactors P) (fun Q => Q)
      (fun Q hQ => fac_monic (⟨Q, Multiset.mem_toFinset.2 hQ⟩ : Fac P))
  exact Polynomial.eq_of_monic_of_associated hmon hm (UniqueFactorizationMonoid.prod_normalizedFactors hP.ne_zero)

/- English proof (translation)
Rewrite using `[Fintype.card_coe, Multiset.toFinset_card_of_nodup (nodup_fac hP)]`. Both sides reduce to the same expression.
-/
theorem card_fac {P : E[X]} (hP : P.Separable) : Fintype.card (Fac P) = nfac P := by
  rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup (nodup_fac hP)]
  rfl

/- English proof (translation)
Introduce `τ z hz` and use `hr τ z (Multiset.mem_of_le (Polynomial.roots.le_of_dvd (hm.map τ).ne_zero (Polynomial.map_dvd τ (fac_dvd Q))) hz)`.
-/
theorem fac_roots {P : E[X]} (hm : P.Monic) (hr : ∀ τ : E →+* ℂ, ∀ z ∈ (P.map τ).roots, ‖z‖ = 1) (Q : Fac P) :
    ∀ τ : E →+* ℂ, ∀ z ∈ (Q.1.map τ).roots, ‖z‖ = 1 := fun τ z hz =>
  hr τ z (Multiset.mem_of_le (Polynomial.roots.le_of_dvd (hm.map τ).ne_zero (Polynomial.map_dvd τ (fac_dvd Q))) hz)

/- English proof (translation)
Establish `hcop : Pairwise (Function.onFun IsCoprime fun Q : Fac P => (Ideal.span {Q.1} : Ideal E[X]))`. Introduce `Q Q' h`. Conclude with `(Ideal.isCoprime_span_singleton_iff _ _).2 (fac_coprime P h)`. Take `⟨x, hx⟩` from `(Ideal.quotientInfRingEquivPiQuotient _ hcop).surjective z`. Take `⟨f, rfl⟩` from `Ideal.Quotient.mk_surjective x`.

Conclude with `⟨f, fun Q => congrFun hx Q⟩`.
-/
theorem exists_rep (P : E[X]) (z : ∀ Q : Fac P, AdjoinRoot Q.1) :
    ∃ f : E[X], ∀ Q : Fac P, AdjoinRoot.mk Q.1 f = z Q := by
  have hcop : Pairwise (Function.onFun IsCoprime fun Q : Fac P => (Ideal.span {Q.1} : Ideal E[X])) := by
    intro Q Q' h
    exact (Ideal.isCoprime_span_singleton_iff _ _).2 (fac_coprime P h)
  obtain ⟨x, hx⟩ := (Ideal.quotientInfRingEquivPiQuotient _ hcop).surjective z
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨f, fun Q => congrFun hx Q⟩

end Fac

section Ev

variable {E : Type} [Field E] {n : ℕ} (N : Matrix (Fin n) (Fin n) E)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h Q`. Conclude with `AdjoinRoot.mk_eq_zero.2 ((fac_dvd Q).trans (GlobalTheory.ClassParam.charpoly_dvd_of_aeval N hs f h))`. Introduce `h`. Establish `hd : ∏ Q : Fac N.charpoly, Q.1 ∣ f` using `Fintype.prod_dvd_of_coprime (fac_coprime _) fun Q => AdjoinRoot.mk_eq_zero.1 (h Q)`.

Rewrite `hd` using `[prod_fac (Matrix.charpoly_monic N) hs]`. Take `⟨k, rfl⟩` from `hd`. Rewrite using `[map_mul, Matrix.aeval_self_charpoly, zero_mul]`.
-/
theorem aeval_eq_zero_iff (hs : N.charpoly.Separable) (f : E[X]) :
    aeval N f = 0 ↔ ∀ Q : Fac N.charpoly, AdjoinRoot.mk Q.1 f = 0 := by
  constructor
  · intro h Q
    exact AdjoinRoot.mk_eq_zero.2 ((fac_dvd Q).trans (GlobalTheory.ClassParam.charpoly_dvd_of_aeval N hs f h))
  · intro h
    have hd : ∏ Q : Fac N.charpoly, Q.1 ∣ f :=
      Fintype.prod_dvd_of_coprime (fac_coprime _) fun Q => AdjoinRoot.mk_eq_zero.1 (h Q)
    rw [prod_fac (Matrix.charpoly_monic N) hs] at hd
    obtain ⟨k, rfl⟩ := hd
    rw [map_mul, Matrix.aeval_self_charpoly, zero_mul]

/- English proof (translation)
Rewrite using `[← sub_eq_zero, ← map_sub, aeval_eq_zero_iff N hs]`. Simplify using `only [map_sub, sub_eq_zero]`.
-/
theorem aeval_eq_iff (hs : N.charpoly.Separable) (f g : E[X]) :
    aeval N f = aeval N g ↔ ∀ Q : Fac N.charpoly, AdjoinRoot.mk Q.1 f = AdjoinRoot.mk Q.1 g := by
  rw [← sub_eq_zero, ← map_sub, aeval_eq_zero_iff N hs]
  simp only [map_sub, sub_eq_zero]

variable {F : Type} [Field F] [Algebra F E] {K : Fac N.charpoly → Type} [∀ Q, Field (K Q)] [∀ Q, Algebra F (K Q)]
  (j : ∀ Q : Fac N.charpoly, K Q →+* AdjoinRoot Q.1)

def repOf (a : ∀ Q, K Q) : E[X] := (exists_rep N.charpoly fun Q => j Q (a Q)).choose

/- English proof (translation)
The claim follows from `(exists_rep N.charpoly fun Q => j Q (a Q)).choose_spec Q`.
-/
theorem repOf_spec (a : ∀ Q, K Q) (Q : Fac N.charpoly) : AdjoinRoot.mk Q.1 (repOf N j a) = j Q (a Q) :=
  (exists_rep N.charpoly fun Q => j Q (a Q)).choose_spec Q

def rhoFun (a : ∀ Q, K Q) : Matrix (Fin n) (Fin n) E := aeval N (repOf N j a)

/- English proof (translation)
The claim follows from `(aeval_eq_iff N hs _ _).2 fun Q => (repOf_spec N j a Q).trans (hf Q).symm`.
-/
theorem rhoFun_eq (hs : N.charpoly.Separable) (a : ∀ Q, K Q) (f : E[X])
    (hf : ∀ Q, AdjoinRoot.mk Q.1 f = j Q (a Q)) : rhoFun N j a = aeval N f :=
  (aeval_eq_iff N hs _ _).2 fun Q => (repOf_spec N j a Q).trans (hf Q).symm

def rho (hs : N.charpoly.Separable)
    (hj : ∀ Q x, j Q (algebraMap F (K Q) x) = AdjoinRoot.of Q.1 (algebraMap F E x)) :
    (∀ Q, K Q) →ₐ[F] Matrix (Fin n) (Fin n) E where
  toFun := rhoFun N j
  map_one' := by
    show rhoFun N j 1 = 1
    rw [rhoFun_eq N j hs 1 1 (fun Q => by rw [map_one, Pi.one_apply, map_one]), map_one]
  map_mul' a b := by
    show rhoFun N j (a * b) = rhoFun N j a * rhoFun N j b
    rw [rhoFun_eq N j hs (a * b) (repOf N j a * repOf N j b)
      (fun Q => by rw [map_mul, repOf_spec, repOf_spec, Pi.mul_apply, map_mul]), map_mul]
    rfl
  map_zero' := by
    show rhoFun N j 0 = 0
    rw [rhoFun_eq N j hs 0 0 (fun Q => by rw [map_zero, Pi.zero_apply, map_zero]), map_zero]
  map_add' a b := by
    show rhoFun N j (a + b) = rhoFun N j a + rhoFun N j b
    rw [rhoFun_eq N j hs (a + b) (repOf N j a + repOf N j b)
      (fun Q => by rw [map_add, repOf_spec, repOf_spec, Pi.add_apply, map_add]), map_add]
    rfl
  commutes' x := by
    show rhoFun N j _ = _
    rw [rhoFun_eq N j hs _ (C (algebraMap F E x)) (fun Q => by rw [Pi.algebraMap_apply, hj, AdjoinRoot.mk_C]),
      aeval_C, IsScalarTower.algebraMap_apply F E (Matrix (Fin n) (Fin n) E)]

variable (hs : N.charpoly.Separable)
  (hj : ∀ Q x, j Q (algebraMap F (K Q) x) = AdjoinRoot.of Q.1 (algebraMap F E x))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rho_apply (a : ∀ Q, K Q) : rho N j hs hj a = aeval N (repOf N j a) := rfl

/- English proof (translation)
Introduce `a b hab`. Rewrite `hab` using `[rho_apply, rho_apply]`. Establish `h` using `(aeval_eq_iff N hs _ _).1 hab`. Use function extensionality and compare the values at `Q`. Apply `(j Q).injective` to reduce the goal to its premises.

Rewrite using `[← repOf_spec N j a Q, ← repOf_spec N j b Q]`. Conclude with `h Q`.
-/
theorem rho_injective : Function.Injective (rho N j hs hj) := by
  intro a b hab
  rw [rho_apply, rho_apply] at hab
  have h := (aeval_eq_iff N hs _ _).1 hab
  funext Q
  apply (j Q).injective
  rw [← repOf_spec N j a Q, ← repOf_spec N j b Q]
  exact h Q

/- English proof (translation)
Rewrite using `[rho_apply]`. Establish `h : aeval N (repOf N j a * X) = aeval N (X * repOf N j a)` using `by rw [mul_comm]`. Rewrite `h` using `[map_mul, map_mul, aeval_X]`. Then use the resulting hypothesis.
-/
theorem rho_comm (a : ∀ Q, K Q) : rho N j hs hj a * N = N * rho N j hs hj a := by
  rw [rho_apply]
  have h : aeval N (repOf N j a * X) = aeval N (X * repOf N j a) := by rw [mul_comm]
  rwa [map_mul, map_mul, aeval_X] at h

/- English proof (translation)
Take `⟨f, rfl⟩` from `GlobalTheory.BCT.ClsFin.exists_aeval_of_comm N x hs hx.symm`. Use `choose a b hab using fun Q => hspan Q (AdjoinRoot.mk Q.1 f)`. Use `⟨a, b, ?_⟩` and prove the remaining obligations. Rewrite using `[rho_apply, rho_apply]`. Establish `h : s • aeval N (repOf N j b) = aeval N (C s * repOf N j b)`.

Rewrite using `[map_mul, aeval_C, Algebra.algebraMap_eq_smul_one (A := Matrix (Fin n) (Fin n) E) s, smul_mul_assoc, one_mul]`. Rewrite using `[h, ← map_add]`. Use `(aeval_eq_iff N hs _ _).2 fun Q => ?_` and prove the remaining obligations. Rewrite using `[hab Q, map_add, map_mul, repOf_spec, repOf_spec, AdjoinRoot.mk_C]`.
-/
theorem rho_span (s : E)
    (hspan : ∀ (Q : Fac N.charpoly) (z : AdjoinRoot Q.1), ∃ (a b : K Q), z = j Q a + AdjoinRoot.of Q.1 s * j Q b)
    (x : Matrix (Fin n) (Fin n) E) (hx : x * N = N * x) :
    ∃ a b, x = rho N j hs hj a + s • (rho N j hs hj b : Matrix (Fin n) (Fin n) E) := by
  obtain ⟨f, rfl⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm N x hs hx.symm
  choose a b hab using fun Q => hspan Q (AdjoinRoot.mk Q.1 f)
  refine ⟨a, b, ?_⟩
  rw [rho_apply, rho_apply]
  have h : s • aeval N (repOf N j b) = aeval N (C s * repOf N j b) := by
    rw [map_mul, aeval_C, Algebra.algebraMap_eq_smul_one (A := Matrix (Fin n) (Fin n) E) s, smul_mul_assoc, one_mul]
  rw [h, ← map_add]
  refine (aeval_eq_iff N hs _ _).2 fun Q => ?_
  rw [hab Q, map_add, map_mul, repOf_spec, repOf_spec, AdjoinRoot.mk_C]

/- English proof (translation)
Rewrite using `[rho_apply]`. Use `set f := repOf N j a with hfdef`. Establish `hdet : IsUnit N.det`. Rewrite using `[hN]`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).1 (δ * thetaGL n c δ).isUnit`.

Establish `hdδ : IsUnit δ.val.det` using `(Matrix.isUnit_iff_isUnit_det _).1 δ.isUnit`. Take `⟨h, hh⟩` from `GlobalTheory.BCT.ClsFin.exists_aeval_of_comm N N⁻¹ hs (by rw [Matrix.mul_nonsing_inv _ hdet, Matrix.nonsing_inv_mul _ hdet])`. Establish `hroot : ∀ Q : Fac N.charpoly, AdjoinRoot.mk Q.1 h * AdjoinRoot.root Q.1 = 1`. Introduce `Q`. Establish `h1 : aeval N (h * X) = aeval N (1 : E[X])`.

Rewrite using `[map_mul, ← hh, aeval_X (R := E) N, map_one, Matrix.nonsing_inv_mul _ hdet]`. Establish `h2` using `(aeval_eq_iff N hs _ _).1 h1 Q`. Rewrite `h2` using `[map_mul, AdjoinRoot.mk_X, map_one]`. Then use the resulting hypothesis. Establish `hpoly : aeval N⁻¹ (f.map c) = aeval N f`. Rewrite using `[hh, ← Polynomial.aeval_comp]`.

Use `(aeval_eq_iff N hs _ _).2 fun Q => ?_` and prove the remaining obligations. Establish `hσroot : σ Q (AdjoinRoot.root Q.1) = AdjoinRoot.mk Q.1 h` using `mul_right_cancel₀ (right_ne_zero_of_mul_eq_one (hroot Q)) ((hσr Q).trans (hroot Q).symm)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[aeval_def, aeval_def, eval₂_map, hom_eval₂, hσroot]`. Use `congr 1`.

Conclude with `RingHom.ext fun x => (hσ Q x).symm`. Use `_ = AdjoinRoot.mk Q.1 f := by`. Rewrite using `[AdjoinRoot.aeval_eq, hfdef, repOf_spec N j a Q, hσj]`. Set `_ : StarRing E` to `{ star := c star_involutive := hc star_mul := fun x y => by show c (x * y) = c y * c x`. Rewrite using `[map_mul, mul_comm]`.

Use `star_add := map_add c }`. Establish `hsr : (starRingEnd E) = c` using `RingHom.ext fun _ => rfl`. Establish `hnrm : GlobalTheory.Tw.nrm δ.val = N`. Rewrite using `[hN, Units.val_mul]`. Use `show δ.val * (GlobalTheory.Tw.Phi n E * ((δ.val)⁻¹)ᴴ * (GlobalTheory.Tw.Phi n E)ᵀ) = δ.val * (GlobalTheory.Tw.Phi n E * (c.mapMatrix (δ⁻¹).val)ᵀ * (GlobalTheory.Tw.Phi n E)ᵀ)`.

Rewrite using `[Matrix.coe_units_inv]`. Both sides reduce to the same expression. Establish `hadj` using `GlobalTheory.BCT.KapMul.adj_aeval δ f`. Rewrite `hadj` using `[hnrm, hsr, hpoly]`. Establish `hadj' : δ.val * GlobalTheory.Tw.Phi n E * (aeval N f)ᴴ * (GlobalTheory.Tw.Phi n E)ᵀ * δ.val⁻¹ = aeval N f` using `hadj`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hadj']`. Use `_ = δ.val * GlobalTheory.Tw.Phi n E * (aeval N f)ᴴ * ((GlobalTheory.Tw.Phi n E)ᵀ * (δ.val⁻¹ * δ.val) * GlobalTheory.Tw.Phi n E) := by`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = δ.val * GlobalTheory.Tw.Phi n E * (aeval N f)ᴴ := by`.

Rewrite using `[Matrix.nonsing_inv_mul _ hdδ, Matrix.mul_one, GlobalTheory.Tw.Model.transpose_mul_Phi, Matrix.mul_one]`. Use `_ = δ.val * GlobalTheory.Tw.Phi n E * ((aeval N f).map c)ᵀ := rfl`.
-/
theorem rho_adj (c : E →+* E) (hc : ∀ x, c (c x) = x) (δ : GL (Fin n) E) (hN : N = (δ * thetaGL n c δ).val)
    (σ : ∀ Q : Fac N.charpoly, AdjoinRoot Q.1 →+* AdjoinRoot Q.1)
    (hσ : ∀ Q x, σ Q (AdjoinRoot.of Q.1 x) = AdjoinRoot.of Q.1 (c x))
    (hσr : ∀ Q, σ Q (AdjoinRoot.root Q.1) * AdjoinRoot.root Q.1 = 1)
    (hσj : ∀ Q a, σ Q (j Q a) = j Q a) (a : ∀ Q, K Q) :
    rho N j hs hj a * (δ.val * GlobalTheory.Tw.Phi n E) = δ.val * GlobalTheory.Tw.Phi n E * ((rho N j hs hj a).map c)ᵀ := by
  rw [rho_apply]
  set f := repOf N j a with hfdef
  have hdet : IsUnit N.det := by
    rw [hN]; exact (Matrix.isUnit_iff_isUnit_det _).1 (δ * thetaGL n c δ).isUnit
  have hdδ : IsUnit δ.val.det := (Matrix.isUnit_iff_isUnit_det _).1 δ.isUnit
  obtain ⟨h, hh⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm N N⁻¹ hs
    (by rw [Matrix.mul_nonsing_inv _ hdet, Matrix.nonsing_inv_mul _ hdet])
  have hroot : ∀ Q : Fac N.charpoly, AdjoinRoot.mk Q.1 h * AdjoinRoot.root Q.1 = 1 := by
    intro Q
    have h1 : aeval N (h * X) = aeval N (1 : E[X]) := by
      rw [map_mul, ← hh, aeval_X (R := E) N, map_one, Matrix.nonsing_inv_mul _ hdet]
    have h2 := (aeval_eq_iff N hs _ _).1 h1 Q
    rwa [map_mul, AdjoinRoot.mk_X, map_one] at h2
  have hpoly : aeval N⁻¹ (f.map c) = aeval N f := by
    rw [hh, ← Polynomial.aeval_comp]
    refine (aeval_eq_iff N hs _ _).2 fun Q => ?_
    have hσroot : σ Q (AdjoinRoot.root Q.1) = AdjoinRoot.mk Q.1 h :=
      mul_right_cancel₀ (right_ne_zero_of_mul_eq_one (hroot Q)) ((hσr Q).trans (hroot Q).symm)
    calc AdjoinRoot.mk Q.1 ((f.map c).comp h)
        = aeval (AdjoinRoot.root Q.1) ((f.map c).comp h) := (AdjoinRoot.aeval_eq _).symm
      _ = aeval (AdjoinRoot.mk Q.1 h) (f.map c) := by rw [Polynomial.aeval_comp, AdjoinRoot.aeval_eq]
      _ = σ Q (aeval (AdjoinRoot.root Q.1) f) := by
        rw [aeval_def, aeval_def, eval₂_map, hom_eval₂, hσroot]
        congr 1
        exact RingHom.ext fun x => (hσ Q x).symm
      _ = AdjoinRoot.mk Q.1 f := by
        rw [AdjoinRoot.aeval_eq, hfdef, repOf_spec N j a Q, hσj]
  let _ : StarRing E :=
    { star := c
      star_involutive := hc
      star_mul := fun x y => by
        show c (x * y) = c y * c x
        rw [map_mul, mul_comm]
      star_add := map_add c }
  have hsr : (starRingEnd E) = c := RingHom.ext fun _ => rfl
  have hnrm : GlobalTheory.Tw.nrm δ.val = N := by
    rw [hN, Units.val_mul]
    show δ.val * (GlobalTheory.Tw.Phi n E * ((δ.val)⁻¹)ᴴ * (GlobalTheory.Tw.Phi n E)ᵀ) =
      δ.val * (GlobalTheory.Tw.Phi n E * (c.mapMatrix (δ⁻¹).val)ᵀ * (GlobalTheory.Tw.Phi n E)ᵀ)
    rw [Matrix.coe_units_inv]
    rfl
  have hadj := GlobalTheory.BCT.KapMul.adj_aeval δ f
  rw [hnrm, hsr, hpoly] at hadj
  have hadj' : δ.val * GlobalTheory.Tw.Phi n E * (aeval N f)ᴴ * (GlobalTheory.Tw.Phi n E)ᵀ * δ.val⁻¹ = aeval N f := hadj
  calc aeval N f * (δ.val * GlobalTheory.Tw.Phi n E)
      = (δ.val * GlobalTheory.Tw.Phi n E * (aeval N f)ᴴ * (GlobalTheory.Tw.Phi n E)ᵀ * δ.val⁻¹) * (δ.val * GlobalTheory.Tw.Phi n E) := by
        rw [hadj']
    _ = δ.val * GlobalTheory.Tw.Phi n E * (aeval N f)ᴴ * ((GlobalTheory.Tw.Phi n E)ᵀ * (δ.val⁻¹ * δ.val) * GlobalTheory.Tw.Phi n E) := by
        simp only [Matrix.mul_assoc]
    _ = δ.val * GlobalTheory.Tw.Phi n E * (aeval N f)ᴴ := by
        rw [Matrix.nonsing_inv_mul _ hdδ, Matrix.mul_one, GlobalTheory.Tw.Model.transpose_mul_Phi, Matrix.mul_one]
    _ = δ.val * GlobalTheory.Tw.Phi n E * ((aeval N f).map c)ᵀ := rfl

end Ev

end PositivityTheory.Rg.BcB.G3.StructP

open PositivityTheory.Rg.BcB.G3.StructP in
/- English proof (translation)
Introduce `E _ _ _ s d hs0 hcs hd n δ hP`. Take `⟨hPm, hPn, hPs, hPr⟩` from `hP`. Establish `hdata : ∀ Q : Fac (δ * thE E n δ).val.charpoly, ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra (maximalRealSubfield E) K) (j : K →+* AdjoinRoot Q.1) (σ : AdjoinRoot Q.1 →+* AdjoinRoot Q.1), NumberField.IsTotallyReal K ∧ Module.finrank (maximalRealSubfield E) K = Q.1. …` using `fun Q => h1 E s d hs0 hcs hd Q.1 (fac_monic Q) (fac_roots hPm hPr Q)`. Use `choose K hKf hKn hKa j σ hKr hKdeg hj hσ hσr hσj hspan using hdata`. Use `⟨Fac (δ * thE E n δ).val.charpoly, inferInstance, K, hKf, hKn, hKa, rho _ j hPs hj, card_fac hPs, hKr, ?_, ?_⟩` and prove the remaining obligations.

Repeatedly rewrite using `[hKdeg]`. Rewrite using `[← Polynomial.natDegree_prod_of_monic _ _ (fun Q _ => fac_monic Q), prod_fac hPm hPs, hPn]`. Use `⟨rho_injective _ j hPs hj, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show rho _ j hPs hj (algebraMap _ _ d) = _`. Rewrite using `[AlgHom.commutes, IsScalarTower.algebraMap_apply (maximalRealSubfield E) E (Matrix (Fin n) (Fin n) E), hd, Algebra.algebraMap_eq_smul_one]`.

Introduce `a`. Conclude with `rho_adj _ j hPs hj (IsCMField.complexConj E).toRingEquiv.toRingHom (fun x => IsCMField.complexConj_apply_apply E x) δ rfl σ hσ hσr hσj a`. Introduce `a`. Conclude with `rho_comm _ j hPs hj a`. Introduce `x hx`.

Conclude with `rho_span _ j hPs hj s hspan x hx`.
-/
theorem PositivityTheory.Rg.BcB.G3.struct_pf (h1 : FactorField) : Struct := by
  intro E _ _ _ s d hs0 hcs hd n δ hP
  obtain ⟨hPm, hPn, hPs, hPr⟩ := hP
  have hdata : ∀ Q : Fac (δ * thE E n δ).val.charpoly, ∃ (K : Type) (_ : Field K) (_ : NumberField K)
      (_ : Algebra (maximalRealSubfield E) K) (j : K →+* AdjoinRoot Q.1) (σ : AdjoinRoot Q.1 →+* AdjoinRoot Q.1),
      NumberField.IsTotallyReal K ∧ Module.finrank (maximalRealSubfield E) K = Q.1.natDegree ∧
      (∀ x : (maximalRealSubfield E), j (algebraMap (maximalRealSubfield E) K x) =
        AdjoinRoot.of Q.1 (algebraMap (maximalRealSubfield E) E x)) ∧
      (∀ x : E, σ (AdjoinRoot.of Q.1 x) = AdjoinRoot.of Q.1 (IsCMField.complexConj E x)) ∧
      σ (AdjoinRoot.root Q.1) * AdjoinRoot.root Q.1 = 1 ∧ (∀ a, σ (j a) = j a) ∧
      ∀ z, ∃ a b, z = j a + AdjoinRoot.of Q.1 s * j b :=
    fun Q => h1 E s d hs0 hcs hd Q.1 (fac_monic Q) (fac_roots hPm hPr Q)
  choose K hKf hKn hKa j σ hKr hKdeg hj hσ hσr hσj hspan using hdata
  refine ⟨Fac (δ * thE E n δ).val.charpoly, inferInstance, K, hKf, hKn, hKa, rho _ j hPs hj, card_fac hPs, hKr, ?_, ?_⟩
  · simp_rw [hKdeg]
    rw [← Polynomial.natDegree_prod_of_monic _ _ (fun Q _ => fac_monic Q), prod_fac hPm hPs, hPn]
  · refine ⟨rho_injective _ j hPs hj, ?_, ?_, ?_, ?_⟩
    · show rho _ j hPs hj (algebraMap _ _ d) = _
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply (maximalRealSubfield E) E (Matrix (Fin n) (Fin n) E), hd,
        Algebra.algebraMap_eq_smul_one]
    · intro a
      exact rho_adj _ j hPs hj (IsCMField.complexConj E).toRingEquiv.toRingHom
        (fun x => IsCMField.complexConj_apply_apply E x) δ rfl σ hσ hσr hσj a
    · intro a
      exact rho_comm _ j hPs hj a
    · intro x hx
      exact rho_span _ j hPs hj s hspan x hx

end
