import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.SecJet GlobalTheory.CovTop

namespace GlobalTheory.SecJet

variable {R : Type} [CommRing R]

/- English proof (translation)
Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
private theorem spMap_comp_spMap' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (φ : A →+* B) (ψ : B →+* C) :
    spMap ψ ≫ spMap φ = spMap (ψ.comp φ) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem epsScaleR_mul (a c : R) : epsScaleR (a * c) = (epsScaleR a).comp (epsScaleR c) := by
  refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_
  · simp [epsScaleR]
  · simp [epsScaleR]
    ring

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem epsScale_mul (a c : R) : epsScale R (a * c) = epsScale R a ≫ epsScale R c := by
  apply Over.OverMorphism.ext
  change spMap (epsScaleR (a * c)) = spMap (epsScaleR a) ≫ spMap (epsScaleR c)
  rw [spMap_comp_spMap', epsScaleR_mul]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem comp_list_prod {T T' G : Over (Sp R)} [GrpObj G] (f : T ⟶ T') (l : List (T' ⟶ G)) :
    f ≫ l.prod = (l.map (f ≫ ·)).prod := by
  induction l with
  | nil => simp [comp_one]
  | cons g l ih => simp [comp_mul, ih]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem tanComb_smul {G : Over (Sp R)} [GrpObj G] {m : ℕ} (x : Fin m → R) (v : Fin m → (epsR R ⟶ G)) (a : R) :
    tanComb (a • x) v = epsScale R a ≫ tanComb x v := by
  rw [tanComb, tanComb, comp_list_prod, List.map_ofFn]
  congr 1
  refine List.ofFn_inj.2 (funext fun i => ?_)
  simp [Pi.smul_apply, smul_eq_mul, epsScale_mul]

def scalePoly (a : R) (k : ℕ) : MvPolynomial (Fin k) R →ₐ[R] MvPolynomial (Fin k) R :=
  MvPolynomial.aeval fun j => MvPolynomial.C a * MvPolynomial.X j

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sqIdeal_le_comap (a : R) (k : ℕ) : sqIdeal R k ≤ (sqIdeal R k).comap (scalePoly a k) := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨j, rfl⟩
  show scalePoly a k (MvPolynomial.X j ^ 2) ∈ sqIdeal R k
  rw [map_pow, scalePoly, MvPolynomial.aeval_X, mul_pow]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

def scaleA (a : R) (k : ℕ) : EpsAlg R k →ₐ[R] EpsAlg R k :=
  Ideal.quotientMapₐ (sqIdeal R k) (scalePoly a k) (sqIdeal_le_comap a k)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem scaleA_mk (a : R) (k : ℕ) (p : MvPolynomial (Fin k) R) :
    scaleA a k (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (scalePoly a k p) := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem scaleA_eps (a : R) {k : ℕ} (j : Fin k) : scaleA a k (eps R j) = a • eps R j := by
  rw [eps, scaleA_mk, scalePoly, MvPolynomial.aeval_X, Algebra.smul_def, map_mul]
  rfl

def scaleO (a : R) (k : ℕ) : epsT R k ⟶ epsT R k :=
  Over.homMk (spMap ((scaleA a k : EpsAlg R k →ₐ[R] EpsAlg R k) : EpsAlg R k →+* EpsAlg R k))
    (spMap_comp_eq R (scaleA a k))

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem epsIncl_comp_epsScaleA (a : R) {k : ℕ} (j : Fin k) :
    (epsIncl R j).comp (epsScaleA R a) = (scaleA a k).comp (epsIncl R j) := by
  apply DualNumber.algHom_ext
  have h1 : epsScaleA R a DualNumber.eps = a • DualNumber.eps := by
    show epsScaleR a DualNumber.eps = _
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [epsScaleR]
    · simp [epsScaleR]
  simp only [AlgHom.comp_apply, h1, map_smul]
  simp [epsIncl, scaleA_eps]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem epsIn_comp_epsScale (a : R) {k : ℕ} (j : Fin k) :
    epsIn R j ≫ epsScale R a = scaleO a k ≫ epsIn R j := by
  apply Over.OverMorphism.ext
  change spMap ((epsIncl R j : DualNumber R →ₐ[R] EpsAlg R k) : DualNumber R →+* EpsAlg R k) ≫ spMap (epsScaleR a) =
    spMap ((scaleA a k : EpsAlg R k →ₐ[R] EpsAlg R k) : EpsAlg R k →+* EpsAlg R k) ≫
      spMap ((epsIncl R j : DualNumber R →ₐ[R] EpsAlg R k) : DualNumber R →+* EpsAlg R k)
  rw [spMap_comp_spMap', spMap_comp_spMap']
  congr 1
  exact congrArg AlgHom.toRingHom (epsIncl_comp_epsScaleA a j)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem epsPt_epsScale {G : Over (Sp R)} [GrpObj G] (y : epsR R ⟶ G) (a : R) (k : ℕ) :
    epsPt (epsScale R a ≫ y) k = scaleO a k ≫ epsPt y k := by
  rw [epsPt, epsPt, comp_list_prod, List.map_ofFn]
  congr 1
  refine List.ofFn_inj.2 (funext fun j => ?_)
  simp only [Function.comp_apply]
  rw [← Category.assoc, epsIn_comp_epsScale, Category.assoc]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem mkN_scaleA (a : R) (k : ℕ) :
    (Ideal.Quotient.mkₐ R (nilradical (EpsAlg R k))).comp (scaleA a k) =
      Ideal.Quotient.mkₐ R (nilradical (EpsAlg R k)) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro j
  have hn : eps R j ∈ nilradical (EpsAlg R k) := mem_nilradical.2 ⟨2, by rw [sq, eps_mul_self]⟩
  have h1 : Ideal.Quotient.mkₐ R (nilradical (EpsAlg R k)) (eps R j) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hn
  change Ideal.Quotient.mkₐ R (nilradical (EpsAlg R k)) (scaleA a k (eps R j)) =
    Ideal.Quotient.mkₐ R (nilradical (EpsAlg R k)) (eps R j)
  rw [scaleA_eps, map_smul, h1, smul_zero]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem scaleA_sub_mem (a : R) {k : ℕ} (e : EpsAlg R k) (P : Ideal (EpsAlg R k)) [P.IsPrime] :
    scaleA a k e - e ∈ P := by
  refine nilradical_le_prime P ?_
  have := congrArg (fun g => g e) (mkN_scaleA a k)
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
  exact Ideal.Quotient.eq.1 this

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem scaleO_base (a : R) (k : ℕ) (p : Sp (EpsAlg R k)) :
    (spMap ((scaleA a k : EpsAlg R k →ₐ[R] EpsAlg R k) : EpsAlg R k →+* EpsAlg R k)).base p = p := by
  apply PrimeSpectrum.ext
  ext e
  change scaleA a k e ∈ p.asIdeal ↔ e ∈ p.asIdeal
  haveI := p.isPrime
  have h := scaleA_sub_mem a e p.asIdeal
  constructor
  · intro he
    simpa using p.asIdeal.sub_mem he h
  · intro he
    simpa using p.asIdeal.add_mem h he

/- English proof (translation)
Consider separately whether the proposition holds or fails. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem valR_scaleO (a : R) (k : ℕ) {X : Scheme.{0}} (z : Sp (EpsAlg R k) ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    valR (spMap ((scaleA a k : EpsAlg R k →ₐ[R] EpsAlg R k) : EpsAlg R k →+* EpsAlg R k) ≫ z) U f =
      scaleA a k (valR z U f) := by
  set ρ : EpsAlg R k →+* EpsAlg R k := ((scaleA a k : EpsAlg R k →ₐ[R] EpsAlg R k) : EpsAlg R k →+* EpsAlg R k)
  by_cases hx : ⊤ ≤ z ⁻¹ᵁ U
  · have hx' : ⊤ ≤ (spMap ρ ≫ z) ⁻¹ᵁ U := fun p _ => hx (x := spMap ρ p) trivial
    have h3 : (spMap ρ).appLE ⊤ ⊤ le_rfl = (spMap ρ).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
    rw [valR, valR, dif_pos hx, dif_pos hx', ← Scheme.Hom.appLE_comp_appLE (spMap ρ) z U ⊤ ⊤ hx le_rfl, h3]
    exact congrArg (fun q => q.hom ((z.appLE U ⊤ hx).hom f)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ρ))
  · have hx' : ¬ ⊤ ≤ (spMap ρ ≫ z) ⁻¹ᵁ U := by
      intro h
      refine hx fun p _ => ?_
      have := h (x := p) trivial
      change z.base ((spMap ρ).base p) ∈ U at this
      rwa [scaleO_base] at this
    rw [valR, valR, dif_neg hx, dif_neg hx', map_zero]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem topCoeff_mk {k : ℕ} (p : MvPolynomial (Fin k) R) :
    topCoeff R k (Ideal.Quotient.mk _ p) = MvPolynomial.coeff (topMon k) p := rfl

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem scalePoly_monomial (a : R) {k : ℕ} (u : Fin k →₀ ℕ) (c : R) :
    scalePoly a k (MvPolynomial.monomial u c) = MvPolynomial.monomial u (a ^ (∑ j, u j) * c) := by
  have e1 : (∏ j, (MvPolynomial.C a * MvPolynomial.X j : MvPolynomial (Fin k) R) ^ u j) =
      MvPolynomial.C (a ^ (∑ j, u j)) * ∏ j, (MvPolynomial.X j : MvPolynomial (Fin k) R) ^ u j := by
    simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod, Finset.prod_pow_eq_pow_sum]
  have e2 : (∏ j, (MvPolynomial.X j : MvPolynomial (Fin k) R) ^ u j) = MvPolynomial.monomial u 1 := by
    rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, _root_.one_mul, Finsupp.prod_pow]
  rw [scalePoly, MvPolynomial.aeval_monomial, Finsupp.prod_pow, e1, e2, MvPolynomial.algebraMap_eq,
    MvPolynomial.C_mul_monomial, MvPolynomial.C_mul_monomial, _root_.mul_one, _root_.mul_comm c]

/- English proof (translation)
Proceed by induction. Treat this case separately. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Treat this case separately. A detailed English derivation is pending.
-/
theorem coeff_scalePoly (a : R) {k : ℕ} (m : Fin k →₀ ℕ) (p : MvPolynomial (Fin k) R) :
    MvPolynomial.coeff m (scalePoly a k p) = a ^ (∑ j, m j) * MvPolynomial.coeff m p := by
  induction p using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [scalePoly_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    split_ifs with h
    · rw [h]
    · rw [mul_zero]
  | add p q hp hq => rw [map_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem sum_topMon (k : ℕ) : ∑ j, topMon k j = k := by
  have h : ∀ j : Fin k, topMon k j = 1 := fun j => by
    simp [topMon, Finsupp.finsetSum_apply, Finsupp.single_apply]
  simp [h]

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.
-/
theorem topCoeff_scaleA (a : R) (k : ℕ) (e : EpsAlg R k) : topCoeff R k (scaleA a k e) = a ^ k * topCoeff R k e := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective e
  rw [scaleA_mk, topCoeff_mk, topCoeff_mk, coeff_scalePoly, sum_topMon]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem jetVal_tanComb_smul : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (m : ℕ) (v : Fin m → (epsR R ⟶ G))
    (x : Fin m → R) (a : R) (k : ℕ) (U : G.left.Opens) (f : Γ(G.left, U)),
    jetVal (tanComb (a • x) v) k U f = a ^ k * jetVal (tanComb x v) k U f := by
  intro R _ G _ m v x a k U f
  rw [jetVal, jetVal, tanComb_smul, epsPt_epsScale]
  change topCoeff R k (valR (spMap ((scaleA a k : EpsAlg R k →ₐ[R] EpsAlg R k) : EpsAlg R k →+* EpsAlg R k) ≫
    (epsPt (tanComb x v) k).left) U f) = _
  rw [valR_scaleO, topCoeff_scaleA]

end GlobalTheory.SecJet
