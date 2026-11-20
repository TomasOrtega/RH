import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SubDSharpInDeg
import Formalism.LocalToGlobal.KernelLattices.ThDistC

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.JetCharScale

variable {K : Type} [Field K]

def scaleVar {σ : Type} (u : σ → K) : MvPolynomial σ K →ₐ[K] MvPolynomial σ K := aeval fun v => C (u v) * X v

/- English proof (translation)
Rewrite using `[scaleVar, aeval_monomial, smul_eq_C_mul, monomial_eq]`. Simplify using `only [mul_pow, Finsupp.prod, Finset.prod_mul_distrib, map_prod, map_pow, algebraMap_eq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem scaleVar_monomial {σ : Type} (u : σ → K) (m : σ →₀ ℕ) (c : K) :
    scaleVar u (monomial m c) = (m.prod fun v e => u v ^ e) • monomial m c := by
  rw [scaleVar, aeval_monomial, smul_eq_C_mul, monomial_eq]
  simp only [mul_pow, Finsupp.prod, Finset.prod_mul_distrib, map_prod, map_pow, algebraMap_eq]
  ring

variable {ι : Type} {a b : ℕ}

/- English proof (translation)
Use `(basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) K).constr_basis K (fun m => (monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn) (J (m.comapDomain Sum.inr Sum.inr_injective.injOn)) : Pol K ι b)) m` as an intermediate fact. Rewrite `this` using `[coe_basisMonomials]`. Conclude with `this`.
-/
theorem jetLin_monomial (J : (DVar ι a b →₀ ℕ) → K) (m : (ι × Fin b × Fin b) ⊕ DVar ι a b →₀ ℕ) :
    jetLin J (monomial m 1) = monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn)
      (J (m.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
  have := (basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) K).constr_basis K (fun m =>
    (monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn) (J (m.comapDomain Sum.inr Sum.inr_injective.injOn)) : Pol K ι b)) m
  rw [coe_basisMonomials] at this
  exact this

/- English proof (translation)
Use `AlgHom.congr_fun (φ₁ := (scaleVar _).comp (subD K ι a b)) (φ₂ := (scaleVar _).comp (subD K ι a b)) (MvPolynomial.algHom_ext fun v => ?_) P` and prove the remaining obligations. Simplify using `only [AlgHom.comp_apply, subD, aeval_X]`. Use `split_ifs with h`. Simplify using `only [map_sum, map_mul, scaleVar, aeval_X, Sum.elim_inl, Sum.elim_inr, map_one]`. Use `Finset.sum_congr rfl fun β _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
theorem subD_scale (w : ι → K) (P : Pol K ι a) :
    scaleVar (Sum.elim (fun _ => 1) fun k => w k.1) (subD K ι a b P) =
      scaleVar (Sum.elim (fun v => w v.1) fun _ => 1) (subD K ι a b P) := by
  refine AlgHom.congr_fun (φ₁ := (scaleVar _).comp (subD K ι a b)) (φ₂ := (scaleVar _).comp (subD K ι a b))
    (MvPolynomial.algHom_ext fun v => ?_) P
  simp only [AlgHom.comp_apply, subD, aeval_X]
  split_ifs with h
  · simp only [map_sum, map_mul, scaleVar, aeval_X, Sum.elim_inl, Sum.elim_inr, map_one]
    refine Finset.sum_congr rfl fun β _ => ?_
    ring
  · simp

variable [Fintype ι]

/- English proof (translation)
Use `LinearMap.congr_fun (g := c • (jetLin J ∘ₗ (scaleVar (Sum.elim (fun _ => 1) fun k => w k.1)).toLinearMap)) ((basisMonomials _ K).ext fun m => ?_) Q` and prove the remaining obligations. Rewrite using `[coe_basisMonomials]`. Simplify using `only [LinearMap.smul_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply]`. Rewrite using `[scaleVar_monomial, map_smul, jetLin_monomial, jetLin_monomial, smul_monomial, smul_monomial, smul_eq_mul, smul_eq_mul, Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]`. Simplify using the standard rewrite rules.
-/
theorem jetLin_right (J : (DVar ι a b →₀ ℕ) → K) (w : ι → K) (c : K)
    (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    jetLin (fun m => c * ((m.prod fun v e => w v.1 ^ e) * J m)) Q =
      c • jetLin J (scaleVar (Sum.elim (fun _ => 1) fun k => w k.1) Q) := by
  refine LinearMap.congr_fun (g := c • (jetLin J ∘ₗ (scaleVar (Sum.elim (fun _ => 1) fun k => w k.1)).toLinearMap))
    ((basisMonomials _ K).ext fun m => ?_) Q
  rw [coe_basisMonomials]
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [scaleVar_monomial, map_smul, jetLin_monomial, jetLin_monomial, smul_monomial, smul_monomial, smul_eq_mul, smul_eq_mul,
    Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]
  simp

/- English proof (translation)
Proceed by induction on `Q using MvPolynomial.induction_on' with`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `monomial m c`. Establish `e : (monomial m c : MvPolynomial _ K) = c • monomial m 1` using `by rw [smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[e, map_smul, map_smul, map_smul, map_smul, scaleVar_monomial, map_smul, jetLin_monomial, scaleVar_monomial, Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]`.

Simplify using the standard rewrite rules.
-/
theorem jetLin_left (J : (DVar ι a b →₀ ℕ) → K) (w : ι → K)
    (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    jetLin J (scaleVar (Sum.elim (fun v => w v.1) fun _ => 1) Q) = scaleVar (fun v => w v.1) (jetLin J Q) := by
  induction Q using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial m c =>
    have e : (monomial m c : MvPolynomial _ K) = c • monomial m 1 := by rw [smul_monomial, smul_eq_mul, mul_one]
    rw [e, map_smul, map_smul, map_smul, map_smul, scaleVar_monomial, map_smul, jetLin_monomial, scaleVar_monomial,
      Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]
    simp

/- English proof (translation)
Simplify using `only [jetMap, LinearMap.comp_apply, AlgHom.toLinearMap_apply]`. Rewrite using `[jetLin_right, subD_scale, jetLin_left]`.
-/
theorem jetMap_scale (J : (DVar ι a b →₀ ℕ) → K) (w : ι → K) (c : K) (n : ι → ℕ) (P : Pol K ι a) :
    jetMap (fun m => c * ((m.prod fun v e => w v.1 ^ e) * J m)) n P = c • scaleVar (fun v => w v.1) (jetMap J n P) := by
  simp only [jetMap, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [jetLin_right, subD_scale, jetLin_left]

/- English proof (translation)
Use `conv_lhs => rw [Q.as_sum]`. Use `conv_rhs => rw [Q.as_sum]`. Rewrite using `[map_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite using `[scaleVar_monomial, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type]`.

Use `congr 1`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Establish `h` using `hQ τ (mem_support_iff.mp hm)`. Rewrite `h` using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type, Finset.sum_eq_single τ]`. Rewrite using `[← h]`.

Simplify using `[GlobalTheory.JetDeg.posW, Finset.prod_pow_eq_pow_sum]`. Introduce `x _ hx`. Simplify using `[GlobalTheory.JetDeg.posW, hx]`. Simplify using the standard rewrite rules.
-/
theorem scaleVar_hom [DecidableEq ι] (w : ι → K) (d : ι → ℕ) {Q : Pol K ι b}
    (hQ : ∀ τ, IsWeightedHomogeneous (GlobalTheory.JetDeg.posW b τ) Q (d τ)) :
    scaleVar (fun v => w v.1) Q = (∏ τ, w τ ^ d τ) • Q := by
  conv_lhs => rw [Q.as_sum]
  conv_rhs => rw [Q.as_sum]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [scaleVar_monomial, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h := hQ τ (mem_support_iff.mp hm)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type, Finset.sum_eq_single τ] at h
  · rw [← h]
    simp [GlobalTheory.JetDeg.posW, Finset.prod_pow_eq_pow_sum]
  · intro x _ hx
    simp [GlobalTheory.JetDeg.posW, hx]
  · simp

/- English proof (translation)
Introduce `ι _ a b lam lam' n J w c hV`. Use `LinearMap.ext fun P => ?_` and prove the remaining obligations. Simplify using `only [jetOp, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply]`. Rewrite using `[jetMap_scale, scaleVar_hom w _ fun τ => GlobalTheory.JetDeg.VV_hom lam' τ (hV J P P.2), smul_smul, map_smul]`.
-/
theorem jetOp_scale : ∀ {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ)
    (J : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) → ℂ) (w : ι → ℂ) (c : ℂ), Formalism.L2.Ker.JetInVV ℂ lam lam' n →
    Formalism.L2.Ker.jetOp lam lam' (fun m => c * ((m.prod fun v e => w v.1 ^ e) * J m)) n =
      (c * ∏ τ, w τ ^ (∑ i, (lam' τ).natW i)) • Formalism.L2.Ker.jetOp lam lam' J n := by
  classical
  intro ι _ a b lam lam' n J w c hV
  refine LinearMap.ext fun P => ?_
  simp only [jetOp, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply]
  rw [jetMap_scale, scaleVar_hom w _ fun τ => GlobalTheory.JetDeg.VV_hom lam' τ (hV J P P.2), smul_smul, map_smul]

end GlobalTheory.JetCharScale

end
