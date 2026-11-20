import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobeniusTwistedHilbertNinetyAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.NormFin

open Polynomial

/- English proof (translation)
Introduce `F₀ F₁ _ _ _ _ _ sb hsb f hf hfix h0`. Use `set d := Module.finrank F₀ F₁ with hd`. Set `s : F₁ ≃+* F₁` to `(sb : F₁ ≃+* F₁)`. Establish `hI : Ideal.span {f} = (Ideal.span {f}).map (Polynomial.mapEquiv s : F₁[X] ≃+* F₁[X])`. Rewrite using `[Ideal.map_span, Set.image_singleton]`.

Use `congr 2`. Conclude with `hfix.symm`. Set `τ : AdjoinRoot f ≃+* AdjoinRoot f` to `Ideal.quotientEquiv (Ideal.span {f}) (Ideal.span {f}) (Polynomial.mapEquiv s) hI`. Establish `hτ : ∀ p : F₁[X], τ (AdjoinRoot.mk f p) = AdjoinRoot.mk f (p.map (sb : F₁ →+* F₁))`. Introduce `p`.

Both sides reduce to the same expression. Establish `hit : ∀ (i : ℕ) (p : F₁[X]), (⇑τ)^[i] (AdjoinRoot.mk f p) = AdjoinRoot.mk f (p.map ((sb : F₁ →+* F₁) ^ i))`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`.

Introduce `p`. Rewrite using `[pow_zero]`. Use `show _ = AdjoinRoot.mk f (p.map (RingHom.id F₁))`. Rewrite using `[Polynomial.map_id]`. Both sides reduce to the same expression.

Consider the case `succ i ih`. Introduce `p`. Rewrite using `[Function.iterate_succ_apply', ih, hτ, Polynomial.map_map, pow_succ']`. Both sides reduce to the same expression. Establish `hcard : Fintype.card F₁ = Fintype.card F₀ ^ d` using `Module.card_eq_pow_finrank`.

Establish `hpowd : ((sb : F₁ →+* F₁) ^ d) = RingHom.id F₁`. Use extensionality with `z`. Establish `: ∀ i : ℕ, ((sb : F₁ →+* F₁) ^ i) z = z ^ (Fintype.card F₀ ^ i)`. Introduce `i`. Proceed by induction on `i with`.

Consider the case `zero => rw [pow_zero, pow_zero, pow_one]`. Both sides reduce to the same expression. Consider the case `succ i ih`. Rewrite using `[pow_succ']`. Express the relevant statement in the definitionally equal form `sb (((sb : F₁ →+* F₁) ^ i) z) = _`.

Rewrite using `[ih, hsb, ← pow_mul, ← pow_succ]`. Rewrite using `[this, ← hcard, FiniteField.pow_card]`. Both sides reduce to the same expression. Establish `hunit : IsUnit (AdjoinRoot.root f)`. Choose the witnesses or unpack the hypotheses as in `⟨q, hq⟩ : X ∣ f - C (f.coeff 0) := by`.

Rewrite using `[Polynomial.X_dvd_iff]`. Simplify using the standard rewrite rules. Establish `h` using `congrArg (AdjoinRoot.mk f) hq`. Rewrite `h` using `[map_sub, AdjoinRoot.mk_self, map_mul, AdjoinRoot.mk_X, zero_sub]`. Use `IsUnit.of_mul_eq_one (AdjoinRoot.mk f q * AdjoinRoot.of f (-(f.coeff 0)⁻¹)) ?_` and prove the remaining obligations.

Rewrite using `[← mul_assoc, ← h, AdjoinRoot.mk_C, ← map_neg, ← map_mul, neg_mul_neg, mul_inv_cancel₀ h0, map_one]`. Use `haveI : Module.Finite F₁ (AdjoinRoot f) := (AdjoinRoot.powerBasis' hf).finite`. Use `haveI : Finite (AdjoinRoot f) := Module.finite_of_finite F₁`. Take `⟨y, hy⟩` from `UpperTheory.Gal.InertialTypesAlt.L.normFin F₀ F₁ sb hsb (AdjoinRoot f) τ (by`. Introduce `z`.

Rewrite using `[AdjoinRoot.algebraMap_eq, AdjoinRoot.of, RingHom.comp_apply, hτ, Polynomial.map_C]`. Use the proof step `rfl)`. Use the proof step `(by`. Introduce `x`. Take `⟨p, rfl⟩` from `AdjoinRoot.mk_surjective x`.

Rewrite using `[hit, hpowd, Polynomial.map_id])`. Use the proof step `(AdjoinRoot.root f) hunit`. Use the proof step `(by`. Rewrite using `[← AdjoinRoot.mk_X, hτ, Polynomial.map_X])`. Take `⟨g, rfl⟩` from `AdjoinRoot.mk_surjective y`.

Use `⟨g, ?_⟩` and prove the remaining obligations. Rewrite using `[← AdjoinRoot.mk_eq_zero, map_sub, AdjoinRoot.mk_X, sub_eq_zero, map_prod, ← hy]`. Unfold `UpperTheory.Gal.InertialTypesAlt.L.itN`. Conclude with `Finset.prod_congr rfl fun i _ => (hit i g).symm`.
-/
theorem UpperTheory.exists_frobeniusTwistedNorm_dvd_sub_X :
    ∀ (F₀ F₁ : Type) [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁] [Algebra F₀ F₁] (sb : F₁ ≃ₐ[F₀] F₁), (∀ z : F₁, sb z = z ^ Fintype.card F₀) → ∀ f : F₁[X], f.Monic → f.map (sb : F₁ →+* F₁) = f → f.coeff 0 ≠ 0 → ∃ g : F₁[X], f ∣ ∏ i ∈ Finset.range (Module.finrank F₀ F₁), g.map ((sb : F₁ →+* F₁) ^ i) - X := by
  intro F₀ F₁ _ _ _ _ _ sb hsb f hf hfix h0
  classical
  set d := Module.finrank F₀ F₁ with hd
  let s : F₁ ≃+* F₁ := (sb : F₁ ≃+* F₁)
  have hI : Ideal.span {f} = (Ideal.span {f}).map (Polynomial.mapEquiv s : F₁[X] ≃+* F₁[X]) := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    exact hfix.symm
  let τ : AdjoinRoot f ≃+* AdjoinRoot f :=
    Ideal.quotientEquiv (Ideal.span {f}) (Ideal.span {f}) (Polynomial.mapEquiv s) hI
  have hτ : ∀ p : F₁[X], τ (AdjoinRoot.mk f p) = AdjoinRoot.mk f (p.map (sb : F₁ →+* F₁)) := by
    intro p
    rfl
  have hit : ∀ (i : ℕ) (p : F₁[X]),
      (⇑τ)^[i] (AdjoinRoot.mk f p) = AdjoinRoot.mk f (p.map ((sb : F₁ →+* F₁) ^ i)) := by
    intro i
    induction i with
    | zero =>
      intro p
      rw [pow_zero]
      show _ = AdjoinRoot.mk f (p.map (RingHom.id F₁))
      rw [Polynomial.map_id]
      rfl
    | succ i ih =>
      intro p
      rw [Function.iterate_succ_apply', ih, hτ, Polynomial.map_map, pow_succ']
      rfl
  have hcard : Fintype.card F₁ = Fintype.card F₀ ^ d := Module.card_eq_pow_finrank
  have hpowd : ((sb : F₁ →+* F₁) ^ d) = RingHom.id F₁ := by
    ext z
    have : ∀ i : ℕ, ((sb : F₁ →+* F₁) ^ i) z = z ^ (Fintype.card F₀ ^ i) := by
      intro i
      induction i with
      | zero => rw [pow_zero, pow_zero, pow_one]; rfl
      | succ i ih =>
        rw [pow_succ']
        change sb (((sb : F₁ →+* F₁) ^ i) z) = _
        rw [ih, hsb, ← pow_mul, ← pow_succ]
    rw [this, ← hcard, FiniteField.pow_card]
    rfl
  have hunit : IsUnit (AdjoinRoot.root f) := by
    obtain ⟨q, hq⟩ : X ∣ f - C (f.coeff 0) := by
      rw [Polynomial.X_dvd_iff]
      simp
    have h := congrArg (AdjoinRoot.mk f) hq
    rw [map_sub, AdjoinRoot.mk_self, map_mul, AdjoinRoot.mk_X, zero_sub] at h
    refine IsUnit.of_mul_eq_one (AdjoinRoot.mk f q * AdjoinRoot.of f (-(f.coeff 0)⁻¹)) ?_
    rw [← mul_assoc, ← h, AdjoinRoot.mk_C, ← map_neg, ← map_mul, neg_mul_neg,
      mul_inv_cancel₀ h0, map_one]
  haveI : Module.Finite F₁ (AdjoinRoot f) := (AdjoinRoot.powerBasis' hf).finite
  haveI : Finite (AdjoinRoot f) := Module.finite_of_finite F₁
  obtain ⟨y, hy⟩ := UpperTheory.Gal.InertialTypesAlt.L.normFin F₀ F₁ sb hsb (AdjoinRoot f) τ
    (by
      intro z
      rw [AdjoinRoot.algebraMap_eq, AdjoinRoot.of, RingHom.comp_apply, hτ, Polynomial.map_C]
      rfl)
    (by
      intro x
      obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
      rw [hit, hpowd, Polynomial.map_id])
    (AdjoinRoot.root f) hunit
    (by
      rw [← AdjoinRoot.mk_X, hτ, Polynomial.map_X])
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective y
  refine ⟨g, ?_⟩
  rw [← AdjoinRoot.mk_eq_zero, map_sub, AdjoinRoot.mk_X, sub_eq_zero, map_prod, ← hy]
  unfold UpperTheory.Gal.InertialTypesAlt.L.itN
  exact Finset.prod_congr rfl fun i _ => (hit i g).symm
