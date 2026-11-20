import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace FibreIncompressibility

variable {S : Type} [CommRing S]
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

/- English proof (translation)
Simplify using `only [aeval_def, eval₂_eq', Finset.mul_sum]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Establish `h1 : ∏ p, (c p.1 * z p) ^ d p = (∏ p, c p.1 ^ d p) * ∏ p, z p ^ d p`. Rewrite using `[← Finset.prod_mul_distrib]`. Repeatedly rewrite using `[mul_pow]`.

Establish `h2 : ∏ p : (Σ k, ι' k), c p.1 ^ d p = ∏ k, c k ^ a k`. Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show ∏ y, c k ^ d ⟨k, y⟩ = _`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hg d hd k]`.

Rewrite using `[h1, h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem aeval_scale {A : Type} [CommRing A] [Algebra S A] {g : MRingOver S ι'} {a : K' → ℕ}
    (hg : IsMultiHomog g a) (c : K' → A) (z : (Σ k, ι' k) → A) :
    aeval (fun p => c p.1 * z p) g = (∏ k, c k ^ a k) * aeval z g := by
  simp only [aeval_def, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have h1 : ∏ p, (c p.1 * z p) ^ d p = (∏ p, c p.1 ^ d p) * ∏ p, z p ^ d p := by
    rw [← Finset.prod_mul_distrib]
    simp_rw [mul_pow]
  have h2 : ∏ p : (Σ k, ι' k), c p.1 ^ d p = ∏ k, c k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ y, c k ^ d ⟨k, y⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hg d hd k]
  rw [h1, h2]
  ring

/- English proof (translation)
Establish `hterm : ∀ d : σ →₀ ℕ, ((C : A →+* MvPolynomial σ A).comp f) (coeff d P) * ∏ k, (X k * C (b k)) ^ d k = monomial d (f (coeff d P) * ∏ k, b k ^ d k)`. Introduce `d`. Establish `hX : ∏ k, (X k : MvPolynomial σ A) ^ d k = monomial d 1`. Rewrite using `[monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]`. Establish `hC : ∏ k, (C (b k) : MvPolynomial σ A) ^ d k = C (∏ k, b k ^ d k)`.

Simplify using `only [map_prod, map_pow]`. Rewrite using `[RingHom.comp_apply]`. Repeatedly rewrite using `[mul_pow]`. Rewrite using `[Finset.prod_mul_distrib, hX, hC, mul_comm (monomial d 1), ← mul_assoc, ← C_mul, C_mul_monomial, mul_one]`. Rewrite using `[eval₂_eq']`.

Repeatedly rewrite using `[hterm, coeff_sum, coeff_monomial]`. Rewrite using `[Finset.sum_ite_eq']`. Use `split_ifs with hm`. Both sides reduce to the same expression. Rewrite using `[notMem_support_iff.mp hm, map_zero, zero_mul]`.
-/
theorem coeff_eval₂_scale {σ R A : Type} [Fintype σ] [CommRing R] [CommRing A] (f : R →+* A) (b : σ → A)
    (P : MvPolynomial σ R) (m : σ →₀ ℕ) :
    coeff m (eval₂ ((C : A →+* MvPolynomial σ A).comp f) (fun k => X k * C (b k)) P) =
      f (coeff m P) * ∏ k, b k ^ m k := by
  classical
  have hterm : ∀ d : σ →₀ ℕ, ((C : A →+* MvPolynomial σ A).comp f) (coeff d P) *
      ∏ k, (X k * C (b k)) ^ d k = monomial d (f (coeff d P) * ∏ k, b k ^ d k) := by
    intro d
    have hX : ∏ k, (X k : MvPolynomial σ A) ^ d k = monomial d 1 := by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    have hC : ∏ k, (C (b k) : MvPolynomial σ A) ^ d k = C (∏ k, b k ^ d k) := by
      simp only [map_prod, map_pow]
    rw [RingHom.comp_apply]
    simp_rw [mul_pow]
    rw [Finset.prod_mul_distrib, hX, hC, mul_comm (monomial d 1), ← mul_assoc, ← C_mul, C_mul_monomial, mul_one]
  rw [eval₂_eq']
  simp_rw [hterm, coeff_sum, coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [notMem_support_iff.mp hm, map_zero, zero_mul]

open Classical in

def scaleWt (κ : K → K') (A : Type) [CommRing A] (k' : K') : MvPolynomial (FibreBlock κ) A :=
  if h : k' ∈ Set.range κ then 1 else X ⟨k', h⟩

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Use `set φ := (rename v : MRingOver S ι →ₐ[S] MRingOver S ι').toRingHom with hφ`. Use `set j := Ideal.quotientMap V' φ le_rfl with hj`. Set `_` to `j.toAlgebra`. Use `set y : FibreBlock κ → MRingOver S ι' ⧸ V' := fun k => Ideal.Quotient.mk V' (X ⟨k.1, i k⟩) with hy`. Set `z : (Σ k, ι' k) → MvPolynomial (FibreBlock κ) (MRingOver S ι' ⧸ V')` to `fun q => C (Ideal.Quotient.mk V' (X q))`.

Set `Θ : MRingOver S ι' →ₐ[S] MvPolynomial (FibreBlock κ) (MRingOver S ι' ⧸ V')` to `aeval fun q => scaleWt κ _ q.1 * z q`. Establish `hz : ∀ f : MRingOver S ι', aeval z f = C (Ideal.Quotient.mk V' f)`. Introduce `f`. Establish `e : (aeval z : MRingOver S ι' →ₐ[S] MvPolynomial (FibreBlock κ) (MRingOver S ι' ⧸ V')) = (IsScalarTower.toAlgHom S (MRingOver S ι' ⧸ V') (MvPolynomial (FibreBlock κ) (MRingOver S ι' ⧸ V'))).comp (Ideal.Quotient.mkₐ S V')` using `algHom_ext fun q => by simp [z]`. Rewrite using `[e]`.

Simplify using the standard rewrite rules. Establish `hkill : ∀ f ∈ V', Θ f = 0`. Take `⟨T, hT, hVT⟩` from `hV'`. Establish `hle : Ideal.span T ≤ RingHom.ker (Θ : MRingOver S ι' →+* MvPolynomial (FibreBlock κ) (MRingOver S ι' ⧸ V'))`. Rewrite using `[Ideal.span_le]`.

Introduce `f hf`. Take `⟨a, ha⟩` from `hT f hf`. Establish `hfV : f ∈ V'` using `by rw [hVT]; exact Ideal.subset_span hf`. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker]`. Use `show aeval (fun q => scaleWt κ _ q.1 * z q) f = 0`.

Use `(aeval_scale ha (scaleWt κ (MRingOver S ι' ⧸ V')) z).trans ?_` and prove the remaining obligations. Rewrite using `[hz, Ideal.Quotient.eq_zero_iff_mem.mpr hfV, map_zero, mul_zero]`. Introduce `f hf`. Rewrite `hf` using `[hVT]`. Conclude with `RingHom.mem_ker.mp (hle hf)`.

Set `θ : MRingOver S ι' ⧸ V' →+* MvPolynomial (FibreBlock κ) (MRingOver S ι' ⧸ V')` to `Ideal.Quotient.lift V' (Θ : MRingOver S ι' →+* _) hkill`. Establish `hθj : ∀ r, θ (j r) = C (j r)`. Introduce `r`. Take `⟨g, rfl⟩` from `Ideal.Quotient.mk_surjective r`. Rewrite using `[hj, Ideal.quotientMap_mk]`.

Use `show Θ (rename v g) = C (Ideal.Quotient.mk V' (rename v g))`. Establish `e : (fun p => scaleWt κ (MRingOver S ι' ⧸ V') (v p).1 * z (v p)) = z ∘ v`. Use function extensionality and compare the values at `p`. Establish `: (v p).1 ∈ Set.range κ` using `⟨p.1, (hv.2.2.1 p).symm⟩`. Simplify using `[scaleWt, this]`.

Use `show aeval (fun q => scaleWt κ _ q.1 * z q) (rename v g) = _`. Rewrite using `[aeval_rename, Function.comp_def, e, ← aeval_rename, hz]`. Establish `hθy : ∀ k, θ (y k) = X k * C (y k)`. Introduce `k`. Use `show aeval (fun q => scaleWt κ _ q.1 * z q) (X ⟨k.1, i k⟩ : MRingOver S ι') = _`.

Rewrite using `[aeval_X]`. Simplify using `[scaleWt, k.2, z, y]`. Establish `hcomp : θ.comp (aeval y : MvPolynomial (FibreBlock κ) (MRingOver S ι ⧸ V'.comap φ) →ₐ[_] _).toRingHom = eval₂Hom ((C : _ →+* MvPolynomial (FibreBlock κ) (MRingOver S ι' ⧸ V')).comp j) (fun k => X k * C (y k))`. Use `ringHom_ext (fun r => ?_) (fun k => ?_)` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, coe_eval₂Hom, eval₂_C]`.

Conclude with `hθj r`. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, coe_eval₂Hom, eval₂_X]`. Conclude with `hθy k`. Establish `hjinj : Function.Injective j` using `Ideal.quotientMap_injective`. Establish `hyprod : ∀ m : FibreBlock κ →₀ ℕ, ∏ k, y k ^ m k ≠ 0`.

Introduce `m`. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `k _`. Use `pow_ne_zero _ fun h => hi k ?_` and prove the remaining obligations. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp h`.

Rewrite using `[algebraicIndependent_iff]`. Introduce `P hP`. Establish `h0 : eval₂ ((C : _ →+* MvPolynomial (FibreBlock κ) (MRingOver S ι' ⧸ V')).comp j) (fun k => X k * C (y k)) P = 0`. Use `congrArg (fun f => f P) hcomp` as an intermediate fact. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_eval₂Hom] at this`.

Rewrite using `[← this, hP, map_zero]`. Use extensionality with `m`. Establish `hc` using `coeff_eval₂_scale j y P m`. Rewrite `hc` using `[h0, coeff_zero]`. Rewrite using `[coeff_zero]`.

Conclude with `hjinj ((mul_eq_zero.mp hc.symm).resolve_right (hyprod m) |>.trans (map_zero j).symm)`.
-/
theorem algebraicIndependent_forgotten {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    (V' : Ideal (MRingOver S ι')) [V'.IsPrime] (hV' : IsMultiHomogIdeal V') (i : ∀ k : FibreBlock κ, ι' k.1)
    (hi : ∀ k : FibreBlock κ, (X ⟨k.1, i k⟩ : MRingOver S ι') ∉ V') :
    letI := (Ideal.quotientMap V' (rename v : MRingOver S ι →ₐ[S] MRingOver S ι').toRingHom le_rfl).toAlgebra
    AlgebraicIndependent (MRingOver S ι ⧸ V'.comap (rename v : MRingOver S ι →ₐ[S] MRingOver S ι').toRingHom)
      (fun k : FibreBlock κ => Ideal.Quotient.mk V' (X ⟨k.1, i k⟩ : MRingOver S ι')) := by
  classical
  set φ := (rename v : MRingOver S ι →ₐ[S] MRingOver S ι').toRingHom with hφ
  set j := Ideal.quotientMap V' φ le_rfl with hj
  let _ := j.toAlgebra
  set y : FibreBlock κ → MRingOver S ι' ⧸ V' := fun k => Ideal.Quotient.mk V' (X ⟨k.1, i k⟩) with hy
  let z : (Σ k, ι' k) → MvPolynomial (FibreBlock κ) (MRingOver S ι' ⧸ V') :=
    fun q => C (Ideal.Quotient.mk V' (X q))
  let Θ : MRingOver S ι' →ₐ[S] MvPolynomial (FibreBlock κ) (MRingOver S ι' ⧸ V') :=
    aeval fun q => scaleWt κ _ q.1 * z q
  have hz : ∀ f : MRingOver S ι', aeval z f = C (Ideal.Quotient.mk V' f) := by
    intro f
    have e : (aeval z : MRingOver S ι' →ₐ[S] MvPolynomial (FibreBlock κ) (MRingOver S ι' ⧸ V')) =
        (IsScalarTower.toAlgHom S (MRingOver S ι' ⧸ V') (MvPolynomial (FibreBlock κ) (MRingOver S ι' ⧸ V'))).comp
          (Ideal.Quotient.mkₐ S V') :=
      algHom_ext fun q => by simp [z]
    rw [e]
    simp
  have hkill : ∀ f ∈ V', Θ f = 0 := by
    obtain ⟨T, hT, hVT⟩ := hV'
    have hle : Ideal.span T ≤ RingHom.ker (Θ : MRingOver S ι' →+* MvPolynomial (FibreBlock κ) (MRingOver S ι' ⧸ V')) := by
      rw [Ideal.span_le]
      intro f hf
      obtain ⟨a, ha⟩ := hT f hf
      have hfV : f ∈ V' := by rw [hVT]; exact Ideal.subset_span hf
      rw [SetLike.mem_coe, RingHom.mem_ker]
      show aeval (fun q => scaleWt κ _ q.1 * z q) f = 0
      refine (aeval_scale ha (scaleWt κ (MRingOver S ι' ⧸ V')) z).trans ?_
      rw [hz, Ideal.Quotient.eq_zero_iff_mem.mpr hfV, map_zero, mul_zero]
    intro f hf
    rw [hVT] at hf
    exact RingHom.mem_ker.mp (hle hf)
  let θ : MRingOver S ι' ⧸ V' →+* MvPolynomial (FibreBlock κ) (MRingOver S ι' ⧸ V') :=
    Ideal.Quotient.lift V' (Θ : MRingOver S ι' →+* _) hkill
  have hθj : ∀ r, θ (j r) = C (j r) := by
    intro r
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [hj, Ideal.quotientMap_mk]
    show Θ (rename v g) = C (Ideal.Quotient.mk V' (rename v g))
    have e : (fun p => scaleWt κ (MRingOver S ι' ⧸ V') (v p).1 * z (v p)) = z ∘ v := by
      funext p
      have : (v p).1 ∈ Set.range κ := ⟨p.1, (hv.2.2.1 p).symm⟩
      simp [scaleWt, this]
    show aeval (fun q => scaleWt κ _ q.1 * z q) (rename v g) = _
    rw [aeval_rename, Function.comp_def, e, ← aeval_rename, hz]
  have hθy : ∀ k, θ (y k) = X k * C (y k) := by
    intro k
    show aeval (fun q => scaleWt κ _ q.1 * z q) (X ⟨k.1, i k⟩ : MRingOver S ι') = _
    rw [aeval_X]
    simp [scaleWt, k.2, z, y]
  have hcomp : θ.comp (aeval y : MvPolynomial (FibreBlock κ) (MRingOver S ι ⧸ V'.comap φ) →ₐ[_] _).toRingHom =
      eval₂Hom ((C : _ →+* MvPolynomial (FibreBlock κ) (MRingOver S ι' ⧸ V')).comp j) (fun k => X k * C (y k)) := by
    refine ringHom_ext (fun r => ?_) (fun k => ?_)
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, coe_eval₂Hom, eval₂_C]
      exact hθj r
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, coe_eval₂Hom, eval₂_X]
      exact hθy k
  have hjinj : Function.Injective j := Ideal.quotientMap_injective
  have hyprod : ∀ m : FibreBlock κ →₀ ℕ, ∏ k, y k ^ m k ≠ 0 := by
    intro m
    rw [Finset.prod_ne_zero_iff]
    intro k _
    refine pow_ne_zero _ fun h => hi k ?_
    exact Ideal.Quotient.eq_zero_iff_mem.mp h
  rw [algebraicIndependent_iff]
  intro P hP
  have h0 : eval₂ ((C : _ →+* MvPolynomial (FibreBlock κ) (MRingOver S ι' ⧸ V')).comp j)
      (fun k => X k * C (y k)) P = 0 := by
    have := congrArg (fun f => f P) hcomp
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_eval₂Hom] at this
    rw [← this, hP, map_zero]
  ext m
  have hc := coeff_eval₂_scale j y P m
  rw [h0, coeff_zero] at hc
  rw [coeff_zero]
  exact hjinj ((mul_eq_zero.mp hc.symm).resolve_right (hyprod m) |>.trans (map_zero j).symm)

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Use `set φ := (rename v : MRingOver S ι →ₐ[S] MRingOver S ι').toRingHom with hφ`. Use `set j := Ideal.quotientMap V' φ le_rfl with hj`. Set `_` to `j.toAlgebra`. Use `choose i hi using fun k : FibreBlock κ => hrel k.1`. Establish `hind` using `algebraicIndependent_forgotten hv V' hV' i hi`.

Establish `: IsScalarTower S (MRingOver S ι ⧸ V'.comap φ) (MRingOver S ι' ⧸ V')`. Use `IsScalarTower.of_algebraMap_eq (R := S) (S := MRingOver S ι ⧸ V'.comap φ) (A := MRingOver S ι' ⧸ V') fun r => ?_` and prove the remaining obligations. Rewrite using `[RingHom.algebraMap_toAlgebra, hj, ← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, Ideal.quotientMap_mk]`. Use `congr 1`. Conclude with `(AlgHom.commutes (rename v : MRingOver S ι →ₐ[S] MRingOver S ι') r).symm`.

Establish `: FaithfulSMul S (MRingOver S ι ⧸ V'.comap φ)` using `(faithfulSMul_iff_algebraMap_injective _ _).mpr hinj`. Establish `: FaithfulSMul (MRingOver S ι ⧸ V'.comap φ) (MRingOver S ι' ⧸ V')` using `(faithfulSMul_iff_algebraMap_injective _ _).mpr Ideal.quotientMap_injective`. Rewrite using `[← trdeg_add_eq S (MRingOver S ι ⧸ V'.comap φ) (A := MRingOver S ι' ⧸ V')]`. Use `gcongr`. Rewrite using `[← Cardinal.mk_fintype]`.

Conclude with `hind.cardinalMk_le_trdeg`.
-/
theorem trdeg_add_card_le [Nontrivial S] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    (V' : Ideal (MRingOver S ι')) [V'.IsPrime] (hV' : IsMultiHomogIdeal V') (hrel : IsRelevant V')
    (hinj : Function.Injective (algebraMap S
      (MRingOver S ι ⧸ V'.comap (rename v : MRingOver S ι →ₐ[S] MRingOver S ι').toRingHom))) :
    Algebra.trdeg S (MRingOver S ι ⧸ V'.comap (rename v : MRingOver S ι →ₐ[S] MRingOver S ι').toRingHom) +
        Fintype.card (FibreBlock κ) ≤ Algebra.trdeg S (MRingOver S ι' ⧸ V') := by
  classical
  set φ := (rename v : MRingOver S ι →ₐ[S] MRingOver S ι').toRingHom with hφ
  set j := Ideal.quotientMap V' φ le_rfl with hj
  let _ := j.toAlgebra
  choose i hi using fun k : FibreBlock κ => hrel k.1
  have hind := algebraicIndependent_forgotten hv V' hV' i hi
  have : IsScalarTower S (MRingOver S ι ⧸ V'.comap φ) (MRingOver S ι' ⧸ V') := by
    refine IsScalarTower.of_algebraMap_eq (R := S) (S := MRingOver S ι ⧸ V'.comap φ)
      (A := MRingOver S ι' ⧸ V') fun r => ?_
    rw [RingHom.algebraMap_toAlgebra, hj, ← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap,
      Ideal.quotientMap_mk]
    congr 1
    exact (AlgHom.commutes (rename v : MRingOver S ι →ₐ[S] MRingOver S ι') r).symm
  have : FaithfulSMul S (MRingOver S ι ⧸ V'.comap φ) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : FaithfulSMul (MRingOver S ι ⧸ V'.comap φ) (MRingOver S ι' ⧸ V') :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Ideal.quotientMap_injective
  rw [← trdeg_add_eq S (MRingOver S ι ⧸ V'.comap φ) (A := MRingOver S ι' ⧸ V')]
  gcongr
  rw [← Cardinal.mk_fintype]
  exact hind.cardinalMk_le_trdeg

end FibreIncompressibility

end GroundTheory.Heights₂.Heights.ForSecondHalf
