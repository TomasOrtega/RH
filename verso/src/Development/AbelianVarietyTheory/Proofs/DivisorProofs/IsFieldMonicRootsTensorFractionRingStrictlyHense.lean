import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationAtPrimeIsDomainIsIntegrallyClos
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FlatMapMaximalIdealIsSeparable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgClosedFractionRingOfMonicPolynomialsHaveRooStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

open Polynomial

namespace AICStalk

/- English proof (translation)
Rewrite using `[isIntegrallyClosed_iff (FractionRing A)]`. Introduce and unpack `x ⟨p, hpm, hp⟩`. It suffices to establish `H : ∀ n : ℕ, ∀ p : A[X], p.Monic → p.natDegree = n → aeval x p = 0 → ∃ y, algebraMap A (FractionRing A) y = x by`. Conclude with `H _ p hpm rfl (by rwa [aeval_def])`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero`. Introduce `p hpm hdeg hp`. Rewrite `hp` using `[Polynomial.eq_one_of_monic_natDegree_zero hpm hdeg]`. Simplify using `at hp`.

Consider the case `succ n ih`. Introduce `p hpm hdeg hp`. Take `⟨a, ha⟩` from `h p hpm (by omega)`. Establish `hq : (X - C a) * (p /ₘ (X - C a)) = p` using `mul_divByMonic_eq_iff_isRoot.mpr ha`. Establish `hqm : (p /ₘ (X - C a)).Monic` using `Polynomial.Monic.of_mul_monic_left (monic_X_sub_C a) (by rw [hq]; exact hpm)`.

Establish `hqd : (p /ₘ (X - C a)).natDegree = n`. Rewrite using `[natDegree_divByMonic p (monic_X_sub_C a), natDegree_X_sub_C, hdeg]`. Both sides reduce to the same expression. Rewrite `hp` using `[← hq, map_mul]`. Simplify using `only [map_sub, aeval_X, aeval_C] at hp`.

Break down `mul_eq_zero.mp hp with h1 | h1` into its components or cases. Conclude with `⟨a, (sub_eq_zero.mp h1).symm⟩`. Conclude with `ih _ hqm hqd h1`.
-/
theorem isIntegrallyClosed_of_aic {A : Type} [CommRing A] [IsDomain A] (h : GlobalTheory.EtC.AIC A) :
    IsIntegrallyClosed A := by
  rw [isIntegrallyClosed_iff (FractionRing A)]
  rintro x ⟨p, hpm, hp⟩
  suffices H : ∀ n : ℕ, ∀ p : A[X], p.Monic → p.natDegree = n → aeval x p = 0 →
      ∃ y, algebraMap A (FractionRing A) y = x by
    exact H _ p hpm rfl (by rwa [aeval_def])
  intro n
  induction n with
  | zero =>
    intro p hpm hdeg hp
    rw [Polynomial.eq_one_of_monic_natDegree_zero hpm hdeg] at hp
    simp at hp
  | succ n ih =>
    intro p hpm hdeg hp
    obtain ⟨a, ha⟩ := h p hpm (by omega)
    have hq : (X - C a) * (p /ₘ (X - C a)) = p := mul_divByMonic_eq_iff_isRoot.mpr ha
    have hqm : (p /ₘ (X - C a)).Monic := Polynomial.Monic.of_mul_monic_left (monic_X_sub_C a) (by rw [hq]; exact hpm)
    have hqd : (p /ₘ (X - C a)).natDegree = n := by
      rw [natDegree_divByMonic p (monic_X_sub_C a), natDegree_X_sub_C, hdeg]; rfl
    rw [← hq, map_mul] at hp
    simp only [map_sub, aeval_X, aeval_C] at hp
    rcases mul_eq_zero.mp hp with h1 | h1
    · exact ⟨a, (sub_eq_zero.mp h1).symm⟩
    · exact ih _ hqm hqd h1

/- English proof (translation)
Introduce `p hpm hdeg`. Establish `hm : (p.map (e.symm : S →+* R)).Monic` using `hpm.map _`. Establish `hd : (p.map (e.symm : S →+* R)).natDegree = p.natDegree` using `natDegree_map_eq_of_injective e.symm.injective p`. Take `⟨a, ha⟩` from `h _ hm (hd ▸ hdeg)`. Use `⟨e a, ?_⟩` and prove the remaining obligations.

Establish `hp : p = (p.map (e.symm : S →+* R)).map (e : R →+* S)`. Rewrite using `[Polynomial.map_map]`. Use extensionality with `n`. Simplify using the standard rewrite rules. Rewrite using `[hp, Polynomial.eval_map, show e a = (e : R →+* S) a from rfl, Polynomial.eval₂_at_apply, ha, map_zero]`.
-/
theorem aic_of_ringEquiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (h : GlobalTheory.EtC.AIC R) :
    GlobalTheory.EtC.AIC S := by
  intro p hpm hdeg
  have hm : (p.map (e.symm : S →+* R)).Monic := hpm.map _
  have hd : (p.map (e.symm : S →+* R)).natDegree = p.natDegree :=
    natDegree_map_eq_of_injective e.symm.injective p
  obtain ⟨a, ha⟩ := h _ hm (hd ▸ hdeg)
  refine ⟨e a, ?_⟩
  have hp : p = (p.map (e.symm : S →+* R)).map (e : R →+* S) := by
    rw [Polynomial.map_map]; ext n; simp
  rw [hp, Polynomial.eval_map, show e a = (e : R →+* S) a from rfl, Polynomial.eval₂_at_apply, ha, map_zero]

/- English proof (translation)
Introduce `p _ hdeg`. Take `⟨a, ha⟩` from `IsAlgClosed.exists_root p (by`. Rewrite using `[degree_eq_natDegree (ne_zero_of_natDegree_gt hdeg)]`. Conclude with `hdeg.ne')` after adjusting the coercions. Conclude with `⟨a, ha⟩`.
-/
theorem aic_of_isAlgClosed (K : Type) [Field K] [IsAlgClosed K] : GlobalTheory.EtC.AIC K := by
  intro p _ hdeg
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p (by
    rw [degree_eq_natDegree (ne_zero_of_natDegree_gt hdeg)]; exact_mod_cast hdeg.ne')
  exact ⟨a, ha⟩

/- English proof (translation)
Use `haveI : Module.Flat A O := GlobalTheory.IndEtaleLocal.flat_of_isIndEtale h`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Assume the negation of the conclusion as `ha0`. Establish `hmem : (1 : O) ∈ Submodule.torsion A O`.

Rewrite using `[Submodule.mem_torsion_iff]`. Conclude with `⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha0⟩, by simp [Algebra.smul_def, ha]⟩`. Rewrite `hmem` using `[Module.Flat.torsion_eq_bot]`. Conclude with `one_ne_zero ((Submodule.mem_bot A).mp hmem)`.
-/
theorem algebraMap_injective_of_indEt {A O : Type} [CommRing A] [IsDomain A] [CommRing O]
    [Nontrivial O] [Algebra A O] (h : GlobalTheory.EtC.IndEt A O) : Function.Injective (algebraMap A O) := by
  haveI : Module.Flat A O := GlobalTheory.IndEtaleLocal.flat_of_isIndEtale h
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  have hmem : (1 : O) ∈ Submodule.torsion A O := by
    rw [Submodule.mem_torsion_iff]
    exact ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha0⟩, by simp [Algebra.smul_def, ha]⟩
  rw [Module.Flat.torsion_eq_bot] at hmem
  exact one_ne_zero ((Submodule.mem_bot A).mp hmem)

/- English proof (translation)
Use `@NoZeroDivisors.to_isDomain O _ _ ⟨fun {x y} hxy => ?_⟩` and prove the remaining obligations. Set `I : Ideal (MvPolynomial (Fin 2) A)` to `Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}`. Use `haveI : Algebra.FinitePresentation A (MvPolynomial (Fin 2) A ⧸ I) := Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton _)`. Set `g : (MvPolynomial (Fin 2) A ⧸ I) →ₐ[A] O` to `Ideal.Quotient.liftₐ I (MvPolynomial.aeval ![x, y]) (by`. Introduce `a ha`.

Take `⟨b, rfl⟩` from `Ideal.mem_span_singleton'.mp ha`. Simplify using `[hxy])`. Take `⟨W, _, _, _, u, v, huv⟩` from `GlobalTheory.IndEtaleLocal.exists_etale_factor h g`. Set `w : Fin 2 → W` to `fun i => u (Ideal.Quotient.mkₐ A I (MvPolynomial.X i))`. Establish `hw : ∀ i, v (w i) = ![x, y] i` using `fun i => by`.

Use `DFunLike.congr_fun huv (Ideal.Quotient.mkₐ A I (MvPolynomial.X i))` as an intermediate fact. Conclude with `this.trans (MvPolynomial.aeval_X _ i)`. Establish `h0 : w 0 * w 1 = 0`. Establish `: Ideal.Quotient.mkₐ A I (MvPolynomial.X 0) * Ideal.Quotient.mkₐ A I (MvPolynomial.X 1) = 0`. Rewrite using `[← map_mul]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)`. Simplify using `only [w, ← map_mul, this, map_zero]`. Set `q : Ideal W` to `(IsLocalRing.maximalIdeal O).comap v`. Use `haveI : q.IsPrime := Ideal.comap_isPrime _ _`. Take `⟨hdom, -⟩` from `GlobalTheory.etale_localization_atPrime_isDomain_isIntegrallyClosed A W q`.

Establish `hq : ∀ t ∈ q.primeCompl, IsUnit (v t)` using `fun t ht => by`. Assume the negation of the conclusion as `hc`. Conclude with `ht (IsLocalRing.mem_maximalIdeal _ |>.mpr hc)`. Establish `hm : algebraMap W (Localization.AtPrime q) (w 0) * algebraMap W (Localization.AtPrime q) (w 1) = 0`. Rewrite using `[← map_mul, h0, map_zero]`.

Break down `mul_eq_zero.mp hm with h1 | h1` into its components or cases. Take `⟨⟨t, ht⟩, hte⟩` from `(IsLocalization.map_eq_zero_iff q.primeCompl _ _).mp h1`. Use `congrArg v hte` as an intermediate fact. Rewrite `this` using `[map_mul, map_zero, hw]`. Conclude with `Or.inl (((hq t ht).mul_right_eq_zero).mp this)`.

Take `⟨⟨t, ht⟩, hte⟩` from `(IsLocalization.map_eq_zero_iff q.primeCompl _ _).mp h1`. Use `congrArg v hte` as an intermediate fact. Rewrite `this` using `[map_mul, map_zero, hw]`. Conclude with `Or.inr (((hq t ht).mul_right_eq_zero).mp this)`.
-/
theorem isDomain_of_indEt {A O : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing O] [IsLocalRing O] [Algebra A O] (h : GlobalTheory.EtC.IndEt A O) : IsDomain O := by
  refine @NoZeroDivisors.to_isDomain O _ _ ⟨fun {x y} hxy => ?_⟩
  let I : Ideal (MvPolynomial (Fin 2) A) := Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}
  haveI : Algebra.FinitePresentation A (MvPolynomial (Fin 2) A ⧸ I) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton _)
  let g : (MvPolynomial (Fin 2) A ⧸ I) →ₐ[A] O :=
    Ideal.Quotient.liftₐ I (MvPolynomial.aeval ![x, y]) (by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp [hxy])
  obtain ⟨W, _, _, _, u, v, huv⟩ := GlobalTheory.IndEtaleLocal.exists_etale_factor h g
  let w : Fin 2 → W := fun i => u (Ideal.Quotient.mkₐ A I (MvPolynomial.X i))
  have hw : ∀ i, v (w i) = ![x, y] i := fun i => by
    have := DFunLike.congr_fun huv (Ideal.Quotient.mkₐ A I (MvPolynomial.X i))
    exact this.trans (MvPolynomial.aeval_X _ i)
  have h0 : w 0 * w 1 = 0 := by
    have : Ideal.Quotient.mkₐ A I (MvPolynomial.X 0) * Ideal.Quotient.mkₐ A I (MvPolynomial.X 1) = 0 := by
      rw [← map_mul]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    simp only [w, ← map_mul, this, map_zero]
  let q : Ideal W := (IsLocalRing.maximalIdeal O).comap v
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨hdom, -⟩ := GlobalTheory.etale_localization_atPrime_isDomain_isIntegrallyClosed A W q
  have hq : ∀ t ∈ q.primeCompl, IsUnit (v t) := fun t ht => by
    by_contra hc
    exact ht (IsLocalRing.mem_maximalIdeal _ |>.mpr hc)
  have hm : algebraMap W (Localization.AtPrime q) (w 0) * algebraMap W (Localization.AtPrime q) (w 1) = 0 := by
    rw [← map_mul, h0, map_zero]
  rcases mul_eq_zero.mp hm with h1 | h1
  · obtain ⟨⟨t, ht⟩, hte⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl _ _).mp h1
    have := congrArg v hte
    rw [map_mul, map_zero, hw] at this
    exact Or.inl (((hq t ht).mul_right_eq_zero).mp this)
  · obtain ⟨⟨t, ht⟩, hte⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl _ _).mp h1
    have := congrArg v hte
    rw [map_mul, map_zero, hw] at this
    exact Or.inr (((hq t ht).mul_right_eq_zero).mp this)

attribute [local instance] Algebra.TensorProduct.rightAlgebra in

/- English proof (translation)
Take `⟨W, _, _, _, u, v, huv⟩` from `GlobalTheory.IndEtaleLocal.exists_etale_factor h (Polynomial.aeval (R := A) o)`. Use `haveI : Algebra.Etale (FractionRing A) (FractionRing A ⊗[A] W) := Algebra.Etale.baseChange A W _`. Use `haveI : Module.Finite (FractionRing A) (FractionRing A ⊗[A] W) := Algebra.FormallyUnramified.finite_of_free _ _`. Use `haveI : Algebra.IsIntegral (FractionRing A) (FractionRing A ⊗[A] W) := Algebra.IsIntegral.of_finite _ _`. Set `χ : W →ₐ[A] O ⊗[A] FractionRing A` to `(Algebra.TensorProduct.includeLeft (S := A)).comp v`.

Set `Χ : FractionRing A ⊗[A] W →ₐ[FractionRing A] O ⊗[A] FractionRing A` to `Algebra.TensorProduct.lift (Algebra.ofId _ _) χ (fun _ _ => Commute.all _ _)`. Establish `hX : Χ (1 ⊗ₜ (u Polynomial.X)) = o ⊗ₜ 1`. Use `DFunLike.congr_fun huv Polynomial.X` as an intermediate fact. Simplify using `only [AlgHom.comp_apply, Polynomial.aeval_X] at this`. Simplify using `[Χ, χ, this]`.

Rewrite using `[← hX]`. Conclude with `(Algebra.IsIntegral.isIntegral _).map Χ`.
-/
theorem isIntegral_tmul_one {A O : Type} [CommRing A] [IsDomain A] [CommRing O] [Algebra A O]
    (h : GlobalTheory.EtC.IndEt A O) (o : O) :
    IsIntegral (FractionRing A) (o ⊗ₜ[A] (1 : FractionRing A)) := by
  obtain ⟨W, _, _, _, u, v, huv⟩ := GlobalTheory.IndEtaleLocal.exists_etale_factor h (Polynomial.aeval (R := A) o)
  haveI : Algebra.Etale (FractionRing A) (FractionRing A ⊗[A] W) := Algebra.Etale.baseChange A W _
  haveI : Module.Finite (FractionRing A) (FractionRing A ⊗[A] W) :=
    Algebra.FormallyUnramified.finite_of_free _ _
  haveI : Algebra.IsIntegral (FractionRing A) (FractionRing A ⊗[A] W) := Algebra.IsIntegral.of_finite _ _
  let χ : W →ₐ[A] O ⊗[A] FractionRing A := (Algebra.TensorProduct.includeLeft (S := A)).comp v
  let Χ : FractionRing A ⊗[A] W →ₐ[FractionRing A] O ⊗[A] FractionRing A :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) χ (fun _ _ => Commute.all _ _)
  have hX : Χ (1 ⊗ₜ (u Polynomial.X)) = o ⊗ₜ 1 := by
    have := DFunLike.congr_fun huv Polynomial.X
    simp only [AlgHom.comp_apply, Polynomial.aeval_X] at this
    simp [Χ, χ, this]
  rw [← hX]
  exact (Algebra.IsIntegral.isIntegral _).map Χ

end AICStalk

open AICStalk in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in

/- English proof (translation)
Introduce `A O _ _ _ _ hA hO h`. Use `haveI := isIntegrallyClosed_of_aic hA`. Take `⟨hH, -⟩` from `hO`. Use `haveI := hH`. Use `haveI := isDomain_of_indEt h`.

Use `haveI : IsAlgClosed (FractionRing A) := GlobalTheory.T.isAlgClosed_fractionRing_of_monic_polynomials_have_roots A hA`. Use `haveI : IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors A)) (O ⊗[A] FractionRing A) := by`. Rewrite using `[Algebra.isLocalization_iff_isPushout (nonZeroDivisors A) (FractionRing A)]`. Use `infer_instance`. Establish `hinj` using `algebraMap_injective_of_indEt h`.

Use `haveI : IsDomain (O ⊗[A] FractionRing A) := IsLocalization.isDomain_of_le_nonZeroDivisors (M := Algebra.algebraMapSubmonoid O (nonZeroDivisors A)) (O ⊗[A] FractionRing A) (by`. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Conclude with `mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero ha)))`. Establish `hall : ∀ x : O ⊗[A] FractionRing A, IsIntegral (FractionRing A) x`. Introduce `x`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact isIntegral_zero`. Consider the case `tmul o k`. Establish `: o ⊗ₜ[A] k = (o ⊗ₜ[A] (1 : FractionRing A)) * algebraMap (FractionRing A) _ k`. Rewrite using `[show algebraMap (FractionRing A) (O ⊗[A] FractionRing A) k = 1 ⊗ₜ k from rfl, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`.

Rewrite using `[this]`. Conclude with `(isIntegral_tmul_one h o).mul isIntegral_algebraMap`. Consider the case `add x y hx hy => exact hx.add hy`. Use `haveI : Algebra.IsIntegral (FractionRing A) (O ⊗[A] FractionRing A) := ⟨hall⟩`. Set `e` to `RingEquiv.ofBijective _ (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := FractionRing A) (K := O ⊗[A] FractionRing A))`.

Conclude with `⟨MulEquiv.isField (Field.toIsField (FractionRing A)) e.symm.toMulEquiv, aic_of_ringEquiv e (aic_of_isAlgClosed _)⟩`.
-/
theorem isField_aic_tensor_fractionRing_of_strictlyHenselian :
    ∀ (A O : Type) [CommRing A] [IsDomain A] [CommRing O] [Algebra A O], GlobalTheory.EtC.AIC A →
      GlobalTheory.EtC.SH O → GlobalTheory.EtC.IndEt A O →
      IsField (O ⊗[A] FractionRing A) ∧ GlobalTheory.EtC.AIC (O ⊗[A] FractionRing A) := by
  intro A O _ _ _ _ hA hO h
  haveI := isIntegrallyClosed_of_aic hA
  obtain ⟨hH, -⟩ := hO
  haveI := hH
  haveI := isDomain_of_indEt h
  haveI : IsAlgClosed (FractionRing A) := GlobalTheory.T.isAlgClosed_fractionRing_of_monic_polynomials_have_roots A hA
  haveI : IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors A))
      (O ⊗[A] FractionRing A) := by
    rw [Algebra.isLocalization_iff_isPushout (nonZeroDivisors A) (FractionRing A)]
    infer_instance
  have hinj := algebraMap_injective_of_indEt h
  haveI : IsDomain (O ⊗[A] FractionRing A) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (M := Algebra.algebraMapSubmonoid O (nonZeroDivisors A)) (O ⊗[A] FractionRing A) (by
      rintro _ ⟨a, ha, rfl⟩
      exact mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero ha)))
  have hall : ∀ x : O ⊗[A] FractionRing A, IsIntegral (FractionRing A) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact isIntegral_zero
    | tmul o k =>
      have : o ⊗ₜ[A] k = (o ⊗ₜ[A] (1 : FractionRing A)) * algebraMap (FractionRing A) _ k := by
        rw [show algebraMap (FractionRing A) (O ⊗[A] FractionRing A) k = 1 ⊗ₜ k from rfl,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this]
      exact (isIntegral_tmul_one h o).mul isIntegral_algebraMap
    | add x y hx hy => exact hx.add hy
  haveI : Algebra.IsIntegral (FractionRing A) (O ⊗[A] FractionRing A) := ⟨hall⟩
  let e := RingEquiv.ofBijective _
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := FractionRing A) (K := O ⊗[A] FractionRing A))
  exact ⟨MulEquiv.isField (Field.toIsField (FractionRing A)) e.symm.toMulEquiv,
    aic_of_ringEquiv e (aic_of_isAlgClosed _)⟩

end GlobalTheory

/- English proof (translation)
The claim follows from `GlobalTheory.isField_aic_tensor_fractionRing_of_strictlyHenselian`.
-/
example : ∀ (A O : Type) [CommRing A] [IsDomain A] [CommRing O] [Algebra A O], AIC A → SH O → IndEt A O → IsField (O ⊗[A] FractionRing A) ∧ AIC (O ⊗[A] FractionRing A) :=
  GlobalTheory.isField_aic_tensor_fractionRing_of_strictlyHenselian
