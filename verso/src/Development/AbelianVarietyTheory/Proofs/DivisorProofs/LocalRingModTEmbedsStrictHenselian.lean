import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointAtZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRootSubMemOfEvalMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingHomOfIsStrictHenselisation
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomToFieldFactorsAlgClosedSubfieldStatement
open IsLocalRing Polynomial

noncomputable section
namespace GlobalTheory.FibreRetract

/- English proof (translation)
Use `haveI : Nontrivial (O ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI`. Use `haveI : IsLocalRing (O ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective`. Use `haveI : HenselianLocalRing (O ⧸ I) := GlobalTheory.henselianLocalRing_of_finite O (O ⧸ I)`. Use `set π : T →+* O ⧸ I := (Ideal.Quotient.mk I).comp (algebraMap T O) with hπ`. Use `haveI : IsLocalHom (Ideal.Quotient.mk I) := isLocalHom_of_le_jacobson_bot I (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]; exact le_maximalIdeal hI)`.

Use `haveI : IsLocalHom π := inferInstance`. Establish `het : (algebraMap A B).Etale` using `RingHom.etale_algebraMap.mpr inferInstance`. Take `⟨ψ, hψ1, hψ2⟩` from `GlobalTheory.T.etale_hom_to_field_factors_algClosed_subfield A B (ResidueField T) (ResidueField (O ⧸ I)) ((residue T).comp i) (ResidueField.map π) ((residue (O ⧸ I)).comp b) (fun a ha => by`. Simplify using `only [RingHom.comp_apply, residue_eq_zero_iff]`. Conclude with `map_nonunit i a ha)`.

Use the proof step `(by`. Use extensionality with `a`. Use `DFunLike.congr_fun hb a` as an intermediate fact. Simplify using `only [RingHom.comp_apply] at this ⊢`. Rewrite using `[this, ResidueField.map_residue])`.

Take `⟨s, hs1, hs2⟩` from `GlobalTheory.NCyc.StrictLocLift.lift_exists (algebraMap A B) het i ψ hψ1`. Use `⟨s, hs1, ?_⟩` and prove the remaining obligations. Use `GlobalTheory.NCyc.StrictLocLift.lift_unique (algebraMap A B) het (π.comp i) _ _ ?_ hb ?_` and prove the remaining obligations. Rewrite using `[RingHom.comp_assoc, hs1]`. Use extensionality with `x`.

Establish `h2` using `DFunLike.congr_fun hψ2 x`. Establish `h3` using `DFunLike.congr_fun hs2 x`. Simplify using `only [RingHom.comp_apply] at h2 h3 ⊢`. Rewrite using `[← h2, ← h3, ResidueField.map_residue]`.
-/
theorem exists_section_mod (T O : Type) [CommRing T] [IsLocalRing T] [HenselianLocalRing T]
    [IsAlgClosed (ResidueField T)] [CommRing O] [HenselianLocalRing O] [Algebra T O]
    [IsLocalHom (algebraMap T O)] (I : Ideal O) (hI : I ≠ ⊤)
    (A : Type) [CommRing A] [IsLocalRing A] (i : A →+* T) [IsLocalHom i]
    (B : Type) [CommRing B] [Algebra A B] [Algebra.Etale A B] (b : B →+* O ⧸ I)
    (hb : b.comp (algebraMap A B) = ((Ideal.Quotient.mk I).comp (algebraMap T O)).comp i) :
    ∃ s : B →+* T, s.comp (algebraMap A B) = i ∧
      ((Ideal.Quotient.mk I).comp (algebraMap T O)).comp s = b := by
  haveI : Nontrivial (O ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI : IsLocalRing (O ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  haveI : HenselianLocalRing (O ⧸ I) := GlobalTheory.henselianLocalRing_of_finite O (O ⧸ I)
  set π : T →+* O ⧸ I := (Ideal.Quotient.mk I).comp (algebraMap T O) with hπ
  haveI : IsLocalHom (Ideal.Quotient.mk I) := isLocalHom_of_le_jacobson_bot I
    (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]; exact le_maximalIdeal hI)
  haveI : IsLocalHom π := inferInstance
  have het : (algebraMap A B).Etale := RingHom.etale_algebraMap.mpr inferInstance
  obtain ⟨ψ, hψ1, hψ2⟩ := GlobalTheory.T.etale_hom_to_field_factors_algClosed_subfield A B (ResidueField T) (ResidueField (O ⧸ I))
    ((residue T).comp i) (ResidueField.map π) ((residue (O ⧸ I)).comp b)
    (fun a ha => by
      simp only [RingHom.comp_apply, residue_eq_zero_iff]
      exact map_nonunit i a ha)
    (by
      ext a
      have := DFunLike.congr_fun hb a
      simp only [RingHom.comp_apply] at this ⊢
      rw [this, ResidueField.map_residue])
  obtain ⟨s, hs1, hs2⟩ := GlobalTheory.NCyc.StrictLocLift.lift_exists (algebraMap A B) het i ψ hψ1
  refine ⟨s, hs1, ?_⟩
  refine GlobalTheory.NCyc.StrictLocLift.lift_unique (algebraMap A B) het (π.comp i) _ _ ?_ hb ?_
  · rw [RingHom.comp_assoc, hs1]
  · ext x
    have h2 := DFunLike.congr_fun hψ2 x
    have h3 := DFunLike.congr_fun hs2 x
    simp only [RingHom.comp_apply] at h2 h3 ⊢
    rw [← h2, ← h3, ResidueField.map_residue]

end GlobalTheory.FibreRetract

namespace GlobalTheory.FibreRetract

/- English proof (translation)
Introduce `T O _ _ _ _ _ _ _ _ hT hTO ht A _ _ _ _ _ _ i hi hil EA _ _ _ _ _ j hj`. Take `⟨hTh, hTac, -⟩` from `GlobalTheory.AbsIntClosedLocal.henselian_isAlgClosed_pow_surj T ⟨inferInstance, hT⟩`. Use `set I : Ideal O := Ideal.span {algebraMap (Polynomial T) O Polynomial.X} with hIdef`. Establish `hI : I ≠ ⊤` using `fun h => (maximalIdeal.isMaximal O).ne_top (top_le_iff.mp (h ▸ (Ideal.span_singleton_le_iff_mem _).mpr ht))`. Use `letI : Algebra (Polynomial A) A := (Polynomial.evalRingHom 0).toAlgebra`.

Set `B` to `TensorProduct (Polynomial A) A EA`. Establish `hC : ∀ c : T, algebraMap (Polynomial T) O (Polynomial.C c) = algebraMap T O c` using `fun c => by`. Rewrite using `[IsScalarTower.algebraMap_apply T (Polynomial T) O c, Polynomial.algebraMap_eq]`. Set `φ : Polynomial A →+* O ⧸ I` to `(Ideal.Quotient.mk I).comp ((algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i))`. Use `letI : Algebra (Polynomial A) (O ⧸ I) := φ.toAlgebra`.

Set `f₁ : A →ₐ[Polynomial A] O ⧸ I` to `{ toRingHom := ((Ideal.Quotient.mk I).comp (algebraMap T O)).comp i commutes' := fun p => by`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk I (algebraMap T O (i (p.eval 0))) = Ideal.Quotient.mk I (algebraMap (Polynomial T) O (p.map i))`. Rewrite using `[Ideal.Quotient.eq]`. Take `⟨q, hq⟩` from `Polynomial.X_dvd_sub_C (p := p.map i)`. Establish `h0 : (p.map i).coeff 0 = i (p.eval 0)`.

Rewrite using `[Polynomial.coeff_map, Polynomial.coeff_zero_eq_eval_zero]`. Rewrite `hq` using `[h0]`. Rewrite using `[← hC, ← map_sub, ← neg_sub, hq, map_neg, map_mul]`. Conclude with `I.neg_mem (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)) }`. Set `f₂ : EA →ₐ[Polynomial A] O ⧸ I` to `{ toRingHom := (Ideal.Quotient.mk I).comp j commutes' := fun p => by`.

Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk I (j (algebraMap (Polynomial A) EA p)) = φ p`. Use `DFunLike.congr_fun hj p` as an intermediate fact. Simplify using `only [RingHom.comp_apply] at this`. Simplify using `only [φ, RingHom.comp_apply, this, Polynomial.coe_mapRingHom] }`. Set `b : B →+* O ⧸ I` to `(Algebra.TensorProduct.lift f₁ f₂ (fun _ _ => Commute.all _ _)).toRingHom`.

Establish `hb : b.comp (algebraMap A B) = ((Ideal.Quotient.mk I).comp (algebraMap T O)).comp i`. Use extensionality with `a`. Express the relevant statement in the definitionally equal form `b (algebraMap A B a) = _`. Rewrite using `[Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]`. Conclude with `(Algebra.TensorProduct.lift_tmul f₁ f₂ _ a 1).trans (by rw [map_one, mul_one]; rfl)`.

Use `haveI := hTh`. Use `haveI := hTac`. Take `⟨s, hs1, hs2⟩` from `exists_section_mod T O I hI A i B b hb`. Set `P : Ideal B` to `(maximalIdeal T).comap s`. Use `haveI hP : P.IsPrime := Ideal.comap_isPrime s (maximalIdeal T)`.

Set `A₁` to `Localization.AtPrime P`. Establish `hunit : ∀ y : P.primeCompl, IsUnit (s y)` using `fun y => by`. Establish `hy : (y : B) ∉ P` using `y.2`. Assume the negation of the conclusion as `h`. Conclude with `hy ((IsLocalRing.mem_maximalIdeal _).mpr h)`.

Set `i₁ : A₁ →+* T` to `IsLocalization.lift hunit`. Establish `hi₁ : i₁.comp (algebraMap B A₁) = s` using `IsLocalization.lift_comp hunit`. Set `f : A →+* A₁` to `algebraMap A A₁`. Set `e : EA →+* A₁` to `(algebraMap B A₁).comp (Algebra.TensorProduct.includeRight : EA →ₐ[Polynomial A] B).toRingHom`. Take `⟨hdom, hic⟩` from `GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale A P A₁`.

Use `haveI := hdom`. Use `haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B`. Use `haveI : IsNoetherianRing A₁ := IsLocalization.isNoetherianRing P.primeCompl A₁ inferInstance`. Use `haveI : Algebra.EssFiniteType ℤ B := Algebra.EssFiniteType.comp ℤ A B`. Use `haveI : Algebra.EssFiniteType B A₁ := Algebra.EssFiniteType.of_isLocalization A₁ P.primeCompl`.

Use `haveI : Algebra.EssFiniteType ℤ A₁ := Algebra.EssFiniteType.comp ℤ B A₁`. Establish `hcomp : i₁.comp f = i`. Rewrite using `[show f = (algebraMap B A₁).comp (algebraMap A B) from IsScalarTower.algebraMap_eq A B A₁, ← RingHom.comp_assoc, hi₁, hs1]`. Establish `hloc : IsLocalHom i₁` using `⟨fun x hx => by`. Take `⟨⟨b', y⟩, rfl⟩` from `IsLocalization.mk'_surjective P.primeCompl x`.

Rewrite using `[IsLocalization.AtPrime.isUnit_mk'_iff]`. Establish `h1 : i₁ (IsLocalization.mk' A₁ b' y) * s y = s b'`. Rewrite using `[← hi₁, RingHom.comp_apply, RingHom.comp_apply, ← map_mul, IsLocalization.mk'_spec]`. Establish `h2 : IsUnit (s b')` using `h1 ▸ hx.mul (hunit y)`. Introduce `hb'`.

Conclude with `(IsLocalRing.mem_maximalIdeal _).mp hb' h2⟩`. Use `haveI : Algebra.QuasiFinite A B := inferInstance`. Use `haveI : Algebra.QuasiFinite A A₁ := inferInstance`. Establish `hinj : Function.Injective i₁`. Establish `h1 : (RingHom.ker i₁).comap f = ⊥`.

Rewrite using `[RingHom.comap_ker, hcomp]`. Conclude with `(RingHom.injective_iff_ker_eq_bot i).mp hi`. Establish `h2 : (⊥ : Ideal A₁).comap f = ⊥` using `eq_bot_iff.mpr fun a ha => h1 ▸ Ideal.comap_mono bot_le ha`. Use `haveI : (RingHom.ker i₁).IsPrime := RingHom.ker_isPrime i₁`. Use `Algebra.QuasiFinite.eq_of_le_of_under_eq (R := A) (⊥ : Ideal A₁) (RingHom.ker i₁) bot_le (by rw [Ideal.under, Ideal.under]; exact h2.trans h1.symm)` as an intermediate fact.

Conclude with `(RingHom.injective_iff_ker_eq_bot i₁).mpr this.symm`. Use `⟨A₁, inferInstance, hdom, inferInstance, inferInstance, hic, ?_, f, i₁, e, hinj, hloc, hcomp, ?_, fun x => ?_⟩` and prove the remaining obligations. Use `‹Algebra.EssFiniteType ℤ A₁› using 1` and compare the differences between its conclusion and the goal. Conclude with `Subsingleton.elim _ _`. Use `RingHom.ext fun p => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `algebraMap B A₁ (Algebra.TensorProduct.includeRight (algebraMap (Polynomial A) EA p)) = algebraMap A A₁ (p.eval 0)`. Rewrite using `[AlgHom.commutes, IsScalarTower.algebraMap_apply A B A₁]`. Both sides reduce to the same expression. Establish `h3` using `DFunLike.congr_fun hs2 (Algebra.TensorProduct.includeRight x)`. Establish `h4 : i₁ (e x) = s (Algebra.TensorProduct.includeRight x)`.

Rewrite using `[← hi₁]`. Both sides reduce to the same expression. Rewrite using `[h4]`. Apply `Ideal.Quotient.eq.mp` to reduce the goal to its premises. Use `h3.trans ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Algebra.TensorProduct.lift f₁ f₂ _ ((1 : A) ⊗ₜ x) = _`. Rewrite using `[Algebra.TensorProduct.lift_tmul, map_one, one_mul]`. Both sides reduce to the same expression.
-/
theorem fibre_retract : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [HenselianLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    IsLocalHom (algebraMap T O) → algebraMap (Polynomial T) O Polynomial.X ∈ maximalIdeal O →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i → IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA] (j : EA →+* O),
      j.comp (algebraMap (Polynomial A) EA) = (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∃ (A₁ : Type) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsLocalRing A₁) (_ : IsNoetherianRing A₁)
      (_ : IsIntegrallyClosed A₁) (_ : Algebra.EssFiniteType ℤ A₁) (f : A →+* A₁) (i₁ : A₁ →+* T) (e : EA →+* A₁),
      Function.Injective i₁ ∧ IsLocalHom i₁ ∧ i₁.comp f = i ∧
      e.comp (algebraMap (Polynomial A) EA) = f.comp (Polynomial.evalRingHom 0) ∧
      ∀ x : EA, algebraMap T O (i₁ (e x)) - j x ∈ Ideal.span {algebraMap (Polynomial T) O Polynomial.X} := by
  intro T O _ _ _ _ _ _ _ _ hT hTO ht A _ _ _ _ _ _ i hi hil EA _ _ _ _ _ j hj
  obtain ⟨hTh, hTac, -⟩ := GlobalTheory.AbsIntClosedLocal.henselian_isAlgClosed_pow_surj T ⟨inferInstance, hT⟩
  set I : Ideal O := Ideal.span {algebraMap (Polynomial T) O Polynomial.X} with hIdef
  have hI : I ≠ ⊤ := fun h => (maximalIdeal.isMaximal O).ne_top (top_le_iff.mp
    (h ▸ (Ideal.span_singleton_le_iff_mem _).mpr ht))
  letI : Algebra (Polynomial A) A := (Polynomial.evalRingHom 0).toAlgebra
  let B := TensorProduct (Polynomial A) A EA
  have hC : ∀ c : T, algebraMap (Polynomial T) O (Polynomial.C c) = algebraMap T O c := fun c => by
    rw [IsScalarTower.algebraMap_apply T (Polynomial T) O c, Polynomial.algebraMap_eq]
  let φ : Polynomial A →+* O ⧸ I :=
    (Ideal.Quotient.mk I).comp ((algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i))
  letI : Algebra (Polynomial A) (O ⧸ I) := φ.toAlgebra
  let f₁ : A →ₐ[Polynomial A] O ⧸ I :=
    { toRingHom := ((Ideal.Quotient.mk I).comp (algebraMap T O)).comp i
      commutes' := fun p => by
        change Ideal.Quotient.mk I (algebraMap T O (i (p.eval 0))) =
          Ideal.Quotient.mk I (algebraMap (Polynomial T) O (p.map i))
        rw [Ideal.Quotient.eq]
        obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := p.map i)
        have h0 : (p.map i).coeff 0 = i (p.eval 0) := by
          rw [Polynomial.coeff_map, Polynomial.coeff_zero_eq_eval_zero]
        rw [h0] at hq
        rw [← hC, ← map_sub, ← neg_sub, hq, map_neg, map_mul]
        exact I.neg_mem (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)) }
  let f₂ : EA →ₐ[Polynomial A] O ⧸ I :=
    { toRingHom := (Ideal.Quotient.mk I).comp j
      commutes' := fun p => by
        change Ideal.Quotient.mk I (j (algebraMap (Polynomial A) EA p)) = φ p
        have := DFunLike.congr_fun hj p
        simp only [RingHom.comp_apply] at this
        simp only [φ, RingHom.comp_apply, this, Polynomial.coe_mapRingHom] }
  let b : B →+* O ⧸ I := (Algebra.TensorProduct.lift f₁ f₂ (fun _ _ => Commute.all _ _)).toRingHom
  have hb : b.comp (algebraMap A B) = ((Ideal.Quotient.mk I).comp (algebraMap T O)).comp i := by
    ext a
    change b (algebraMap A B a) = _
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
    exact (Algebra.TensorProduct.lift_tmul f₁ f₂ _ a 1).trans (by rw [map_one, mul_one]; rfl)
  haveI := hTh; haveI := hTac
  obtain ⟨s, hs1, hs2⟩ := exists_section_mod T O I hI A i B b hb
  let P : Ideal B := (maximalIdeal T).comap s
  haveI hP : P.IsPrime := Ideal.comap_isPrime s (maximalIdeal T)
  let A₁ := Localization.AtPrime P
  have hunit : ∀ y : P.primeCompl, IsUnit (s y) := fun y => by
    have hy : (y : B) ∉ P := y.2
    by_contra h
    exact hy ((IsLocalRing.mem_maximalIdeal _).mpr h)
  let i₁ : A₁ →+* T := IsLocalization.lift hunit
  have hi₁ : i₁.comp (algebraMap B A₁) = s := IsLocalization.lift_comp hunit
  let f : A →+* A₁ := algebraMap A A₁
  let e : EA →+* A₁ := (algebraMap B A₁).comp
    (Algebra.TensorProduct.includeRight : EA →ₐ[Polynomial A] B).toRingHom
  obtain ⟨hdom, hic⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale A P A₁
  haveI := hdom
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  haveI : IsNoetherianRing A₁ := IsLocalization.isNoetherianRing P.primeCompl A₁ inferInstance
  haveI : Algebra.EssFiniteType ℤ B := Algebra.EssFiniteType.comp ℤ A B
  haveI : Algebra.EssFiniteType B A₁ := Algebra.EssFiniteType.of_isLocalization A₁ P.primeCompl
  haveI : Algebra.EssFiniteType ℤ A₁ := Algebra.EssFiniteType.comp ℤ B A₁
  have hcomp : i₁.comp f = i := by
    rw [show f = (algebraMap B A₁).comp (algebraMap A B) from IsScalarTower.algebraMap_eq A B A₁,
      ← RingHom.comp_assoc, hi₁, hs1]
  have hloc : IsLocalHom i₁ := ⟨fun x hx => by
    obtain ⟨⟨b', y⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
    rw [IsLocalization.AtPrime.isUnit_mk'_iff]
    have h1 : i₁ (IsLocalization.mk' A₁ b' y) * s y = s b' := by
      rw [← hi₁, RingHom.comp_apply, RingHom.comp_apply, ← map_mul, IsLocalization.mk'_spec]
    have h2 : IsUnit (s b') := h1 ▸ hx.mul (hunit y)
    intro hb'
    exact (IsLocalRing.mem_maximalIdeal _).mp hb' h2⟩
  haveI : Algebra.QuasiFinite A B := inferInstance
  haveI : Algebra.QuasiFinite A A₁ := inferInstance
  have hinj : Function.Injective i₁ := by
    have h1 : (RingHom.ker i₁).comap f = ⊥ := by
      rw [RingHom.comap_ker, hcomp]; exact (RingHom.injective_iff_ker_eq_bot i).mp hi
    have h2 : (⊥ : Ideal A₁).comap f = ⊥ := eq_bot_iff.mpr fun a ha => h1 ▸ Ideal.comap_mono bot_le ha
    haveI : (RingHom.ker i₁).IsPrime := RingHom.ker_isPrime i₁
    have := Algebra.QuasiFinite.eq_of_le_of_under_eq (R := A) (⊥ : Ideal A₁) (RingHom.ker i₁) bot_le
      (by rw [Ideal.under, Ideal.under]; exact h2.trans h1.symm)
    exact (RingHom.injective_iff_ker_eq_bot i₁).mpr this.symm
  refine ⟨A₁, inferInstance, hdom, inferInstance, inferInstance, hic, ?_, f, i₁, e, hinj,
    hloc, hcomp, ?_, fun x => ?_⟩
  · convert ‹Algebra.EssFiniteType ℤ A₁› using 1
    exact Subsingleton.elim _ _
  · refine RingHom.ext fun p => ?_
    change algebraMap B A₁ (Algebra.TensorProduct.includeRight (algebraMap (Polynomial A) EA p)) =
      algebraMap A A₁ (p.eval 0)
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A B A₁]
    rfl
  · have h3 := DFunLike.congr_fun hs2 (Algebra.TensorProduct.includeRight x)
    have h4 : i₁ (e x) = s (Algebra.TensorProduct.includeRight x) := by
      rw [← hi₁]; rfl
    rw [h4]
    apply Ideal.Quotient.eq.mp
    refine h3.trans ?_
    change Algebra.TensorProduct.lift f₁ f₂ _ ((1 : A) ⊗ₜ x) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl

end GlobalTheory.FibreRetract
