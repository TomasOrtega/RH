import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointAtZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FittingDatumBaseChangeLocalEnlargementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingModTEmbedsStrictHenselianStatement
open IsLocalRing Polynomial

namespace GlobalTheory.KeyOriginRetract

/- English proof (translation)
Unfold `GlobalTheory.KeyOriginCut.originIdeal`. Prove the components needed by the constructor for the conclusion. Introduce `hp`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hp`. Rewrite using `[Polynomial.coeff_add]`.

Use `Ideal.add_mem _ ((Ideal.mem_map_C_iff.1 ha) 0) ?_` and prove the remaining obligations. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton.1 hb`. Simplify using the standard rewrite rules. Introduce `hp`. Establish `h1 : Polynomial.C (p.coeff 0) ∈ (maximalIdeal R).map (Polynomial.C : R →+* Polynomial R)` using `Ideal.mem_map_of_mem _ hp`.

Establish `h2 : p - Polynomial.C (p.coeff 0) ∈ Ideal.span {(Polynomial.X : Polynomial R)}` using `Ideal.mem_span_singleton.2 Polynomial.X_dvd_sub_C`. Use `Submodule.add_mem_sup h1 h2` as an intermediate fact. Simplify using `using this`.
-/
theorem mem_originIdeal {R : Type} [CommRing R] [IsLocalRing R] (p : Polynomial R) :
    p ∈ GlobalTheory.KeyOriginCut.originIdeal R ↔ p.coeff 0 ∈ maximalIdeal R := by
  unfold GlobalTheory.KeyOriginCut.originIdeal
  constructor
  · intro hp
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hp
    rw [Polynomial.coeff_add]
    refine Ideal.add_mem _ ((Ideal.mem_map_C_iff.1 ha) 0) ?_
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 hb
    simp
  · intro hp
    have h1 : Polynomial.C (p.coeff 0) ∈ (maximalIdeal R).map (Polynomial.C : R →+* Polynomial R) :=
      Ideal.mem_map_of_mem _ hp
    have h2 : p - Polynomial.C (p.coeff 0) ∈ Ideal.span {(Polynomial.X : Polynomial R)} :=
      Ideal.mem_span_singleton.2 Polynomial.X_dvd_sub_C
    have := Submodule.add_mem_sup h1 h2
    simpa using this

/- English proof (translation)
Take `⟨r, hr⟩` from `(Polynomial.X_dvd_sub_C (p := p))`. Rewrite using `[IsScalarTower.algebraMap_apply R (Polynomial R) B, Polynomial.algebraMap_eq, ← map_sub, hr, map_mul]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)`.
-/
theorem sub_coeff_zero_mem {R B : Type} [CommRing R] [CommRing B] [Algebra R B] [Algebra (Polynomial R) B]
    [IsScalarTower R (Polynomial R) B] (p : Polynomial R) :
    algebraMap (Polynomial R) B p - algebraMap R B (p.coeff 0) ∈
      Ideal.span {algebraMap (Polynomial R) B Polynomial.X} := by
  obtain ⟨r, hr⟩ := (Polynomial.X_dvd_sub_C (p := p))
  rw [IsScalarTower.algebraMap_apply R (Polynomial R) B, Polynomial.algebraMap_eq, ← map_sub, hr, map_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 h (hu.map f), fun h => map_nonunit f a h⟩`.
-/
theorem map_mem_max_iff {R S : Type} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] (a : R) : f a ∈ maximalIdeal S ↔ a ∈ maximalIdeal R :=
  ⟨fun h => (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 h (hu.map f), fun h => map_nonunit f a h⟩

end GlobalTheory.KeyOriginRetract

namespace GlobalTheory.KeyOriginRetract

/- English proof (translation)
Introduce `R C D _ _ _ _ _ _ _ _ _ ρ ι hρι`. Establish `hsec : ∀ y : C, ρ (ι (ρ y)) = ρ y` using `fun y => AlgHom.congr_fun hρι (ρ y)`. Establish `hsq : RingHom.ker ρ ≤ RingHom.ker ρ ^ 2`. Introduce `x hx`. Set `π : C →ₐ[R] C ⧸ RingHom.ker ρ ^ 2` to `Ideal.Quotient.mkₐ R (RingHom.ker ρ ^ 2)`.

Set `I : Ideal (C ⧸ RingHom.ker ρ ^ 2)` to `(RingHom.ker ρ).map (Ideal.Quotient.mk (RingHom.ker ρ ^ 2))`. Establish `hI : I ^ 2 = ⊥`. Simplify using `only [I, ← Ideal.map_pow, Ideal.map_quotient_self]`. Establish `key : π = (π.comp ι).comp ρ`. Apply `Algebra.FormallyUnramified.comp_injective I hI` to reduce the goal to its premises.

Use `AlgHom.ext fun y => ?_` and prove the remaining obligations. Simplify using `only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, π]`. Rewrite using `[Ideal.Quotient.eq, ← map_sub]`. Use `Ideal.mem_map_of_mem _ ?_` and prove the remaining obligations. Rewrite using `[RingHom.mem_ker, map_sub, hsec, sub_self]`.

Establish `h1` using `AlgHom.congr_fun key x`. Rewrite `h1` using `[AlgHom.comp_apply, AlgHom.comp_apply, (RingHom.mem_ker).1 hx, map_zero, map_zero]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 h1`. Establish `hid : IsIdempotentElem (RingHom.ker ρ)`. Use `le_antisymm ?_ ?_` and prove the remaining obligations.

Conclude with `Ideal.mul_le_right`. Simplify `hsq` using `[pow_two]`. Take `⟨e, he, hJ⟩` from `(Ideal.isIdempotentElem_iff_of_fg _ (IsNoetherian.noetherian _)).1 hid`. Break down `IsLocalRing.isUnit_or_isUnit_one_sub_self e with hu | hu` into its components or cases. It suffices to derive a contradiction.

Establish `he1 : e = 1`. Establish `: e * e = e * 1` using `by rw [he.eq, mul_one]`. Conclude with `hu.mul_left_cancel this`. Establish `: (1 : C) ∈ RingHom.ker ρ`. Rewrite using `[hJ, he1]`.

Conclude with `Ideal.mem_span_singleton_self 1`. Rewrite `this` using `[RingHom.mem_ker, map_one]`. Conclude with `one_ne_zero this`. Establish `he0 : e = 0`. Establish `: (1 - e) * e = (1 - e) * 0` using `by rw [sub_mul, one_mul, he.eq, sub_self, mul_zero]`.

Conclude with `hu.mul_left_cancel this`. Rewrite using `[hJ, he0]`. Simplify using the standard rewrite rules.
-/
theorem ker_eq_bot_of_section : ∀ (R C D : Type) [CommRing R] [CommRing C] [IsLocalRing C] [IsNoetherianRing C] [CommRing D] [Nontrivial D]
    [Algebra R C] [Algebra R D] [Algebra.FormallyUnramified R C] (ρ : C →ₐ[R] D) (ι : D →ₐ[R] C),
    ρ.comp ι = AlgHom.id R D → RingHom.ker ρ = ⊥ := by
  intro R C D _ _ _ _ _ _ _ _ _ ρ ι hρι
  have hsec : ∀ y : C, ρ (ι (ρ y)) = ρ y := fun y => AlgHom.congr_fun hρι (ρ y)
  have hsq : RingHom.ker ρ ≤ RingHom.ker ρ ^ 2 := by
    intro x hx
    let π : C →ₐ[R] C ⧸ RingHom.ker ρ ^ 2 := Ideal.Quotient.mkₐ R (RingHom.ker ρ ^ 2)
    let I : Ideal (C ⧸ RingHom.ker ρ ^ 2) := (RingHom.ker ρ).map (Ideal.Quotient.mk (RingHom.ker ρ ^ 2))
    have hI : I ^ 2 = ⊥ := by
      simp only [I, ← Ideal.map_pow, Ideal.map_quotient_self]
    have key : π = (π.comp ι).comp ρ := by
      apply Algebra.FormallyUnramified.comp_injective I hI
      refine AlgHom.ext fun y => ?_
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, π]
      rw [Ideal.Quotient.eq, ← map_sub]
      refine Ideal.mem_map_of_mem _ ?_
      rw [RingHom.mem_ker, map_sub, hsec, sub_self]
    have h1 := AlgHom.congr_fun key x
    rw [AlgHom.comp_apply, AlgHom.comp_apply, (RingHom.mem_ker).1 hx, map_zero, map_zero] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.1 h1
  have hid : IsIdempotentElem (RingHom.ker ρ) := by
    refine le_antisymm ?_ ?_
    · exact Ideal.mul_le_right
    · simpa [pow_two] using hsq
  obtain ⟨e, he, hJ⟩ := (Ideal.isIdempotentElem_iff_of_fg _ (IsNoetherian.noetherian _)).1 hid
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with hu | hu
  · exfalso
    have he1 : e = 1 := by
      have : e * e = e * 1 := by rw [he.eq, mul_one]
      exact hu.mul_left_cancel this
    have : (1 : C) ∈ RingHom.ker ρ := by
      rw [hJ, he1]; exact Ideal.mem_span_singleton_self 1
    rw [RingHom.mem_ker, map_one] at this
    exact one_ne_zero this
  · have he0 : e = 0 := by
      have : (1 - e) * e = (1 - e) * 0 := by rw [sub_mul, one_mul, he.eq, sub_self, mul_zero]
      exact hu.mul_left_cancel this
    rw [hJ, he0]
    simp
end GlobalTheory.KeyOriginRetract

namespace GlobalTheory.KeyOriginEnlarge
open GlobalTheory.KeyOriginRetract in
/- English proof (translation)
Introduce `T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP q hq0 hqT A _ _ _ _ _ _ i EA _ _ _ _ _ QA _ jA ψA DA _ _ actA hF`. Establish `hF0` using `hF`. Take `⟨hi, hil, hqA, hQA, hjA, hψA, htor⟩` from `hF`. Use `haveI : HenselianLocalRing O := hsh.1`. Use `haveI : IsLocalHom φ := hsh.2.2.1`.

Establish `hPmax : ∀ p : Polynomial T, algebraMap (Polynomial T) O p ∈ maximalIdeal O ↔ p ∈ P`. Introduce `p`. Rewrite using `[← hφ, RingHom.comp_apply, map_mem_max_iff, IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P p]`. Establish `hTO : IsLocalHom (algebraMap T O)`. Use `⟨fun t ht => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hu`. Establish `hm : Polynomial.C t ∈ P`. Rewrite using `[hP, mem_originIdeal]`. Simplify using `using hu`. Rewrite `ht` using `[IsScalarTower.algebraMap_apply T (Polynomial T) O, Polynomial.algebraMap_eq]`.

Conclude with `(mem_maximalIdeal _).1 ((hPmax _).2 hm) ht`. Use `haveI := hTO`. Establish `hX : algebraMap (Polynomial T) O Polynomial.X ∈ maximalIdeal O` using `(hPmax _).2 (by rw [hP, mem_originIdeal]; simp)`. Set `I : Ideal O` to `Ideal.span {algebraMap (Polynomial T) O Polynomial.X}`. Establish `hIm : I ≤ maximalIdeal O` using `(Ideal.span_singleton_le_iff_mem _).2 hX`.

Establish `hj : (jA.comp (algebraMap EA (Localization.AtPrime QA))).comp (algebraMap (Polynomial A) EA) = (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i)`. Rewrite using `[RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, hjA]`. Take `⟨A₁, _, _, _, _, _, _, f, i₁, e, hi₁, hil₁, hfi, he, hag⟩` from `GlobalTheory.T.localRing_mod_t_embeds_strictHenselian T O hT hTO hX A i hi hil EA (jA.comp (algebraMap EA (Localization.AtPrime QA))) hj`. Take `⟨EA', _, _, _, _, _, QA', _, jA', ψA', DA', _, _, actA', hF', ⟨β, h, hβ, hh⟩, γ, hγ, hjγ, hQ', hex, huniq⟩` from `GlobalTheory.T.fittingDatum_baseChange_localEnlargement T O hT P φ hφ hsh hP q hq0 hqT A i EA QA jA ψA DA actA hF0 A₁ f i₁ hi₁ hil₁ hfi`. Use `haveI := hil₁`.

Take `⟨σ, hσC, hσγ⟩` from `hex A₁ (Polynomial.evalRingHom 0) e (by`. Rewrite using `[he]`. Use `RingHom.ext fun p => ?_` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.coe_mapRingHom, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map])`. Establish `hag' : (Ideal.Quotient.mk I).comp ((algebraMap T O).comp (i₁.comp σ)) = (Ideal.Quotient.mk I).comp (jA'.comp (algebraMap EA' (Localization.AtPrime QA')))`.

Apply `huniq (O ⧸ I)` to reduce the goal to its premises. Use `RingHom.ext fun p => ?_` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[← RingHom.comp_apply σ, hσC, ← IsScalarTower.algebraMap_apply, ← RingHom.comp_apply jA', hF'.2.2.2.2.1, Ideal.Quotient.eq]`. Use `sub_coeff_zero_mem (B := O) (p.map i₁)` as an intermediate fact.

Rewrite `this` using `[Polynomial.coeff_map]`. Rewrite using `[← neg_mem_iff, neg_sub]`. Simplify `this` using `[Polynomial.coeff_zero_eq_eval_zero]`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Establish `h1` using `RingHom.congr_fun hjγ x`.

Simplify using `only [RingHom.comp_apply] at h1 ⊢`. Rewrite using `[← RingHom.comp_apply σ γ, hσγ, h1, Ideal.Quotient.eq]`. Conclude with `hag x`. Establish `hdiff : ∀ y : EA', algebraMap T O (i₁ (σ y)) - jA' (algebraMap EA' (Localization.AtPrime QA') y) ∈ I`. Introduce `y`.

Use `RingHom.congr_fun hag' y` as an intermediate fact. Simplify using `only [RingHom.comp_apply] at this`. Conclude with `Ideal.Quotient.eq.1 this`. Establish `hQc : ∀ y : EA', y ∈ QA' ↔ σ y ∈ maximalIdeal A₁`. Introduce `y`.

Rewrite using `[← map_mem_max_iff i₁, ← map_mem_max_iff (algebraMap T O)]`. Use `conv_lhs => rw [hQ', Ideal.mem_comap, RingHom.comp_apply]`. Establish `hd` using `hIm (hdiff y)`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Simplify using `using Ideal.add_mem _ hd hy`. Introduce `hy`. Simplify using `using Ideal.sub_mem _ hy hd`. Establish `hunit : ∀ y : QA'.primeCompl, IsUnit (σ y)`. Introduce `y`.

Assume the negation of the conclusion as `hu`. Conclude with `y.2 ((hQc y).2 ((mem_maximalIdeal _).2 hu))`. Set `ρ' : Localization.AtPrime QA' →+* A₁` to `IsLocalization.lift (M := QA'.primeCompl) hunit`. Establish `hρσ : ρ'.comp (algebraMap EA' (Localization.AtPrime QA')) = σ` using `IsLocalization.lift_comp hunit`. Establish `hρA : ρ'.comp (algebraMap A₁ (Localization.AtPrime QA')) = RingHom.id A₁`.

Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply, RingHom.id_apply]`. Rewrite using `[IsScalarTower.algebraMap_apply A₁ EA' (Localization.AtPrime QA'), ← RingHom.comp_apply ρ', hρσ, IsScalarTower.algebraMap_apply A₁ (Polynomial A₁) EA', ← RingHom.comp_apply σ, hσC]`. Simplify using the standard rewrite rules. Establish `hρP : ∀ p : Polynomial A₁, ρ' (algebraMap (Polynomial A₁) (Localization.AtPrime QA') p) = p.coeff 0`.

Introduce `p`. Rewrite using `[IsScalarTower.algebraMap_apply (Polynomial A₁) EA' (Localization.AtPrime QA'), ← RingHom.comp_apply ρ', hρσ, ← RingHom.comp_apply σ, hσC]`. Simplify using `[Polynomial.coeff_zero_eq_eval_zero]`. Establish `hagR : (Ideal.Quotient.mk I).comp ((algebraMap T O).comp (i₁.comp ρ')) = (Ideal.Quotient.mk I).comp jA'`. Use `IsLocalization.ringHom_ext QA'.primeCompl (RingHom.ext fun y => ?_)` and prove the remaining obligations.

Establish `h1` using `RingHom.congr_fun hag' y`. Simplify using `only [RingHom.comp_apply] at h1 ⊢`. Rewrite using `[← RingHom.comp_apply ρ' (algebraMap EA' (Localization.AtPrime QA')), hρσ]`. Conclude with `h1`. Establish `hmod : ∀ x : Localization.AtPrime QA', algebraMap T O (i₁ (ρ' x)) - jA' x ∈ I`.

Introduce `x`. Use `RingHom.congr_fun hagR x` as an intermediate fact. Simplify using `only [RingHom.comp_apply] at this`. Conclude with `Ideal.Quotient.eq.1 this`. Set `J : Ideal (Localization.AtPrime QA')` to `Ideal.span {algebraMap (Polynomial A₁) (Localization.AtPrime QA') Polynomial.X}`.

Establish `hJle : J ≤ RingHom.ker ρ'`. Rewrite using `[Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, hρP]`. Simplify using the standard rewrite rules. Establish `hJne : J ≠ ⊤`. Introduce `hJ`.

Establish `h1 : (1 : Localization.AtPrime QA') ∈ RingHom.ker ρ'` using `hJle (hJ ▸ Submodule.mem_top)`. Rewrite `h1` using `[RingHom.mem_ker, map_one]`. Conclude with `one_ne_zero h1`. Use `haveI : Nontrivial (Localization.AtPrime QA' ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJne`. Use `haveI : IsLocalRing (Localization.AtPrime QA' ⧸ J) := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective`.

Use `haveI : IsNoetherianRing EA' := Algebra.FiniteType.isNoetherianRing (Polynomial A₁) EA'`. Use `haveI : IsNoetherianRing (Localization.AtPrime QA') := IsLocalization.isNoetherianRing QA'.primeCompl _ inferInstance`. Use `haveI : Algebra.FormallyUnramified EA' (Localization.AtPrime QA') := Algebra.FormallyUnramified.of_isLocalization QA'.primeCompl`. Use `haveI : Algebra.FormallyUnramified (Polynomial A₁) (Localization.AtPrime QA') := Algebra.FormallyUnramified.comp _ EA' _`. Use `haveI : Algebra.FormallyUnramified (Polynomial A₁) (Localization.AtPrime QA' ⧸ J) := Algebra.FormallyUnramified.of_surjective (Ideal.Quotient.mkₐ (Polynomial A₁) J) Ideal.Quotient.mk_surjective`.

Use `letI : Algebra (Polynomial A₁) A₁ := (Polynomial.evalRingHom 0).toAlgebra`. Use `haveI : IsScalarTower A₁ (Polynomial A₁) (Localization.AtPrime QA') := IsScalarTower.of_algebraMap_eq fun a => by`. Rewrite using `[IsScalarTower.algebraMap_apply A₁ EA' (Localization.AtPrime QA'), IsScalarTower.algebraMap_apply A₁ (Polynomial A₁) EA', ← IsScalarTower.algebraMap_apply]`. Establish `hρc : ∀ p : Polynomial A₁, ρ' (algebraMap (Polynomial A₁) (Localization.AtPrime QA') p) = algebraMap (Polynomial A₁) A₁ p`. Introduce `p`.

Express the relevant statement in the definitionally equal form `ρ' _ = Polynomial.eval 0 p`. Rewrite using `[hρP, Polynomial.coeff_zero_eq_eval_zero]`. Set `ρa : Localization.AtPrime QA' →ₐ[Polynomial A₁] A₁` to `AlgHom.mk ρ' hρc`. Set `ρb : (Localization.AtPrime QA' ⧸ J) →ₐ[Polynomial A₁] A₁` to `Ideal.Quotient.liftₐ J ρa (fun a ha => hJle ha)`. Establish `hιc : ∀ p : Polynomial A₁, ((Ideal.Quotient.mk J).comp (algebraMap A₁ (Localization.AtPrime QA'))) (algebraMap (Polynomial A₁) A₁ p) = algebraMap (Polynomial A₁) (Localization.AtPrime QA' ⧸ J) p`.

Introduce `p`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk J (algebraMap A₁ (Localization.AtPrime QA') (Polynomial.eval 0 p)) = Ideal.Quotient.mk J (algebraMap (Polynomial A₁) (Localization.AtPrime QA') p)`. Rewrite using `[Ideal.Quotient.eq, ← neg_mem_iff, neg_sub, ← Polynomial.coeff_zero_eq_eval_zero]`. Conclude with `sub_coeff_zero_mem p`. Set `ιb : A₁ →ₐ[Polynomial A₁] (Localization.AtPrime QA' ⧸ J)` to `AlgHom.mk ((Ideal.Quotient.mk J).comp (algebraMap A₁ (Localization.AtPrime QA'))) hιc`.

Establish `hcomp : ρb.comp ιb = AlgHom.id (Polynomial A₁) A₁`. Use `AlgHom.ext fun a => ?_` and prove the remaining obligations. Conclude with `RingHom.congr_fun hρA a`. Establish `hkb` using `ker_eq_bot_of_section (Polynomial A₁) (Localization.AtPrime QA' ⧸ J) A₁ ρb ιb hcomp`. Establish `hker : RingHom.ker ρ' = J`.

Use `le_antisymm (fun x hx => ?_) hJle` and prove the remaining obligations. Establish `h1 : Ideal.Quotient.mk J x ∈ RingHom.ker ρb` using `hx`. Rewrite `h1` using `[hkb, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `h1`. Conclude with `⟨A₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, i₁, EA', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, QA', inferInstance, jA', ψA', DA', inferInstance, inferInstance, actA', hF', ⟨ρ', ⟨hρA, hker, hmod⟩, …`.
-/
theorem enlarge_retract : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsLocalRing A') (_ : IsNoetherianRing A')
      (_ : IsIntegrallyClosed A') (_ : Algebra.EssFiniteType ℤ A') (i' : A' →+* T)
      (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A') EA') (_ : Algebra A' EA')
      (_ : IsScalarTower A' (Polynomial A') EA') (_ : Algebra.Etale (Polynomial A') EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime) (jA' : Localization.AtPrime QA' →+* O)
      (ψA' : GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA')
      (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')] DA')),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A' i' EA' QA' jA' ψA' DA' actA' ∧
      (∃ ρ' : Localization.AtPrime QA' →+* A',
        GlobalTheory.KeyOriginEnlarge.Retracts T O A' i' EA' QA' jA' ρ' ∧ True) ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) (h : DA →+* DA'),
        ψA'.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA').comp β := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP q hq0 hqT A _ _ _ _ _ _ i EA _ _ _ _ _ QA _ jA ψA DA _ _ actA hF
  have hF0 := hF
  obtain ⟨hi, hil, hqA, hQA, hjA, hψA, htor⟩ := hF
  haveI : HenselianLocalRing O := hsh.1
  haveI : IsLocalHom φ := hsh.2.2.1
  have hPmax : ∀ p : Polynomial T, algebraMap (Polynomial T) O p ∈ maximalIdeal O ↔ p ∈ P := by
    intro p
    rw [← hφ, RingHom.comp_apply, map_mem_max_iff,
      IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P p]
  have hTO : IsLocalHom (algebraMap T O) := by
    refine ⟨fun t ht => ?_⟩
    by_contra hu
    have hm : Polynomial.C t ∈ P := by
      rw [hP, mem_originIdeal]; simpa using hu
    rw [IsScalarTower.algebraMap_apply T (Polynomial T) O, Polynomial.algebraMap_eq] at ht
    exact (mem_maximalIdeal _).1 ((hPmax _).2 hm) ht
  haveI := hTO
  have hX : algebraMap (Polynomial T) O Polynomial.X ∈ maximalIdeal O :=
    (hPmax _).2 (by rw [hP, mem_originIdeal]; simp)
  let I : Ideal O := Ideal.span {algebraMap (Polynomial T) O Polynomial.X}
  have hIm : I ≤ maximalIdeal O := (Ideal.span_singleton_le_iff_mem _).2 hX
  have hj : (jA.comp (algebraMap EA (Localization.AtPrime QA))).comp (algebraMap (Polynomial A) EA) =
      (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) := by
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, hjA]
  obtain ⟨A₁, _, _, _, _, _, _, f, i₁, e, hi₁, hil₁, hfi, he, hag⟩ :=
    GlobalTheory.T.localRing_mod_t_embeds_strictHenselian T O hT hTO hX A i hi hil EA (jA.comp (algebraMap EA (Localization.AtPrime QA))) hj
  obtain ⟨EA', _, _, _, _, _, QA', _, jA', ψA', DA', _, _, actA', hF', ⟨β, h, hβ, hh⟩, γ, hγ, hjγ, hQ',
    hex, huniq⟩ := GlobalTheory.T.fittingDatum_baseChange_localEnlargement T O hT P φ hφ hsh hP q hq0 hqT A i EA QA jA ψA DA actA hF0 A₁ f i₁ hi₁ hil₁ hfi
  haveI := hil₁
  obtain ⟨σ, hσC, hσγ⟩ := hex A₁ (Polynomial.evalRingHom 0) e (by
    rw [he]
    refine RingHom.ext fun p => ?_
    simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.coe_mapRingHom,
      ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map])
  have hag' : (Ideal.Quotient.mk I).comp ((algebraMap T O).comp (i₁.comp σ)) =
      (Ideal.Quotient.mk I).comp (jA'.comp (algebraMap EA' (Localization.AtPrime QA'))) := by
    apply huniq (O ⧸ I)
    · refine RingHom.ext fun p => ?_
      simp only [RingHom.comp_apply]
      rw [← RingHom.comp_apply σ, hσC, ← IsScalarTower.algebraMap_apply,
        ← RingHom.comp_apply jA', hF'.2.2.2.2.1, Ideal.Quotient.eq]
      have := sub_coeff_zero_mem (B := O) (p.map i₁)
      rw [Polynomial.coeff_map] at this
      rw [← neg_mem_iff, neg_sub]
      simpa [Polynomial.coeff_zero_eq_eval_zero] using this
    · refine RingHom.ext fun x => ?_
      have h1 := RingHom.congr_fun hjγ x
      simp only [RingHom.comp_apply] at h1 ⊢
      rw [← RingHom.comp_apply σ γ, hσγ, h1, Ideal.Quotient.eq]
      exact hag x

  have hdiff : ∀ y : EA', algebraMap T O (i₁ (σ y)) - jA' (algebraMap EA' (Localization.AtPrime QA') y) ∈ I := by
    intro y
    have := RingHom.congr_fun hag' y
    simp only [RingHom.comp_apply] at this
    exact Ideal.Quotient.eq.1 this
  have hQc : ∀ y : EA', y ∈ QA' ↔ σ y ∈ maximalIdeal A₁ := by
    intro y
    rw [← map_mem_max_iff i₁, ← map_mem_max_iff (algebraMap T O)]
    conv_lhs => rw [hQ', Ideal.mem_comap, RingHom.comp_apply]
    have hd := hIm (hdiff y)
    constructor
    · intro hy; simpa using Ideal.add_mem _ hd hy
    · intro hy; simpa using Ideal.sub_mem _ hy hd
  have hunit : ∀ y : QA'.primeCompl, IsUnit (σ y) := by
    intro y
    by_contra hu
    exact y.2 ((hQc y).2 ((mem_maximalIdeal _).2 hu))
  let ρ' : Localization.AtPrime QA' →+* A₁ := IsLocalization.lift (M := QA'.primeCompl) hunit
  have hρσ : ρ'.comp (algebraMap EA' (Localization.AtPrime QA')) = σ := IsLocalization.lift_comp hunit
  have hρA : ρ'.comp (algebraMap A₁ (Localization.AtPrime QA')) = RingHom.id A₁ := by
    refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [IsScalarTower.algebraMap_apply A₁ EA' (Localization.AtPrime QA'), ← RingHom.comp_apply ρ', hρσ,
      IsScalarTower.algebraMap_apply A₁ (Polynomial A₁) EA', ← RingHom.comp_apply σ, hσC]
    simp
  have hρP : ∀ p : Polynomial A₁, ρ' (algebraMap (Polynomial A₁) (Localization.AtPrime QA') p) = p.coeff 0 := by
    intro p
    rw [IsScalarTower.algebraMap_apply (Polynomial A₁) EA' (Localization.AtPrime QA'), ← RingHom.comp_apply ρ', hρσ,
      ← RingHom.comp_apply σ, hσC]
    simp [Polynomial.coeff_zero_eq_eval_zero]
  have hagR : (Ideal.Quotient.mk I).comp ((algebraMap T O).comp (i₁.comp ρ')) = (Ideal.Quotient.mk I).comp jA' := by
    refine IsLocalization.ringHom_ext QA'.primeCompl (RingHom.ext fun y => ?_)
    have h1 := RingHom.congr_fun hag' y
    simp only [RingHom.comp_apply] at h1 ⊢
    rw [← RingHom.comp_apply ρ' (algebraMap EA' (Localization.AtPrime QA')), hρσ]
    exact h1
  have hmod : ∀ x : Localization.AtPrime QA', algebraMap T O (i₁ (ρ' x)) - jA' x ∈ I := by
    intro x
    have := RingHom.congr_fun hagR x
    simp only [RingHom.comp_apply] at this
    exact Ideal.Quotient.eq.1 this

  let J : Ideal (Localization.AtPrime QA') := Ideal.span {algebraMap (Polynomial A₁) (Localization.AtPrime QA') Polynomial.X}
  have hJle : J ≤ RingHom.ker ρ' := by
    rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, hρP]; simp
  have hJne : J ≠ ⊤ := by
    intro hJ
    have h1 : (1 : Localization.AtPrime QA') ∈ RingHom.ker ρ' := hJle (hJ ▸ Submodule.mem_top)
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  haveI : Nontrivial (Localization.AtPrime QA' ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJne
  haveI : IsLocalRing (Localization.AtPrime QA' ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  haveI : IsNoetherianRing EA' := Algebra.FiniteType.isNoetherianRing (Polynomial A₁) EA'
  haveI : IsNoetherianRing (Localization.AtPrime QA') :=
    IsLocalization.isNoetherianRing QA'.primeCompl _ inferInstance
  haveI : Algebra.FormallyUnramified EA' (Localization.AtPrime QA') :=
    Algebra.FormallyUnramified.of_isLocalization QA'.primeCompl
  haveI : Algebra.FormallyUnramified (Polynomial A₁) (Localization.AtPrime QA') :=
    Algebra.FormallyUnramified.comp _ EA' _
  haveI : Algebra.FormallyUnramified (Polynomial A₁) (Localization.AtPrime QA' ⧸ J) :=
    Algebra.FormallyUnramified.of_surjective (Ideal.Quotient.mkₐ (Polynomial A₁) J) Ideal.Quotient.mk_surjective
  letI : Algebra (Polynomial A₁) A₁ := (Polynomial.evalRingHom 0).toAlgebra
  haveI : IsScalarTower A₁ (Polynomial A₁) (Localization.AtPrime QA') :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsScalarTower.algebraMap_apply A₁ EA' (Localization.AtPrime QA'),
        IsScalarTower.algebraMap_apply A₁ (Polynomial A₁) EA', ← IsScalarTower.algebraMap_apply]
  have hρc : ∀ p : Polynomial A₁, ρ' (algebraMap (Polynomial A₁) (Localization.AtPrime QA') p) =
      algebraMap (Polynomial A₁) A₁ p := by
    intro p
    change ρ' _ = Polynomial.eval 0 p
    rw [hρP, Polynomial.coeff_zero_eq_eval_zero]
  let ρa : Localization.AtPrime QA' →ₐ[Polynomial A₁] A₁ := AlgHom.mk ρ' hρc
  let ρb : (Localization.AtPrime QA' ⧸ J) →ₐ[Polynomial A₁] A₁ :=
    Ideal.Quotient.liftₐ J ρa (fun a ha => hJle ha)
  have hιc : ∀ p : Polynomial A₁, ((Ideal.Quotient.mk J).comp (algebraMap A₁ (Localization.AtPrime QA')))
      (algebraMap (Polynomial A₁) A₁ p) = algebraMap (Polynomial A₁) (Localization.AtPrime QA' ⧸ J) p := by
    intro p
    change Ideal.Quotient.mk J (algebraMap A₁ (Localization.AtPrime QA') (Polynomial.eval 0 p)) =
      Ideal.Quotient.mk J (algebraMap (Polynomial A₁) (Localization.AtPrime QA') p)
    rw [Ideal.Quotient.eq, ← neg_mem_iff, neg_sub, ← Polynomial.coeff_zero_eq_eval_zero]
    exact sub_coeff_zero_mem p
  let ιb : A₁ →ₐ[Polynomial A₁] (Localization.AtPrime QA' ⧸ J) :=
    AlgHom.mk ((Ideal.Quotient.mk J).comp (algebraMap A₁ (Localization.AtPrime QA'))) hιc
  have hcomp : ρb.comp ιb = AlgHom.id (Polynomial A₁) A₁ := by
    refine AlgHom.ext fun a => ?_
    exact RingHom.congr_fun hρA a
  have hkb := ker_eq_bot_of_section (Polynomial A₁) (Localization.AtPrime QA' ⧸ J) A₁ ρb ιb hcomp
  have hker : RingHom.ker ρ' = J := by
    refine le_antisymm (fun x hx => ?_) hJle
    have h1 : Ideal.Quotient.mk J x ∈ RingHom.ker ρb := hx
    rw [hkb, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at h1
    exact h1
  exact ⟨A₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, i₁,
    EA', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, QA', inferInstance, jA', ψA',
    DA', inferInstance, inferInstance, actA', hF', ⟨ρ', ⟨hρA, hker, hmod⟩, trivial⟩, β, h, hβ, hh⟩
end GlobalTheory.KeyOriginEnlarge
