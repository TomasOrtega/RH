import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsIntegralOfIsAbelianSchemeField
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsUniquePointOfRingHom
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.EqZeroOfForallAlgHomComplex
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Topology

namespace GlobalTheory.ContinuousQuotient

/- English proof (translation)
Use `set I : Ideal A := Ideal.span {b} with hI`. Establish `hmk : ∀ r x : A, r • (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (r * x)` using `fun r x => by`. Rewrite using `[Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_mul]`. Establish `hz : ∀ x : A, Ideal.Quotient.mk I x = 0 ↔ b ∣ x` using `fun x => by`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton]`.

Set `J : A → Ideal A` to `fun x => Submodule.comap (LinearMap.mulRight A x) I`. Establish `hJ : ∀ x r : A, r ∈ J x ↔ b ∣ r * x` using `fun x r => by`. Simplify using `only [J, Submodule.mem_comap, LinearMap.mulRight_apply, hI, Ideal.mem_span_singleton]`. Take `⟨P, ⟨c, hc, hac, rfl⟩, hmaxP⟩` from `(set_has_maximal_iff_noetherian (R := A) (M := A)).2 inferInstance {P | ∃ x, ¬ b ∣ x ∧ J a ≤ J x ∧ P = J x} ⟨J a, a, h, le_rfl, rfl⟩`. Establish `hp : (J c).IsPrime`.

Use `⟨fun ht => hc (by simpa using (hJ c 1).1 ((Ideal.eq_top_iff_one _).1 ht)), ?_⟩` and prove the remaining obligations. Introduce `r s hrs`. Assume the negation of the conclusion as `hno`. Use `push Not at hno`. Take `⟨hr, hs⟩` from `hno`.

Establish `hle' : J c ≤ J (r * c)` using `fun t ht => by`. Take `⟨k, hk⟩` from `(hJ c t).1 ht`. Conclude with `(hJ _ t).2 ⟨r * k, by rw [← _root_.mul_assoc, _root_.mul_comm t r, _root_.mul_assoc, hk]; ring⟩`. Establish `hrc : ¬ b ∣ r * c` using `fun hd => hr ((hJ c r).2 hd)`. Establish `heq : J c = J (r * c)`.

Assume the negation of the conclusion as `hne`. Conclude with `hmaxP (J (r * c)) ⟨r * c, hrc, hac.trans hle', rfl⟩ (lt_of_le_of_ne hle' hne)`. Apply `hs` to reduce the goal to its premises. Rewrite using `[heq, hJ]`. Take `⟨k, hk⟩` from `(hJ c (r * s)).1 hrs`.

Conclude with `⟨k, by rw [← hk]; ring⟩`. Use `set p := J c with hpdef`. Establish `hpc : ∀ r : A, r ∈ p ↔ b ∣ r * c` using `hJ c`. Establish `hla : ∀ r : A, b ∣ r * a → r ∈ p` using `fun r hr => hac ((hJ a r).2 hr)`. Establish `hbp : b ∈ p` using `(hpc b).2 (dvd_mul_right b c)`.

Establish `key : ∃ q w : A, q ∈ p ∧ w ∉ p ∧ b * w = q * c`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Set `K` to `FractionRing A`. Set `y : K` to `algebraMap A K c / algebraMap A K b`.

Establish `hb' : algebraMap A K b ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hb`. Set `N : Submodule A K` to `Submodule.map (Algebra.linearMap A K) p`. Establish `hN : N ≠ ⊥`. Introduce `h0`. Establish `: algebraMap A K b ∈ N` using `Submodule.mem_map_of_mem (f := Algebra.linearMap A K) hbp`.

Rewrite `this` using `[h0, Submodule.mem_bot]`. Conclude with `hb' this`. Establish `hfg : N.FG` using `(IsNoetherian.noetherian p).map (Algebra.linearMap A K)`. Establish `hint : IsIntegral A y`. Use `isIntegral_of_smul_mem_submodule N hN hfg y ?_` and prove the remaining obligations.

Introduce `n hn`. Take `⟨q, hq, rfl⟩` from `Submodule.mem_map.1 hn`. Take `⟨w, hw⟩` from `(hpc q).1 hq`. Establish `hwp : w ∈ p`. Assume the negation of the conclusion as `hwp`.

Conclude with `hne q w hq hwp hw.symm`. Use `⟨w, hwp, ?_⟩` and prove the remaining obligations. Simplify using `only [Algebra.linearMap_apply, smul_eq_mul, y]`. Rewrite using `[div_mul_eq_mul_div, eq_div_iff hb', ← map_mul, ← map_mul, _root_.mul_comm w b, ← hw, _root_.mul_comm]`. Take `⟨z, hz'⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hint`.

Establish `hbc : b * z = c`. Apply `IsFractionRing.injective A K` to reduce the goal to its premises. Rewrite using `[map_mul, hz', mul_div_cancel₀ _ hb']`. Conclude with `hp.ne_top ((Ideal.eq_top_iff_one p).2 ((hpc 1).2 ⟨z, by rw [_root_.one_mul, hbc]⟩))`. Take `⟨q, w, hq, hw, hbw⟩` from `key`.

Set `R` to `Localization.AtPrime p`. Establish `: IsDomain R` using `IsLocalization.isDomain_localization p.primeCompl_le_nonZeroDivisors`. Establish `: IsNoetherianRing R` using `IsLocalization.isNoetherianRing p.primeCompl R inferInstance`. Establish `hinj : Function.Injective (algebraMap A R)` using `IsLocalization.injective R p.primeCompl_le_nonZeroDivisors`. Establish `hmax : IsLocalRing.maximalIdeal R = Ideal.span {algebraMap A R q}`.

Rewrite using `[← Localization.AtPrime.map_eq_maximalIdeal]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `x hx`. Take `⟨v, hv⟩` from `(hpc x).1 hx`.

Establish `hwx : w * x = v * q`. Apply `mul_left_cancel₀ hb` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Take `⟨u, hu⟩` from `IsLocalization.map_units R (⟨w, hw⟩ : p.primeCompl)`. Rewrite using `[Ideal.mem_comap, Ideal.mem_span_singleton']`.

Use `⟨(↑u⁻¹ : R) * algebraMap A R v, ?_⟩` and prove the remaining obligations. Establish `e : (u : R) * algebraMap A R x = algebraMap A R v * algebraMap A R q`. Rewrite using `[hu, ← map_mul, ← map_mul, hwx]`. Rewrite using `[_root_.mul_assoc, ← e, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]`. Conclude with `(Ideal.span_singleton_le_iff_mem _).2 (Ideal.mem_map_of_mem _ hq)`.

Establish `hnf : ¬ IsField R`. Introduce `hF`. Establish `h0` using `IsLocalRing.isField_iff_maximalIdeal_eq.1 hF`. Establish `: algebraMap A R b ∈ IsLocalRing.maximalIdeal R`. Rewrite using `[← Localization.AtPrime.map_eq_maximalIdeal]`.

Conclude with `Ideal.mem_map_of_mem _ hbp`. Rewrite `this` using `[h0, Ideal.mem_bot, ← map_zero (algebraMap A R)]`. Conclude with `hb (hinj this)`. Establish `: ValuationRing R` using `((IsDiscreteValuationRing.TFAE R hnf).out 4 1).1 (show Submodule.IsPrincipal (IsLocalRing.maximalIdeal R) from ⟨⟨_, hmax⟩⟩)`. Take `⟨z, hz2⟩` from `ValuationRing.cond (algebraMap A R a) (algebraMap A R b)`.

Take `⟨⟨r, s⟩, rfl⟩` from `IsLocalization.mk'_surjective p.primeCompl z`. Establish `hs : (s : A) ∉ p` using `s.2`. Break down `hz2 with e | e` into its components or cases. Rewrite `e` using `[IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul]`. Establish `e' : a * r = b * s` using `hinj e`.

Establish `hr : r ∈ p` using `hla r ⟨s, by rw [_root_.mul_comm r a, e']⟩`. Conclude with `⟨p, hp, s, r, hs, hr, e'.symm⟩`. Rewrite `e` using `[IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul]`. Establish `e' : b * r = a * s` using `hinj e`. Conclude with `absurd (hla s ⟨r, by rw [_root_.mul_comm (s : A) a, e']⟩) hs`.
-/
theorem exists_prime_of_not_dvd {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] {a b : A} (hb : b ≠ 0) (h : ¬ b ∣ a) :
    ∃ p : Ideal A, p.IsPrime ∧ ∃ s r : A, s ∉ p ∧ r ∈ p ∧ b * s = a * r := by
  classical
  set I : Ideal A := Ideal.span {b} with hI
  have hmk : ∀ r x : A, r • (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (r * x) := fun r x => by
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_mul]
  have hz : ∀ x : A, Ideal.Quotient.mk I x = 0 ↔ b ∣ x := fun x => by
    rw [Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton]

  let J : A → Ideal A := fun x => Submodule.comap (LinearMap.mulRight A x) I
  have hJ : ∀ x r : A, r ∈ J x ↔ b ∣ r * x := fun x r => by
    simp only [J, Submodule.mem_comap, LinearMap.mulRight_apply, hI, Ideal.mem_span_singleton]

  obtain ⟨P, ⟨c, hc, hac, rfl⟩, hmaxP⟩ := (set_has_maximal_iff_noetherian (R := A) (M := A)).2 inferInstance
    {P | ∃ x, ¬ b ∣ x ∧ J a ≤ J x ∧ P = J x} ⟨J a, a, h, le_rfl, rfl⟩
  have hp : (J c).IsPrime := by
    refine ⟨fun ht => hc (by simpa using (hJ c 1).1 ((Ideal.eq_top_iff_one _).1 ht)), ?_⟩
    intro r s hrs
    by_contra hno
    push Not at hno
    obtain ⟨hr, hs⟩ := hno
    have hle' : J c ≤ J (r * c) := fun t ht => by
      obtain ⟨k, hk⟩ := (hJ c t).1 ht
      exact (hJ _ t).2 ⟨r * k, by rw [← _root_.mul_assoc, _root_.mul_comm t r, _root_.mul_assoc, hk]; ring⟩
    have hrc : ¬ b ∣ r * c := fun hd => hr ((hJ c r).2 hd)
    have heq : J c = J (r * c) := by
      by_contra hne
      exact hmaxP (J (r * c)) ⟨r * c, hrc, hac.trans hle', rfl⟩ (lt_of_le_of_ne hle' hne)
    apply hs
    rw [heq, hJ]
    obtain ⟨k, hk⟩ := (hJ c (r * s)).1 hrs
    exact ⟨k, by rw [← hk]; ring⟩
  set p := J c with hpdef
  have hpc : ∀ r : A, r ∈ p ↔ b ∣ r * c := hJ c
  have hla : ∀ r : A, b ∣ r * a → r ∈ p := fun r hr => hac ((hJ a r).2 hr)
  have hbp : b ∈ p := (hpc b).2 (dvd_mul_right b c)

  have key : ∃ q w : A, q ∈ p ∧ w ∉ p ∧ b * w = q * c := by
    by_contra hne
    push Not at hne
    let K := FractionRing A
    let y : K := algebraMap A K c / algebraMap A K b
    have hb' : algebraMap A K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hb
    let N : Submodule A K := Submodule.map (Algebra.linearMap A K) p
    have hN : N ≠ ⊥ := by
      intro h0
      have : algebraMap A K b ∈ N := Submodule.mem_map_of_mem (f := Algebra.linearMap A K) hbp
      rw [h0, Submodule.mem_bot] at this
      exact hb' this
    have hfg : N.FG := (IsNoetherian.noetherian p).map (Algebra.linearMap A K)
    have hint : IsIntegral A y := by
      refine isIntegral_of_smul_mem_submodule N hN hfg y ?_
      intro n hn
      obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.1 hn
      obtain ⟨w, hw⟩ := (hpc q).1 hq
      have hwp : w ∈ p := by
        by_contra hwp
        exact hne q w hq hwp hw.symm
      refine ⟨w, hwp, ?_⟩
      simp only [Algebra.linearMap_apply, smul_eq_mul, y]
      rw [div_mul_eq_mul_div, eq_div_iff hb', ← map_mul, ← map_mul, _root_.mul_comm w b, ← hw, _root_.mul_comm]
    obtain ⟨z, hz'⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    have hbc : b * z = c := by
      apply IsFractionRing.injective A K
      rw [map_mul, hz', mul_div_cancel₀ _ hb']
    exact hp.ne_top ((Ideal.eq_top_iff_one p).2 ((hpc 1).2 ⟨z, by rw [_root_.one_mul, hbc]⟩))
  obtain ⟨q, w, hq, hw, hbw⟩ := key
  let R := Localization.AtPrime p
  have : IsDomain R := IsLocalization.isDomain_localization p.primeCompl_le_nonZeroDivisors
  have : IsNoetherianRing R := IsLocalization.isNoetherianRing p.primeCompl R inferInstance
  have hinj : Function.Injective (algebraMap A R) :=
    IsLocalization.injective R p.primeCompl_le_nonZeroDivisors
  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {algebraMap A R q} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      obtain ⟨v, hv⟩ := (hpc x).1 hx
      have hwx : w * x = v * q := by
        apply mul_left_cancel₀ hb
        calc b * (w * x) = (b * w) * x := by ring
          _ = b * v * q := by rw [hbw, _root_.mul_assoc, _root_.mul_comm c x, hv]; ring
          _ = b * (v * q) := by ring
      obtain ⟨u, hu⟩ := IsLocalization.map_units R (⟨w, hw⟩ : p.primeCompl)
      rw [Ideal.mem_comap, Ideal.mem_span_singleton']
      refine ⟨(↑u⁻¹ : R) * algebraMap A R v, ?_⟩
      have e : (u : R) * algebraMap A R x = algebraMap A R v * algebraMap A R q := by
        rw [hu, ← map_mul, ← map_mul, hwx]
      rw [_root_.mul_assoc, ← e, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
    · exact (Ideal.span_singleton_le_iff_mem _).2 (Ideal.mem_map_of_mem _ hq)
  have hnf : ¬ IsField R := by
    intro hF
    have h0 := IsLocalRing.isField_iff_maximalIdeal_eq.1 hF
    have : algebraMap A R b ∈ IsLocalRing.maximalIdeal R := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]; exact Ideal.mem_map_of_mem _ hbp
    rw [h0, Ideal.mem_bot, ← map_zero (algebraMap A R)] at this
    exact hb (hinj this)
  have : ValuationRing R :=
    ((IsDiscreteValuationRing.TFAE R hnf).out 4 1).1
      (show Submodule.IsPrincipal (IsLocalRing.maximalIdeal R) from ⟨⟨_, hmax⟩⟩)
  obtain ⟨z, hz2⟩ := ValuationRing.cond (algebraMap A R a) (algebraMap A R b)
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
  have hs : (s : A) ∉ p := s.2
  rcases hz2 with e | e
  · rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul] at e
    have e' : a * r = b * s := hinj e
    have hr : r ∈ p := hla r ⟨s, by rw [_root_.mul_comm r a, e']⟩
    exact ⟨p, hp, s, r, hs, hr, e'.symm⟩
  · rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul] at e
    have e' : b * r = a * s := hinj e
    exact absurd (hla s ⟨r, by rw [_root_.mul_comm (s : A) a, e']⟩) hs

/- English proof (translation)
Establish `hv : valAt' x U f = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom ((x.appLE U ⊤ h).hom f)`. Simplify using `only [valAt', dif_pos h, valAt]`. Establish `hb : x ⁻¹ᵁ X.basicOpen f = (Sp ℂ).basicOpen ((x.appLE U ⊤ h).hom f)`. Rewrite using `[Scheme.preimage_basicOpen]`. Use `(Sp ℂ).basicOpen_res (x.app U f) (homOfLE h).op` as an intermediate fact.

Rewrite `this` using `[top_inf_eq]`. Rewrite using `[← this]`. Both sides reduce to the same expression. Rewrite using `[hv, hb]`. Prove the components needed by the constructor for the conclusion.

Introduce `h0`. Use `le_of_eq (Scheme.basicOpen_of_isUnit _ ?_).symm` and prove the remaining obligations. Establish `hu : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom ((x.appLE U ⊤ h).hom f))` using `isUnit_iff_ne_zero.2 h0`. Simplify using `using hu.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom`. Introduce `h1 h0`.

Establish `hz : (x.appLE U ⊤ h).hom f = 0`. Use `congrArg (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom h0` as an intermediate fact. Simplify using `using this`. Rewrite `h1` using `[hz, Scheme.basicOpen_zero]`. Take `⟨pt⟩ : Nonempty (Sp ℂ)` from `inferInstance`.

Conclude with `(h1 (show pt ∈ (⊤ : (Sp ℂ).Opens) from trivial)).elim`.
-/
private theorem valAt'_ne_zero_iff_top_le_preimage_basicOpen {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {U : X.Opens}
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) : valAt' x U f ≠ 0 ↔ ⊤ ≤ x ⁻¹ᵁ X.basicOpen f := by
  have hv : valAt' x U f = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom ((x.appLE U ⊤ h).hom f) := by
    simp only [valAt', dif_pos h, valAt]
  have hb : x ⁻¹ᵁ X.basicOpen f = (Sp ℂ).basicOpen ((x.appLE U ⊤ h).hom f) := by
    rw [Scheme.preimage_basicOpen]
    have := (Sp ℂ).basicOpen_res (x.app U f) (homOfLE h).op
    rw [top_inf_eq] at this
    rw [← this]
    rfl
  rw [hv, hb]
  constructor
  · intro h0
    refine le_of_eq (Scheme.basicOpen_of_isUnit _ ?_).symm
    have hu : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom ((x.appLE U ⊤ h).hom f)) :=
      isUnit_iff_ne_zero.2 h0
    simpa using hu.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  · intro h1 h0
    have hz : (x.appLE U ⊤ h).hom f = 0 := by
      have := congrArg (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom h0
      simpa using this
    rw [hz, Scheme.basicOpen_zero] at h1
    obtain ⟨pt⟩ : Nonempty (Sp ℂ) := inferInstance
    exact (h1 (show pt ∈ (⊤ : (Sp ℂ).Opens) from trivial)).elim

/- English proof (translation)
Simplify using `only [valAt', dif_pos h, valAt, map_mul]`.
-/
private theorem valAt'_mul_of_top_le_preimage_open {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {U : X.Opens}
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f f' : Γ(X, U)) : valAt' x U (f * f') = valAt' x U f * valAt' x U f' := by
  simp only [valAt', dif_pos h, valAt, map_mul]

/- English proof (translation)
Establish `hle : U ≤ X.hom ⁻¹ᵁ ⊤` using `by simp`. Set `φ : ℂ →+* Γ(X.left, U)` to `(X.hom.appLE ⊤ U hle).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom`. Establish `hft : φ.FiniteType`. Use `RingHom.FiniteType.comp (X.hom.finiteType_appLE (isAffineOpen_top _) hU hle) ?_` and prove the remaining obligations. Conclude with `RingHom.FiniteType.of_surjective _ (fun x => ⟨(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom x, by simp⟩)`.

Use `letI : Algebra ℂ Γ(X.left, U) := φ.toAlgebra`. Establish `: Algebra.FiniteType ℂ Γ(X.left, U)` using `hft`. Establish `: IsJacobsonRing Γ(X.left, U)` using `isJacobsonRing_of_finiteType (A := ℂ)`. Establish `hjac : p.jacobson = p` using `isJacobsonRing_iff_prime_eq.1 this p inferInstance`. Choose the witnesses or unpack the hypotheses as in `⟨m, ⟨hpm, hm⟩, hsm⟩ : ∃ m : Ideal Γ(X.left, U), (p ≤ m ∧ m.IsMaximal) ∧ s ∉ m := by`.

Assume the negation of the conclusion as `hno`. Use `push Not at hno`. Apply `hs` to reduce the goal to its premises. Rewrite using `[← hjac, Ideal.jacobson, Ideal.mem_sInf]`. Conclude with `fun J hJ => hno J hJ`.

Use `letI : Field (Γ(X.left, U) ⧸ m) := Ideal.Quotient.field m`. Establish `: Algebra.FiniteType ℂ (Γ(X.left, U) ⧸ m)` using `Algebra.FiniteType.trans (S := Γ(X.left, U)) inferInstance inferInstance`. Establish `: Module.Finite ℂ (Γ(X.left, U) ⧸ m)` using `finite_of_finite_type_of_isJacobsonRing ℂ _`. Set `E : ℂ ≃+* (Γ(X.left, U) ⧸ m)` to `RingEquiv.ofBijective (algebraMap ℂ _) IsAlgClosed.algebraMap_bijective_of_isIntegral`. Set `e : Γ(X.left, U) →+* ℂ` to `E.symm.toRingHom.comp (Ideal.Quotient.mk m)`.

Establish `he : ∀ a, e (constFn X.hom U a) = a` using `fun a => by`. Express the relevant statement in the definitionally equal form `E.symm (Ideal.Quotient.mk m (φ a)) = a`. Rewrite using `[RingEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Take `⟨x, ⟨hx, hxv⟩, -⟩` from `existsUnique_point_of_ringHom X U hU e he`.

Use `⟨x, hx, ?_, fun r hr => ?_⟩` and prove the remaining obligations. Rewrite using `[hxv]`. Introduce `h0`. Apply `hsm` to reduce the goal to its premises. Establish `: Ideal.Quotient.mk m s = 0`.

Use `congrArg E h0` as an intermediate fact. Simplify `this` using `[e]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 this`. Rewrite using `[hxv]`. Simplify using `[e, Ideal.Quotient.eq_zero_iff_mem.2 (hpm hr)]`.
-/
theorem exists_point_of_prime (X : Over (Sp ℂ)) [LocallyOfFiniteType X.hom] {U : X.left.Opens}
    (hU : IsAffineOpen U) (p : Ideal Γ(X.left, U)) [p.IsPrime] {s : Γ(X.left, U)} (hs : s ∉ p) :
    ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ X, ⊤ ≤ x.left ⁻¹ᵁ U ∧ valAt' x.left U s ≠ 0 ∧
      ∀ r ∈ p, valAt' x.left U r = 0 := by
  classical
  have hle : U ≤ X.hom ⁻¹ᵁ ⊤ := by simp
  let φ : ℂ →+* Γ(X.left, U) :=
    (X.hom.appLE ⊤ U hle).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  have hft : φ.FiniteType := by
    refine RingHom.FiniteType.comp (X.hom.finiteType_appLE (isAffineOpen_top _) hU hle) ?_
    exact RingHom.FiniteType.of_surjective _
      (fun x => ⟨(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom x, by simp⟩)
  letI : Algebra ℂ Γ(X.left, U) := φ.toAlgebra
  have : Algebra.FiniteType ℂ Γ(X.left, U) := hft
  have : IsJacobsonRing Γ(X.left, U) := isJacobsonRing_of_finiteType (A := ℂ)

  have hjac : p.jacobson = p := isJacobsonRing_iff_prime_eq.1 this p inferInstance
  obtain ⟨m, ⟨hpm, hm⟩, hsm⟩ : ∃ m : Ideal Γ(X.left, U), (p ≤ m ∧ m.IsMaximal) ∧ s ∉ m := by
    by_contra hno
    push Not at hno
    apply hs
    rw [← hjac, Ideal.jacobson, Ideal.mem_sInf]
    exact fun J hJ => hno J hJ
  letI : Field (Γ(X.left, U) ⧸ m) := Ideal.Quotient.field m
  have : Algebra.FiniteType ℂ (Γ(X.left, U) ⧸ m) :=
    Algebra.FiniteType.trans (S := Γ(X.left, U)) inferInstance inferInstance
  have : Module.Finite ℂ (Γ(X.left, U) ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ _
  let E : ℂ ≃+* (Γ(X.left, U) ⧸ m) :=
    RingEquiv.ofBijective (algebraMap ℂ _) IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : Γ(X.left, U) →+* ℂ := E.symm.toRingHom.comp (Ideal.Quotient.mk m)
  have he : ∀ a, e (constFn X.hom U a) = a := fun a => by
    change E.symm (Ideal.Quotient.mk m (φ a)) = a
    rw [RingEquiv.symm_apply_eq]
    rfl
  obtain ⟨x, ⟨hx, hxv⟩, -⟩ := existsUnique_point_of_ringHom X U hU e he
  refine ⟨x, hx, ?_, fun r hr => ?_⟩
  · rw [hxv]
    intro h0
    apply hsm
    have : Ideal.Quotient.mk m s = 0 := by
      have := congrArg E h0
      simpa [e] using this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  · rw [hxv]
    simp [e, Ideal.Quotient.eq_zero_iff_mem.2 (hpm hr)]

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

/- English proof (translation)
Use `set V : Set (Fin g → ℂ) := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ W} with hVdef`. Take `⟨pt⟩ : Nonempty (Sp ℂ)` from `inferInstance`. Establish `hpt : ∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X) (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x.base pt ∈ U`. Introduce `X x U`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `h (show pt ∈ (⊤ : (Sp ℂ).Opens) from trivial)`. Introduce `h q _`. Rewrite using `[Subsingleton.elim q pt]`. Conclude with `h`.

Assume the negation of the conclusion as `hnd`. Use `set F := closure V with hF`. Establish `hFne : F ≠ Set.univ` using `fun h => hnd (dense_iff_closure_eq.2 h)`. Establish `hFn : F.Nonempty`. Take `⟨z, hz⟩` from `hW`.

Conclude with `⟨z, subset_closure hz⟩`. Choose the witnesses or unpack the hypotheses as in `⟨zs, hzs⟩ : (frontier F).Nonempty := by`. Rewrite using `[Set.nonempty_iff_ne_empty]`. Introduce `h0`. Break down `isClopen_iff.1 (isClopen_iff_frontier_eq_empty.2 h0) with h1 | h1` into its components or cases.

Conclude with `hFn.ne_empty h1`. Conclude with `hFne h1`. Rewrite `hzs` using `[isClosed_closure.frontier_eq]`. Take `⟨hzsF, hzsi⟩` from `hzs`. Take `⟨U0, hU0a, hxU0, -⟩` from `TopologicalSpace.Opens.isBasis_iff_nbhd.1 (Scheme.isBasis_affineOpens A.left) (show (u.ex zs).left.base pt ∈ (⊤ : A.left.Opens) from trivial)`.

Establish `hU0 : IsAffineOpen U0` using `hU0a`. Establish `hV0o : IsOpen {z : Fin g → ℂ | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U0}` using `(u.8 U0 0).1`. Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.1 hV0o zs ((hpt _ _ _).2 hxU0)`. Take `⟨z1, hz1V, hz1d⟩` from `Metric.mem_closure_iff.1 hzsF ε hε`. Establish `hz1b : z1 ∈ Metric.ball zs ε` using `by rw [Metric.mem_ball, dist_comm]; exact hz1d`.

Choose the witnesses or unpack the hypotheses as in `⟨z0, hz0b, hz0F⟩ : ∃ z0 ∈ Metric.ball zs ε, z0 ∉ F := by`. Assume the negation of the conclusion as `hno`. Use `push Not at hno`. Conclude with `hzsi (mem_interior.2 ⟨Metric.ball zs ε, hno, Metric.isOpen_ball, Metric.mem_ball_self hε⟩)`. Take `⟨δ, hδ, hδb⟩` from `Metric.isOpen_iff.1 (isClosed_closure.isOpen_compl.inter Metric.isOpen_ball) z0 ⟨hz0F, hz0b⟩`.

Establish `hx1 : (u.ex z1).left.base pt ∈ W ⊓ U0` using `⟨(hpt _ _ _).1 hz1V, (hpt _ _ _).1 (hball hz1b)⟩`. Take `⟨f, hfW, hf1⟩` from `hU0.exists_basicOpen_le (V := W ⊓ U0) ⟨_, hx1⟩ hx1.2`. Establish `hf1' : valAt' (u.ex z1).left U0 f ≠ 0` using `(valAt'_ne_zero_iff_top_le_preimage_basicOpen _ (hball hz1b) f).2 ((hpt _ _ _).2 hf1)`. Establish `hf0 : ∀ z ∈ Metric.ball z0 δ, valAt' (u.ex z).left U0 f = 0`. Introduce `z hz`.

Take `⟨hzF, hzb⟩` from `hδb hz`. Assume the negation of the conclusion as `hne`. Establish `h1` using `(valAt'_ne_zero_iff_top_le_preimage_basicOpen _ (hball hzb) f).1 hne`. Conclude with `hzF (subset_closure ((hpt _ _ _).2 (hfW ((hpt _ _ _).1 h1)).1))`. Set `ℓ : ℂ → (Fin g → ℂ)` to `fun t => z0 + t • (z1 - z0)`.

Establish `hℓd : Differentiable ℂ ℓ` using `by fun_prop`. Set `T : Set ℂ` to `ℓ ⁻¹' Metric.ball zs ε`. Establish `hTo : IsOpen T` using `Metric.isOpen_ball.preimage hℓd.continuous`. Establish `hTc : Convex ℝ T`. Introduce `t₁ h₁ t₂ h₂ α β hα hβ hαβ`.

Establish `hc` using `convex_ball zs ε h₁ h₂ hα hβ hαβ`. Establish `hαβ' : (α : ℂ) + (β : ℂ) = 1` using `by exact_mod_cast hαβ`. Express the relevant statement in the definitionally equal form `ℓ (α • t₁ + β • t₂) ∈ Metric.ball zs ε`. Use `hc using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i`.

Simplify using `only [ℓ, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Complex.real_smul]`. Take the linear combination `(-(z0 i)) * hαβ'`. Establish `hℓ0 : ℓ 0 = z0` using `by simp [ℓ]`. Establish `hℓ1 : ℓ 1 = z1` using `by simp [ℓ]`. Establish `h0T : (0 : ℂ) ∈ T`.

Express the relevant statement in the definitionally equal form `ℓ 0 ∈ Metric.ball zs ε`. Rewrite using `[hℓ0]`. Conclude with `hz0b`. Set `h : ℂ → ℂ` to `fun t => valAt' (u.ex (ℓ t)).left U0 f`. Establish `hd : DifferentiableOn ℂ h T` using `(u.8 U0 f).2.comp hℓd.differentiableOn (fun t ht => hball ht)`.

Establish `hev : h =ᶠ[nhds 0] 0`. Establish `hmem : ℓ ⁻¹' Metric.ball z0 δ ∈ nhds (0 : ℂ)` using `hℓd.continuous.continuousAt.preimage_mem_nhds (by rw [hℓ0]; exact Metric.ball_mem_nhds z0 hδ)`. Use `filter_upwards [hmem] with t ht`. Conclude with `hf0 _ ht`. Establish `hzero` using `(hd.analyticOnNhd hTo).eqOn_zero_of_preconnected_of_eventuallyEq_zero hTc.isPreconnected h0T hev`.

Establish `h1T : (1 : ℂ) ∈ T`. Express the relevant statement in the definitionally equal form `ℓ 1 ∈ Metric.ball zs ε`. Rewrite using `[hℓ1]`. Conclude with `hz1b`. Apply `hf1'` to reduce the goal to its premises.

Use `hzero h1T` as an intermediate fact. Simplify using `only [h, hℓ1, Pi.zero_apply] at this`. Conclude with `this`.
-/
theorem dense_preimage (W : A.left.Opens) (hW : ∃ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ W) :
    Dense {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ W} := by
  classical
  set V : Set (Fin g → ℂ) := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ W} with hVdef
  obtain ⟨pt⟩ : Nonempty (Sp ℂ) := inferInstance
  have hpt : ∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X) (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x.base pt ∈ U := by
    intro X x U
    constructor
    · intro h
      exact h (show pt ∈ (⊤ : (Sp ℂ).Opens) from trivial)
    · intro h q _
      rw [Subsingleton.elim q pt]
      exact h
  by_contra hnd
  set F := closure V with hF
  have hFne : F ≠ Set.univ := fun h => hnd (dense_iff_closure_eq.2 h)
  have hFn : F.Nonempty := by
    obtain ⟨z, hz⟩ := hW
    exact ⟨z, subset_closure hz⟩

  obtain ⟨zs, hzs⟩ : (frontier F).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h0
    rcases isClopen_iff.1 (isClopen_iff_frontier_eq_empty.2 h0) with h1 | h1
    · exact hFn.ne_empty h1
    · exact hFne h1
  rw [isClosed_closure.frontier_eq] at hzs
  obtain ⟨hzsF, hzsi⟩ := hzs

  obtain ⟨U0, hU0a, hxU0, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 (Scheme.isBasis_affineOpens A.left)
    (show (u.ex zs).left.base pt ∈ (⊤ : A.left.Opens) from trivial)
  have hU0 : IsAffineOpen U0 := hU0a
  have hV0o : IsOpen {z : Fin g → ℂ | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U0} := (u.8 U0 0).1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV0o zs ((hpt _ _ _).2 hxU0)
  obtain ⟨z1, hz1V, hz1d⟩ := Metric.mem_closure_iff.1 hzsF ε hε
  have hz1b : z1 ∈ Metric.ball zs ε := by rw [Metric.mem_ball, dist_comm]; exact hz1d
  obtain ⟨z0, hz0b, hz0F⟩ : ∃ z0 ∈ Metric.ball zs ε, z0 ∉ F := by
    by_contra hno
    push Not at hno
    exact hzsi (mem_interior.2 ⟨Metric.ball zs ε, hno, Metric.isOpen_ball, Metric.mem_ball_self hε⟩)
  obtain ⟨δ, hδ, hδb⟩ := Metric.isOpen_iff.1
    (isClosed_closure.isOpen_compl.inter Metric.isOpen_ball) z0 ⟨hz0F, hz0b⟩

  have hx1 : (u.ex z1).left.base pt ∈ W ⊓ U0 := ⟨(hpt _ _ _).1 hz1V, (hpt _ _ _).1 (hball hz1b)⟩
  obtain ⟨f, hfW, hf1⟩ := hU0.exists_basicOpen_le (V := W ⊓ U0) ⟨_, hx1⟩ hx1.2
  have hf1' : valAt' (u.ex z1).left U0 f ≠ 0 :=
    (valAt'_ne_zero_iff_top_le_preimage_basicOpen _ (hball hz1b) f).2 ((hpt _ _ _).2 hf1)
  have hf0 : ∀ z ∈ Metric.ball z0 δ, valAt' (u.ex z).left U0 f = 0 := by
    intro z hz
    obtain ⟨hzF, hzb⟩ := hδb hz
    by_contra hne
    have h1 := (valAt'_ne_zero_iff_top_le_preimage_basicOpen _ (hball hzb) f).1 hne
    exact hzF (subset_closure ((hpt _ _ _).2 (hfW ((hpt _ _ _).1 h1)).1))

  let ℓ : ℂ → (Fin g → ℂ) := fun t => z0 + t • (z1 - z0)
  have hℓd : Differentiable ℂ ℓ := by fun_prop
  let T : Set ℂ := ℓ ⁻¹' Metric.ball zs ε
  have hTo : IsOpen T := Metric.isOpen_ball.preimage hℓd.continuous
  have hTc : Convex ℝ T := by
    intro t₁ h₁ t₂ h₂ α β hα hβ hαβ
    have hc := convex_ball zs ε h₁ h₂ hα hβ hαβ
    have hαβ' : (α : ℂ) + (β : ℂ) = 1 := by exact_mod_cast hαβ
    change ℓ (α • t₁ + β • t₂) ∈ Metric.ball zs ε
    convert hc using 1
    ext i
    simp only [ℓ, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Complex.real_smul]
    linear_combination (-(z0 i)) * hαβ'
  have hℓ0 : ℓ 0 = z0 := by simp [ℓ]
  have hℓ1 : ℓ 1 = z1 := by simp [ℓ]
  have h0T : (0 : ℂ) ∈ T := by
    change ℓ 0 ∈ Metric.ball zs ε
    rw [hℓ0]; exact hz0b
  let h : ℂ → ℂ := fun t => valAt' (u.ex (ℓ t)).left U0 f
  have hd : DifferentiableOn ℂ h T :=
    (u.8 U0 f).2.comp hℓd.differentiableOn (fun t ht => hball ht)
  have hev : h =ᶠ[nhds 0] 0 := by
    have hmem : ℓ ⁻¹' Metric.ball z0 δ ∈ nhds (0 : ℂ) :=
      hℓd.continuous.continuousAt.preimage_mem_nhds (by rw [hℓ0]; exact Metric.ball_mem_nhds z0 hδ)
    filter_upwards [hmem] with t ht
    exact hf0 _ ht
  have hzero := (hd.analyticOnNhd hTo).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    hTc.isPreconnected h0T hev
  have h1T : (1 : ℂ) ∈ T := by
    change ℓ 1 ∈ Metric.ball zs ε
    rw [hℓ1]; exact hz1b
  apply hf1'
  have := hzero h1T
  simp only [h, hℓ1, Pi.zero_apply] at this
  exact this

end GlobalTheory.ContinuousQuotient

namespace GlobalTheory

open ContinuousQuotient in

/- English proof (translation)
Introduce `P L u U a b φ _ hU hb hφc hφ`. Establish `hsm : Smooth P.A.hom` using `P.5.smooth`. Take `⟨-, hnorm, hnoeth⟩` from `isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field ℂ P.A.left P.A.hom hsm`. Establish `hint : IsIntegral P.A.left` using `polAV_isIntegral_of_isAlgClosed ℂ P`. Establish `hne : Nonempty U`.

Break down `U.1.eq_empty_or_nonempty with h | h` into its components or cases. Establish `hU0 : U = ⊥` using `SetLike.ext' h`. Establish `: Subsingleton Γ(P.A.left, U)` using `CommRingCat.subsingleton_of_isTerminal (P.A.left.sheaf.isTerminalOfEqEmpty hU0)`. Conclude with `absurd (Subsingleton.elim b 0) hb`. Simplify using `using h`.

Establish `: IsNoetherianRing Γ(P.A.left, U)` using `hnoeth.component_noetherian ⟨U, hU⟩`. Establish `: IsIntegrallyClosed Γ(P.A.left, U)`. Use `IsIntegrallyClosed.of_localization_maximal fun q _ hqm => ?_` and prove the remaining obligations. Set `y : PrimeSpectrum Γ(P.A.left, U)` to `⟨q, hqm.isPrime⟩`. Establish `hy : hU.fromSpec y ∈ U`.

Rewrite using `[← SetLike.mem_coe, ← hU.range_fromSpec]`. Conclude with `⟨y, rfl⟩`. Use `letI := TopCat.Presheaf.algebra_section_stalk P.A.left.presheaf ⟨hU.fromSpec y, hy⟩`. Establish `: IsLocalization.AtPrime (P.A.left.presheaf.stalk (hU.fromSpec y)) q` using `hU.isLocalization_stalk' y hy`. Take `⟨_, hic⟩` from `hnorm (hU.fromSpec y)`.

Conclude with `IsIntegrallyClosed.of_equiv (IsLocalization.algEquiv q.primeCompl (P.A.left.presheaf.stalk (hU.fromSpec y)) (Localization.AtPrime q)).toRingEquiv`. Assume the negation of the conclusion as `hnd`. Take `⟨p, hp, s, r, hs, hr, hbs⟩` from `ContinuousQuotient.exists_prime_of_not_dvd (a := a) hb (by rintro ⟨c, hc⟩; exact hnd ⟨c, by rw [hc, _root_.mul_comm]⟩)`. Establish `hr0 : r ≠ 0`. Introduce and unpack `rfl`.

Apply `hs` to reduce the goal to its premises. Establish `h0 : b * s = 0` using `by rw [hbs, mul_zero]`. Break down `mul_eq_zero.1 h0 with h0 | h0` into its components or cases. Conclude with `absurd h0 hb`. Rewrite using `[h0]`.

Conclude with `p.zero_mem`. Take `⟨x, hxU, hxs, hxp⟩` from `ContinuousQuotient.exists_point_of_prime P.A hU p hs`. Take `⟨z₀, hz₀⟩` from `u.3 x`. Take `⟨y, hyU, hyrb, -⟩` from `ContinuousQuotient.exists_point_of_prime P.A hU ⊥ (s := r * b) (by rw [Ideal.mem_bot]; exact mul_ne_zero hr0 hb)`. Take `⟨z₁, hz₁⟩` from `u.3 y`.

Establish `hD` using `ContinuousQuotient.dense_preimage u (P.A.left.basicOpen (r * b)) ⟨z₁, by rw [hz₁]; exact (valAt'_ne_zero_iff_top_le_preimage_basicOpen y.left hyU _).1 hyrb⟩`. Use `set O : Set (Fin P.g → ℂ) := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U} with hO`. Use `set D : Set (Fin P.g → ℂ) := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.A.left.basicOpen (r * b)} with hDdef`. Establish `hOo : IsOpen O` using `(u.8 U s).1`. Establish `hDO : D ⊆ O` using `fun z hz => hz.trans (Scheme.Hom.preimage_mono _ (P.A.left.basicOpen_le (r * b)))`.

Establish `hz₀O : z₀ ∈ O`. Express the relevant statement in the definitionally equal form `⊤ ≤ (u.ex z₀).left ⁻¹ᵁ U`. Rewrite using `[hz₀]`. Conclude with `hxU`. Set `G : (Fin P.g → ℂ) → ℂ` to `fun z => valAt' (u.ex z).left U s - φ z * valAt' (u.ex z).left U r`.

Establish `hG : ContinuousWithinAt G O z₀` using `(((u.8 U s).2.continuousOn).sub (hφc.mul (u.8 U r).2.continuousOn)) z₀ hz₀O`. Establish `hG0 : ∀ z ∈ O ∩ D, G z = 0`. Introduce and unpack `z ⟨hzO, hzD⟩`. Establish `hrb` using `(valAt'_ne_zero_iff_top_le_preimage_basicOpen (u.ex z).left hzO (r * b)).2 hzD`. Rewrite `hrb` using `[valAt'_mul_of_top_le_preimage_open _ hzO]`.

Establish `hbz : valAt' (u.ex z).left U b ≠ 0` using `right_ne_zero_of_mul hrb`. Establish `e1` using `congrArg (valAt' (u.ex z).left U) hbs`. Rewrite `e1` using `[valAt'_mul_of_top_le_preimage_open _ hzO, valAt'_mul_of_top_le_preimage_open _ hzO, hφ z hzO]`. Establish `e2 : valAt' (u.ex z).left U b * G z = 0`. Simplify using `only [G]`.

Rewrite using `[_root_.mul_sub, e1]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `(mul_eq_zero.1 e2).resolve_left hbz`. Establish `hcl : z₀ ∈ closure (O ∩ D)` using `hD.open_subset_closure_inter hOo hz₀O`. Establish `hGz : G z₀ ∈ closure (G '' (O ∩ D))` using `(hG.mono Set.inter_subset_left).mem_closure_image hcl`.

Establish `hsub : G '' (O ∩ D) ⊆ {0}`. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Conclude with `hG0 z hz`. Establish `hGz0 : G z₀ = 0`. Simplify using `using closure_mono hsub hGz`.

Apply `hxs` to reduce the goal to its premises. Establish `hrx : valAt' x.left U r = 0` using `hxp r hr`. Simplify using `only [G, hz₀, hrx, mul_zero, sub_zero] at hGz0`. Conclude with `hGz0`.
-/
theorem exists_eq_mul_of_continuousOn_quotient :
    ∀ (P : Out.PolAV (Sp ℂ)) (L : LB P.A.left) (u : HolUnif P.A L P.g) (U : P.A.left.Opens) (a b : Γ(P.A.left, U)) (φ : (Fin P.g → ℂ) → ℂ), Out.Laws → IsAffineOpen U → b ≠ 0 → ContinuousOn φ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U} → (∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ U → valAt' (u.ex z).left U a = φ z * valAt' (u.ex z).left U b) → ∃ c : Γ(P.A.left, U), a = c * b := by
  intro P L u U a b φ _ hU hb hφc hφ
  classical
  have hsm : Smooth P.A.hom := P.5.smooth
  obtain ⟨-, hnorm, hnoeth⟩ :=
    isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field ℂ P.A.left P.A.hom hsm
  have hint : IsIntegral P.A.left := polAV_isIntegral_of_isAlgClosed ℂ P
  have hne : Nonempty U := by
    rcases U.1.eq_empty_or_nonempty with h | h
    · have hU0 : U = ⊥ := SetLike.ext' h
      have : Subsingleton Γ(P.A.left, U) :=
        CommRingCat.subsingleton_of_isTerminal (P.A.left.sheaf.isTerminalOfEqEmpty hU0)
      exact absurd (Subsingleton.elim b 0) hb
    · simpa using h
  have : IsNoetherianRing Γ(P.A.left, U) := hnoeth.component_noetherian ⟨U, hU⟩
  have : IsIntegrallyClosed Γ(P.A.left, U) := by
    refine IsIntegrallyClosed.of_localization_maximal fun q _ hqm => ?_
    let y : PrimeSpectrum Γ(P.A.left, U) := ⟨q, hqm.isPrime⟩
    have hy : hU.fromSpec y ∈ U := by
      rw [← SetLike.mem_coe, ← hU.range_fromSpec]; exact ⟨y, rfl⟩
    letI := TopCat.Presheaf.algebra_section_stalk P.A.left.presheaf ⟨hU.fromSpec y, hy⟩
    have : IsLocalization.AtPrime (P.A.left.presheaf.stalk (hU.fromSpec y)) q :=
      hU.isLocalization_stalk' y hy
    obtain ⟨_, hic⟩ := hnorm (hU.fromSpec y)
    exact IsIntegrallyClosed.of_equiv (IsLocalization.algEquiv q.primeCompl
      (P.A.left.presheaf.stalk (hU.fromSpec y)) (Localization.AtPrime q)).toRingEquiv
  by_contra hnd
  obtain ⟨p, hp, s, r, hs, hr, hbs⟩ := ContinuousQuotient.exists_prime_of_not_dvd (a := a) hb
    (by rintro ⟨c, hc⟩; exact hnd ⟨c, by rw [hc, _root_.mul_comm]⟩)
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hs
    have h0 : b * s = 0 := by rw [hbs, mul_zero]
    rcases mul_eq_zero.1 h0 with h0 | h0
    · exact absurd h0 hb
    · rw [h0]; exact p.zero_mem

  obtain ⟨x, hxU, hxs, hxp⟩ := ContinuousQuotient.exists_point_of_prime P.A hU p hs
  obtain ⟨z₀, hz₀⟩ := u.3 x

  obtain ⟨y, hyU, hyrb, -⟩ := ContinuousQuotient.exists_point_of_prime P.A hU ⊥ (s := r * b)
    (by rw [Ideal.mem_bot]; exact mul_ne_zero hr0 hb)
  obtain ⟨z₁, hz₁⟩ := u.3 y
  have hD := ContinuousQuotient.dense_preimage u (P.A.left.basicOpen (r * b))
    ⟨z₁, by rw [hz₁]; exact (valAt'_ne_zero_iff_top_le_preimage_basicOpen y.left hyU _).1 hyrb⟩
  set O : Set (Fin P.g → ℂ) := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U} with hO
  set D : Set (Fin P.g → ℂ) := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.A.left.basicOpen (r * b)} with hDdef
  have hOo : IsOpen O := (u.8 U s).1
  have hDO : D ⊆ O := fun z hz =>
    hz.trans (Scheme.Hom.preimage_mono _ (P.A.left.basicOpen_le (r * b)))
  have hz₀O : z₀ ∈ O := by
    change ⊤ ≤ (u.ex z₀).left ⁻¹ᵁ U
    rw [hz₀]; exact hxU
  let G : (Fin P.g → ℂ) → ℂ := fun z =>
    valAt' (u.ex z).left U s - φ z * valAt' (u.ex z).left U r
  have hG : ContinuousWithinAt G O z₀ :=
    (((u.8 U s).2.continuousOn).sub (hφc.mul (u.8 U r).2.continuousOn)) z₀ hz₀O
  have hG0 : ∀ z ∈ O ∩ D, G z = 0 := by
    rintro z ⟨hzO, hzD⟩
    have hrb := (valAt'_ne_zero_iff_top_le_preimage_basicOpen (u.ex z).left hzO (r * b)).2 hzD
    rw [valAt'_mul_of_top_le_preimage_open _ hzO] at hrb
    have hbz : valAt' (u.ex z).left U b ≠ 0 := right_ne_zero_of_mul hrb
    have e1 := congrArg (valAt' (u.ex z).left U) hbs
    rw [valAt'_mul_of_top_le_preimage_open _ hzO, valAt'_mul_of_top_le_preimage_open _ hzO, hφ z hzO] at e1
    have e2 : valAt' (u.ex z).left U b * G z = 0 := by
      simp only [G]
      rw [_root_.mul_sub, e1]
      ring
    exact (mul_eq_zero.1 e2).resolve_left hbz
  have hcl : z₀ ∈ closure (O ∩ D) := hD.open_subset_closure_inter hOo hz₀O
  have hGz : G z₀ ∈ closure (G '' (O ∩ D)) := (hG.mono Set.inter_subset_left).mem_closure_image hcl
  have hsub : G '' (O ∩ D) ⊆ {0} := by
    rintro _ ⟨z, hz, rfl⟩
    exact hG0 z hz
  have hGz0 : G z₀ = 0 := by
    simpa using closure_mono hsub hGz
  apply hxs
  have hrx : valAt' x.left U r = 0 := hxp r hr
  simp only [G, hz₀, hrx, mul_zero, sub_zero] at hGz0
  exact hGz0

end GlobalTheory
