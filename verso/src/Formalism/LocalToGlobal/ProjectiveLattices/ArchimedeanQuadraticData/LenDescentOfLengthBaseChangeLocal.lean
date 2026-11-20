import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QCoreSt
import Formalism.FilteredPoleLength.LocalDescentLevels.LengthBaseChange
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.TieLDA
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.TieLDB

namespace Formalism.L2.Pj.QAt

namespace TieLD

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct

attribute [local instance] TieLDA.modT TieLDA.modR

/- English proof (translation)
Establish `h0 : IsLocalRing.maximalIdeal T ≠ ⊥` using `IsDiscreteValuationRing.not_a_field T`. Establish `h1 : IsLocalRing.maximalIdeal T ≠ ⊤` using `(IsLocalRing.maximalIdeal.isMaximal T).ne_top`. Conclude with `(Ideal.pow_right_strictAnti _ h0 h1).injective h`.
-/
theorem pow_maximalIdeal_inj {T : Type*} [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    {a b : ℕ} (h : IsLocalRing.maximalIdeal T ^ a = IsLocalRing.maximalIdeal T ^ b) : a = b := by
  have h0 : IsLocalRing.maximalIdeal T ≠ ⊥ := IsDiscreteValuationRing.not_a_field T
  have h1 : IsLocalRing.maximalIdeal T ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal T).ne_top
  exact (Ideal.pow_right_strictAnti _ h0 h1).injective h

variable {K K₁ : Type} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]

noncomputable abbrev Tw (w : HeightOneSpectrum (𝓞 K₁)) : Subring K₁ := (w.valuationSubringAtPrime K₁).toSubring

noncomputable abbrev algCT (w : HeightOneSpectrum (𝓞 K₁)) : Algebra (𝓞 K₁) (Tw w) :=
  inferInstanceAs (Algebra (𝓞 K₁) (w.valuationSubringAtPrime K₁))

attribute [local instance] algCT

/- English proof (translation)
The claim follows from `inferInstanceAs (IsLocalization w.asIdeal.primeCompl (w.valuationSubringAtPrime K₁))`.
-/
theorem locT (w : HeightOneSpectrum (𝓞 K₁)) : IsLocalization w.asIdeal.primeCompl (Tw w) :=
  inferInstanceAs (IsLocalization w.asIdeal.primeCompl (w.valuationSubringAtPrime K₁))

attribute [local instance] locT

/- English proof (translation)
Use `first`. Consider the case `exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K₁) (NumberField.RingOfIntegers.not_isField K₁) w.ne_bot (Tw w)`. Consider the case `exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain w.ne_bot (Tw w)`. Consider the case `exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K₁) w.ne_bot (Tw w)`.
-/
theorem dvrT (w : HeightOneSpectrum (𝓞 K₁)) : IsDiscreteValuationRing (Tw w) := by
  first
    | exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K₁) (NumberField.RingOfIntegers.not_isField K₁) w.ne_bot (Tw w)
    | exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain w.ne_bot (Tw w)
    | exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K₁) w.ne_bot (Tw w)

attribute [local instance] dvrT

/- English proof (translation)
Use `first`. Consider the case `exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) (NumberField.RingOfIntegers.not_isField K) la.ne_bot _`. Consider the case `exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain la.ne_bot _`. Consider the case `exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) la.ne_bot _`.
-/
theorem dvrLa (la : HeightOneSpectrum (𝓞 K)) :
    IsDiscreteValuationRing (Localization.AtPrime la.asIdeal) := by
  first
    | exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) (NumberField.RingOfIntegers.not_isField K) la.ne_bot _
    | exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain la.ne_bot _
    | exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) la.ne_bot _

attribute [local instance] dvrLa

noncomputable abbrev algLaK (la : HeightOneSpectrum (𝓞 K)) :
    Algebra (Localization.AtPrime la.asIdeal) K :=
  IsLocalization.localizationAlgebraOfSubmonoidLe _ K la.asIdeal.primeCompl
    (nonZeroDivisors (𝓞 K)) la.asIdeal.primeCompl_le_nonZeroDivisors

attribute [local instance] algLaK

/- English proof (translation)
Use `first`. Consider the case `exact IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ _`. Consider the case `exact IsLocalization.localization_isScalarTower_of_submonoid_le (Localization.AtPrime la.asIdeal) K _ _ la.asIdeal.primeCompl_le_nonZeroDivisors`. Consider the case `(apply IsScalarTower.of_algebraMap_eq; intro x; exact (IsLocalization.map_eq _ x).symm)`.
-/
theorem towerLaK (la : HeightOneSpectrum (𝓞 K)) :
    IsScalarTower (𝓞 K) (Localization.AtPrime la.asIdeal) K := by
  first
    | exact IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ _
    | exact IsLocalization.localization_isScalarTower_of_submonoid_le (Localization.AtPrime la.asIdeal) K _ _ la.asIdeal.primeCompl_le_nonZeroDivisors
    | (apply IsScalarTower.of_algebraMap_eq; intro x; exact (IsLocalization.map_eq _ x).symm)

attribute [local instance] towerLaK

/- English proof (translation)
Use `first`. Consider the case `exact IsFractionRing.isFractionRing_of_isLocalization la.asIdeal.primeCompl _ _ la.asIdeal.primeCompl_le_nonZeroDivisors`. Consider the case `exact IsLocalization.isFractionRing_of_isDomain_of_isLocalization la.asIdeal.primeCompl _ _`. Consider the case `exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization la.asIdeal.primeCompl _ _`.
-/
theorem fracLaK (la : HeightOneSpectrum (𝓞 K)) :
    IsFractionRing (Localization.AtPrime la.asIdeal) K := by
  first
    | exact IsFractionRing.isFractionRing_of_isLocalization la.asIdeal.primeCompl _ _ la.asIdeal.primeCompl_le_nonZeroDivisors
    | exact IsLocalization.isFractionRing_of_isDomain_of_isLocalization la.asIdeal.primeCompl _ _
    | exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization la.asIdeal.primeCompl _ _

attribute [local instance] fracLaK

/- English proof (translation)
Introduce `x hx`. Unfold `LiesOver at hw`. Rewrite using `[Submonoid.mem_comap, Ideal.mem_primeCompl_iff]`. Rewrite `hx` using `[Ideal.mem_primeCompl_iff]`. Introduce `hxw`.

Apply `hx` to reduce the goal to its premises. Rewrite using `[← hw]`. Conclude with `Ideal.mem_comap.mpr hxw`.
-/
theorem primeCompl_le (la : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K₁))
    (hw : LiesOver w la) :
    la.asIdeal.primeCompl ≤ w.asIdeal.primeCompl.comap (algebraMap (𝓞 K) (𝓞 K₁)) := by
  intro x hx
  unfold LiesOver at hw
  rw [Submonoid.mem_comap, Ideal.mem_primeCompl_iff]
  rw [Ideal.mem_primeCompl_iff] at hx
  intro hxw
  apply hx
  rw [← hw]
  exact Ideal.mem_comap.mpr hxw

noncomputable def mapLaT (la : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K₁))
    (hw : LiesOver w la) : Localization.AtPrime la.asIdeal →+* Tw w :=
  IsLocalization.map (M := la.asIdeal.primeCompl) (S := Localization.AtPrime la.asIdeal) (Tw w)
    (algebraMap (𝓞 K) (𝓞 K₁)) (T := w.asIdeal.primeCompl) (primeCompl_le la w hw)

/- English proof (translation)
Establish `key : (Tw w).subtype.comp (mapLaT la w hw) = (algebraMap K K₁).comp (algebraMap (Localization.AtPrime la.asIdeal) K)`. Apply `IsLocalization.ringHom_ext la.asIdeal.primeCompl` to reduce the goal to its premises. Use extensionality with `x`. Simplify using `only [RingHom.comp_apply, mapLaT, IsLocalization.map_eq]`. Rewrite using `[← IsScalarTower.algebraMap_apply (𝓞 K) (Localization.AtPrime la.asIdeal) K]`.

Use `first`. Consider the case `rfl`. Consider the case `simp`. Consider the case `(norm_cast; simp)`. Consider the case `exact (trivial : True)`.

Conclude with `RingHom.congr_fun key r`.
-/
theorem mapLaT_coe (la : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K₁))
    (hw : LiesOver w la) (r : Localization.AtPrime la.asIdeal) :
    ((mapLaT la w hw r : Tw w) : K₁) =
      algebraMap K K₁ (algebraMap (Localization.AtPrime la.asIdeal) K r) := by
  have key : (Tw w).subtype.comp (mapLaT la w hw) =
      (algebraMap K K₁).comp (algebraMap (Localization.AtPrime la.asIdeal) K) := by
    apply IsLocalization.ringHom_ext la.asIdeal.primeCompl
    ext x
    simp only [RingHom.comp_apply, mapLaT, IsLocalization.map_eq]
    rw [← IsScalarTower.algebraMap_apply (𝓞 K) (Localization.AtPrime la.asIdeal) K]
    first
      | rfl
      | simp
      | (norm_cast; simp)
      | exact (trivial : True)
  exact RingHom.congr_fun key r

/- English proof (translation)
Unfold `LiesOver at hw`. Establish `hlo : w.asIdeal.LiesOver la.asIdeal` using `⟨hw.symm⟩`. Rewrite using `[← Ideal.ramificationIdx_eq_ramificationIdx' la.asIdeal w.asIdeal la.ne_bot]`. Apply the tactic sequence `apply Ideal.IsDedekindDomain.ramificationIdx'_ne_zero <;> first`. Consider the case `exact la.ne_bot`.

Consider the case `exact w.ne_bot`. Consider the case `exact hlo`. Consider the case `exact w.isPrime`. Consider the case `infer_instance`. Consider the case `exact Ideal.map_le_iff_le_comap.mpr hw.ge`.

Consider the case `exact (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 K₁))).not.mpr la.ne_bot`. Consider the case `exact (Ideal.map_eq_bot_iff_of_injective (NoZeroSMulDivisors.algebraMap_injective (𝓞 K) (𝓞 K₁))).not.mpr la.ne_bot`. Consider the case `exact Ideal.map_ne_bot_of_ne_bot la.ne_bot`. Consider the case `exact (trivial : True)`.
-/
theorem ramificationIdx_ne_zero' (la : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K₁))
    (hw : LiesOver w la) : w.asIdeal.ramificationIdx (𝓞 K) ≠ 0 := by
  unfold LiesOver at hw
  have hlo : w.asIdeal.LiesOver la.asIdeal := ⟨hw.symm⟩
  rw [← Ideal.ramificationIdx_eq_ramificationIdx' la.asIdeal w.asIdeal la.ne_bot]
  apply Ideal.IsDedekindDomain.ramificationIdx'_ne_zero <;>
    first
          | exact la.ne_bot
          | exact w.ne_bot
          | exact hlo
          | exact w.isPrime
          | infer_instance
          | exact Ideal.map_le_iff_le_comap.mpr hw.ge
          | exact (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 K₁))).not.mpr la.ne_bot
          | exact (Ideal.map_eq_bot_iff_of_injective (NoZeroSMulDivisors.algebraMap_injective (𝓞 K) (𝓞 K₁))).not.mpr la.ne_bot
          | exact Ideal.map_ne_bot_of_ne_bot la.ne_bot
          | exact (trivial : True)

/- English proof (translation)
Establish `: w.asIdeal.LiesOver la.asIdeal` using `⟨hw.symm⟩`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime la.asIdeal)`. Take `⟨ϖ₁, hϖ₁⟩` from `IsDiscreteValuationRing.exists_irreducible (Tw w)`. Establish `hinj : Function.Injective (mapLaT la w hw)`. Introduce `x y hxy`.

Establish `h` using `congrArg (fun t : Tw w => (t : K₁)) hxy`. Simplify using `only [mapLaT_coe] at h`. Conclude with `IsFractionRing.injective (Localization.AtPrime la.asIdeal) K ((algebraMap K K₁).injective h)`. Establish `h0 : mapLaT la w hw ϖ ≠ 0` using `fun h => hϖ.ne_zero (hinj (h.trans (map_zero _).symm))`. Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ₁`.

Establish `hmap0 : la.asIdeal.map (algebraMap (𝓞 K) (𝓞 K₁)) ≠ ⊥` using `Ideal.map_ne_bot_of_ne_bot la.ne_bot`. Take `⟨Q, hQ, hfac⟩` from `Ideal.eq_prime_pow_mul_coprime hmap0 w.asIdeal`. Generalize the expression as in `hc : Multiset.count w.asIdeal (UniqueFactorizationMonoid.normalizedFactors (la.asIdeal.map (algebraMap (𝓞 K) (𝓞 K₁)))) = c at hfac`. Establish `hQw : ¬ Q ≤ w.asIdeal` using `fun hle => by`. Rewrite `hQ` using `[sup_eq_left.2 hle]`.

Conclude with `w.isPrime.ne_top hQ`. Establish `h1 : (la.asIdeal.map (algebraMap (𝓞 K) (𝓞 K₁))).map (algebraMap (𝓞 K₁) (Tw w)) = IsLocalRing.maximalIdeal (Tw w) ^ c`. Rewrite using `[hfac, Ideal.map_mul, Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal (p := w.asIdeal) (Rₚ := Tw w), IsLocalization.AtPrime.map_eq_top_of_not_le (S := Tw w) hQw, Ideal.mul_top]`. Establish `hcomp : (mapLaT la w hw).comp (algebraMap (𝓞 K) (Localization.AtPrime la.asIdeal)) = (algebraMap (𝓞 K₁) (Tw w)).comp (algebraMap (𝓞 K) (𝓞 K₁))` using `IsLocalization.map_comp _`. Establish `h2 : (la.asIdeal.map (algebraMap (𝓞 K) (𝓞 K₁))).map (algebraMap (𝓞 K₁) (Tw w)) = Ideal.span {mapLaT la w hw ϖ}`.

Rewrite using `[Ideal.map_map, ← hcomp, ← Ideal.map_map, IsLocalization.AtPrime.map_eq_maximalIdeal (p := la.asIdeal) (Rₚ := Localization.AtPrime la.asIdeal), hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]`. Establish `h3 : Ideal.span {mapLaT la w hw ϖ} = IsLocalRing.maximalIdeal (Tw w) ^ n`. Rewrite using `[hu, Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow, ← hϖ₁.maximalIdeal_eq]`. Establish `hn : n = c` using `pow_maximalIdeal_inj (h3.symm.trans (h2.symm.trans h1))`. Establish `he : n = w.asIdeal.ramificationIdx (𝓞 K)`.

Rewrite using `[hn, ← hc, ← Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmap0 w.isPrime w.ne_bot, Ideal.ramificationIdx'_eq_ramificationIdx la.asIdeal w.asIdeal la.ne_bot]`. Conclude with `⟨ϖ, ϖ₁, u, hϖ, hϖ₁, by rw [hu, he]⟩`.
-/
theorem exists_rel (la : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K₁))
    (hw : LiesOver w la) :
    ∃ (ϖ : Localization.AtPrime la.asIdeal) (ϖ₁ : Tw w) (u : (Tw w)ˣ), Irreducible ϖ ∧
      Irreducible ϖ₁ ∧ mapLaT la w hw ϖ = u * ϖ₁ ^ (w.asIdeal.ramificationIdx (𝓞 K)) := by
  have : w.asIdeal.LiesOver la.asIdeal := ⟨hw.symm⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime la.asIdeal)
  obtain ⟨ϖ₁, hϖ₁⟩ := IsDiscreteValuationRing.exists_irreducible (Tw w)
  have hinj : Function.Injective (mapLaT la w hw) := by
    intro x y hxy
    have h := congrArg (fun t : Tw w => (t : K₁)) hxy
    simp only [mapLaT_coe] at h
    exact IsFractionRing.injective (Localization.AtPrime la.asIdeal) K
      ((algebraMap K K₁).injective h)
  have h0 : mapLaT la w hw ϖ ≠ 0 := fun h => hϖ.ne_zero (hinj (h.trans (map_zero _).symm))
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ₁
  have hmap0 : la.asIdeal.map (algebraMap (𝓞 K) (𝓞 K₁)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot la.ne_bot
  obtain ⟨Q, hQ, hfac⟩ := Ideal.eq_prime_pow_mul_coprime hmap0 w.asIdeal
  generalize hc : Multiset.count w.asIdeal
    (UniqueFactorizationMonoid.normalizedFactors (la.asIdeal.map (algebraMap (𝓞 K) (𝓞 K₁)))) = c
    at hfac
  have hQw : ¬ Q ≤ w.asIdeal := fun hle => by
    rw [sup_eq_left.2 hle] at hQ
    exact w.isPrime.ne_top hQ
  have h1 : (la.asIdeal.map (algebraMap (𝓞 K) (𝓞 K₁))).map (algebraMap (𝓞 K₁) (Tw w)) =
      IsLocalRing.maximalIdeal (Tw w) ^ c := by
    rw [hfac, Ideal.map_mul, Ideal.map_pow,
      IsLocalization.AtPrime.map_eq_maximalIdeal (p := w.asIdeal) (Rₚ := Tw w),
      IsLocalization.AtPrime.map_eq_top_of_not_le (S := Tw w) hQw, Ideal.mul_top]
  have hcomp : (mapLaT la w hw).comp (algebraMap (𝓞 K) (Localization.AtPrime la.asIdeal)) =
      (algebraMap (𝓞 K₁) (Tw w)).comp (algebraMap (𝓞 K) (𝓞 K₁)) :=
    IsLocalization.map_comp _
  have h2 : (la.asIdeal.map (algebraMap (𝓞 K) (𝓞 K₁))).map (algebraMap (𝓞 K₁) (Tw w)) =
      Ideal.span {mapLaT la w hw ϖ} := by
    rw [Ideal.map_map, ← hcomp, ← Ideal.map_map,
      IsLocalization.AtPrime.map_eq_maximalIdeal (p := la.asIdeal)
        (Rₚ := Localization.AtPrime la.asIdeal),
      hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have h3 : Ideal.span {mapLaT la w hw ϖ} = IsLocalRing.maximalIdeal (Tw w) ^ n := by
    rw [hu, Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
      ← hϖ₁.maximalIdeal_eq]
  have hn : n = c := pow_maximalIdeal_inj (h3.symm.trans (h2.symm.trans h1))
  have he : n = w.asIdeal.ramificationIdx (𝓞 K) := by
    rw [hn, ← hc, ← Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmap0
      w.isPrime w.ne_bot, Ideal.ramificationIdx'_eq_ramificationIdx la.asIdeal w.asIdeal la.ne_bot]
  exact ⟨ϖ, ϖ₁, u, hϖ, hϖ₁, by rw [hu, he]⟩

/- English proof (translation)
Set `_ : Algebra (Localization.AtPrime la.asIdeal) (Tw w)` to `(mapLaT la w hw).toAlgebra`. Establish `hRT : ∀ r : Localization.AtPrime la.asIdeal, ((algebraMap (Localization.AtPrime la.asIdeal) (Tw w) r : Tw w) : K₁) = algebraMap K K₁ (algebraMap (Localization.AtPrime la.asIdeal) K r)` using `mapLaT_coe la w hw`. Set `_ : Module (Localization.AtPrime la.asIdeal) V` to `Module.compHom V (algebraMap (Localization.AtPrime la.asIdeal) K)`. Establish `: IsScalarTower (Localization.AtPrime la.asIdeal) K V` using `⟨fun o k v => by`. Express the relevant statement in the definitionally equal form `(o • k) • v = algebraMap _ K o • (k • v)`.

Rewrite using `[Algebra.smul_def, mul_smul]⟩`. Establish `: IsScalarTower (𝓞 K) (Localization.AtPrime la.asIdeal) V` using `⟨fun a o v => by`. Express the relevant statement in the definitionally equal form `algebraMap _ K (a • o) • v = a • (algebraMap _ K o • v)`. Rewrite using `[Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, mul_smul, algebraMap_smul]⟩`. Set `θ' : Fin ρ → V` to `fun j => (θ j : V)`.

Set `S : Set V` to `((M ⊓ W.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) ∪ Set.range θ'`. Establish `hSM : S ⊆ (M : Set V)`. Introduce and unpack `x (hx | ⟨j, rfl⟩)`. Conclude with `hx.1`. Conclude with `(θ j).2`.

Set `G : Submodule (𝓞 K) V` to `Submodule.span (𝓞 K) S`. Establish `hGM : G ≤ M` using `Submodule.span_le.2 hSM`. Set `X : Submodule (Localization.AtPrime la.asIdeal) V` to `Submodule.span (Localization.AtPrime la.asIdeal) (M : Set V)`. Set `Y : Submodule (Localization.AtPrime la.asIdeal) V` to `Submodule.span (Localization.AtPrime la.asIdeal) S`. Establish `hYG : Y = Submodule.span (Localization.AtPrime la.asIdeal) (G : Set V)` using `by show _ = Submodule.span _ (Submodule.span (𝓞 K) S : Set V)`.

Rewrite using `[Submodule.span_span_of_tower]`. Set `S₁ : Submodule (𝓞 K) M` to `(W.restrictScalars (𝓞 K)).comap M.subtype`. Establish `hS₂ : G.comap M.subtype = S₁ ⊔ Submodule.span (𝓞 K) (Set.range θ)`. Apply `Submodule.map_injective_of_injective M.injective_subtype` to reduce the goal to its premises. Rewrite using `[Submodule.map_comap_subtype, inf_eq_right.2 hGM, Submodule.map_sup, Submodule.map_comap_subtype, Submodule.map_span, ← Set.range_comp]`.

Use `show Submodule.span (𝓞 K) S = _`. Rewrite using `[Submodule.span_union, Submodule.span_eq]`. Both sides reduce to the same expression. Establish `hmapQ : (G.comap M.subtype).map S₁.mkQ = Submodule.span (𝓞 K) (Set.range fun j => (Submodule.Quotient.mk (θ j) : QuotMW M W))`. Rewrite using `[hS₂, Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, Submodule.map_span, ← Set.range_comp]`.

Both sides reduce to the same expression. Establish `hle : S₁ ≤ G.comap M.subtype` using `by rw [hS₂]; exact le_sup_left`. Set `e1 : (QuotMW M W ⧸ Submodule.span (𝓞 K) (Set.range fun j => (Submodule.Quotient.mk (θ j) : QuotMW M W))) ≃ₗ[𝓞 K] M ⧸ G.comap M.subtype` to `(Submodule.quotEquivOfEq _ _ hmapQ.symm).trans (Submodule.quotientQuotientEquivQuotient S₁ (G.comap M.subtype) hle)`. Establish `hA : lenLa la (QuotMW M W ⧸ Submodule.span (𝓞 K) (Set.range fun j => (Submodule.Quotient.mk (θ j) : QuotMW M W))) = Module.length (Localization.AtPrime la.asIdeal) (X ⧸ Y.comap X.subtype)`. Rewrite using `[hYG]`.

Conclude with `TieLDB.length_localized_eq la.asIdeal M G e1`. Establish `hXfg : X.FG`. Take `⟨s, hs⟩` from `hMfg`. Use `⟨s, ?_⟩` and prove the remaining obligations. Use `show Submodule.span _ (s : Set V) = Submodule.span _ (M : Set V)`.

Rewrite using `[← hs, Submodule.span_span_of_tower]`. Establish `hYX : Y ≤ X` using `Submodule.span_mono hSM`. Establish `hMw : Submodule.span (Tw w) (TieLDA.tm K K₁ '' (M : Set V)) = Submodule.span (Tw w) (TieLDA.tm K K₁ '' (X : Set V))` using `(TieLDA.span_tm_span (Tw w) hRT (M : Set V)).symm`. Establish `hNw : (Submodule.span (Tw w) (Submodule.span K₁ (TieLDA.tm K K₁ '' (W : Set V)) : Set (K₁ ⊗[K] V)) ⊓ Submodule.span (Tw w) (TieLDA.tm K K₁ '' (X : Set V))) ⊔ Submodule.span (Tw w) (Set.range fun j => TieLDA.tm K K₁ (θ' j)) = Submodule.span (Tw w) (TieLDA.tm K K₁ '' (Y : Set V))`. Rewrite using `[TieLDA.span_inf_eq (Tw w) hRT X hXfg W]`.

Establish `h1 : X ⊓ W.restrictScalars (Localization.AtPrime la.asIdeal) = Submodule.span (Localization.AtPrime la.asIdeal) ((M ⊓ W.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V)` using `(TieLDB.span_inf_eq la.asIdeal M (W.restrictScalars (Localization.AtPrime la.asIdeal))).symm`. Rewrite using `[h1, TieLDA.span_tm_span (Tw w) hRT]`. Use `show _ = Submodule.span (Tw w) (TieLDA.tm K K₁ '' (Submodule.span (Localization.AtPrime la.asIdeal) S : Set V))`. Rewrite using `[TieLDA.span_tm_span (Tw w) hRT, Set.image_union, Submodule.span_union, ← Set.range_comp]`. Both sides reduce to the same expression.

Establish `hW : lenW w M W θ = Module.length (Tw w) (↥(Submodule.span (Tw w) (TieLDA.tm K K₁ '' (M : Set V))) ⧸ ((Submodule.span (Tw w) (Submodule.span K₁ (TieLDA.tm K K₁ '' (W : Set V)) : Set (K₁ ⊗[K] V)) ⊓ Submodule.span (Tw w) (TieLDA.tm K K₁ '' (M : Set V))) ⊔ Submodule.span (Tw w) (Set …` using `rfl`. Rewrite using `[hW, hMw, hNw, TieLDA.length_quot_eq (Tw w) hRT X Y hXfg hYX, hA]`. Establish `hfinX : Module.Finite (Localization.AtPrime la.asIdeal) X` using `Module.Finite.iff_fg.2 hXfg`. Distinguish the cases in `hN : Module.length (Localization.AtPrime la.asIdeal) (X ⧸ Y.comap X.subtype) = ⊤`. Establish `he : ((w.asIdeal.ramificationIdx (𝓞 K) : ℕ) : ℕ∞) ≠ 0`.

Conclude with `ramificationIdx_ne_zero' la w hw` after adjusting the coercions. Rewrite using `[TieLDA.length_tensor_eq_top (T := Tw w) _ hN, hN, ENat.mul_top he]`. Take `⟨ϖ, ϖ₁, u, hϖ, hϖ₁, hrel⟩` from `exists_rel la w hw`. Conclude with `hL (Localization.AtPrime la.asIdeal) (Tw w) (X ⧸ Y.comap X.subtype) ϖ ϖ₁ u _ hϖ hϖ₁ hrel hN`.
-/
theorem main_eq (hL : Formalism.LatticeBaseChangeAlt.LengthBaseChangeLocal)
    {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (M : Submodule (𝓞 K) V) (hMfg : M.FG) (W : Submodule K V) {ρ : ℕ} (θ : Fin ρ → M)
    (la : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K₁)) (hw : LiesOver w la) :
    lenW w M W θ = (w.asIdeal.ramificationIdx (𝓞 K) : ℕ∞) *
      lenLa la (QuotMW M W ⧸ Submodule.span (𝓞 K)
        (Set.range fun j => (Submodule.Quotient.mk (θ j) : QuotMW M W))) := by
  let _ : Algebra (Localization.AtPrime la.asIdeal) (Tw w) := (mapLaT la w hw).toAlgebra
  have hRT : ∀ r : Localization.AtPrime la.asIdeal,
      ((algebraMap (Localization.AtPrime la.asIdeal) (Tw w) r : Tw w) : K₁) =
        algebraMap K K₁ (algebraMap (Localization.AtPrime la.asIdeal) K r) := mapLaT_coe la w hw
  let _ : Module (Localization.AtPrime la.asIdeal) V :=
    Module.compHom V (algebraMap (Localization.AtPrime la.asIdeal) K)
  have : IsScalarTower (Localization.AtPrime la.asIdeal) K V := ⟨fun o k v => by
    change (o • k) • v = algebraMap _ K o • (k • v)
    rw [Algebra.smul_def, mul_smul]⟩
  have : IsScalarTower (𝓞 K) (Localization.AtPrime la.asIdeal) V := ⟨fun a o v => by
    change algebraMap _ K (a • o) • v = a • (algebraMap _ K o • v)
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, mul_smul, algebraMap_smul]⟩

  let θ' : Fin ρ → V := fun j => (θ j : V)
  let S : Set V := ((M ⊓ W.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) ∪ Set.range θ'
  have hSM : S ⊆ (M : Set V) := by
    rintro x (hx | ⟨j, rfl⟩)
    · exact hx.1
    · exact (θ j).2
  let G : Submodule (𝓞 K) V := Submodule.span (𝓞 K) S
  have hGM : G ≤ M := Submodule.span_le.2 hSM
  let X : Submodule (Localization.AtPrime la.asIdeal) V :=
    Submodule.span (Localization.AtPrime la.asIdeal) (M : Set V)
  let Y : Submodule (Localization.AtPrime la.asIdeal) V :=
    Submodule.span (Localization.AtPrime la.asIdeal) S
  have hYG : Y = Submodule.span (Localization.AtPrime la.asIdeal) (G : Set V) := by
    show _ = Submodule.span _ (Submodule.span (𝓞 K) S : Set V)
    rw [Submodule.span_span_of_tower]

  let S₁ : Submodule (𝓞 K) M := (W.restrictScalars (𝓞 K)).comap M.subtype
  have hS₂ : G.comap M.subtype = S₁ ⊔ Submodule.span (𝓞 K) (Set.range θ) := by
    apply Submodule.map_injective_of_injective M.injective_subtype
    rw [Submodule.map_comap_subtype, inf_eq_right.2 hGM, Submodule.map_sup,
      Submodule.map_comap_subtype, Submodule.map_span, ← Set.range_comp]
    show Submodule.span (𝓞 K) S = _
    rw [Submodule.span_union, Submodule.span_eq]
    rfl
  have hmapQ : (G.comap M.subtype).map S₁.mkQ =
      Submodule.span (𝓞 K) (Set.range fun j => (Submodule.Quotient.mk (θ j) : QuotMW M W)) := by
    rw [hS₂, Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, Submodule.map_span,
      ← Set.range_comp]
    rfl
  have hle : S₁ ≤ G.comap M.subtype := by rw [hS₂]; exact le_sup_left
  let e1 : (QuotMW M W ⧸ Submodule.span (𝓞 K)
      (Set.range fun j => (Submodule.Quotient.mk (θ j) : QuotMW M W))) ≃ₗ[𝓞 K]
      M ⧸ G.comap M.subtype :=
    (Submodule.quotEquivOfEq _ _ hmapQ.symm).trans
      (Submodule.quotientQuotientEquivQuotient S₁ (G.comap M.subtype) hle)
  have hA : lenLa la (QuotMW M W ⧸ Submodule.span (𝓞 K)
      (Set.range fun j => (Submodule.Quotient.mk (θ j) : QuotMW M W))) =
      Module.length (Localization.AtPrime la.asIdeal) (X ⧸ Y.comap X.subtype) := by
    rw [hYG]
    exact TieLDB.length_localized_eq la.asIdeal M G e1

  have hXfg : X.FG := by
    obtain ⟨s, hs⟩ := hMfg
    refine ⟨s, ?_⟩
    show Submodule.span _ (s : Set V) = Submodule.span _ (M : Set V)
    rw [← hs, Submodule.span_span_of_tower]
  have hYX : Y ≤ X := Submodule.span_mono hSM
  have hMw : Submodule.span (Tw w) (TieLDA.tm K K₁ '' (M : Set V)) =
      Submodule.span (Tw w) (TieLDA.tm K K₁ '' (X : Set V)) :=
    (TieLDA.span_tm_span (Tw w) hRT (M : Set V)).symm
  have hNw : (Submodule.span (Tw w)
        (Submodule.span K₁ (TieLDA.tm K K₁ '' (W : Set V)) : Set (K₁ ⊗[K] V)) ⊓
        Submodule.span (Tw w) (TieLDA.tm K K₁ '' (X : Set V))) ⊔
      Submodule.span (Tw w) (Set.range fun j => TieLDA.tm K K₁ (θ' j)) =
      Submodule.span (Tw w) (TieLDA.tm K K₁ '' (Y : Set V)) := by
    rw [TieLDA.span_inf_eq (Tw w) hRT X hXfg W]
    have h1 : X ⊓ W.restrictScalars (Localization.AtPrime la.asIdeal) =
        Submodule.span (Localization.AtPrime la.asIdeal)
          ((M ⊓ W.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) :=
      (TieLDB.span_inf_eq la.asIdeal M (W.restrictScalars (Localization.AtPrime la.asIdeal))).symm
    rw [h1, TieLDA.span_tm_span (Tw w) hRT]
    show _ = Submodule.span (Tw w) (TieLDA.tm K K₁ ''
      (Submodule.span (Localization.AtPrime la.asIdeal) S : Set V))
    rw [TieLDA.span_tm_span (Tw w) hRT, Set.image_union, Submodule.span_union, ← Set.range_comp]
    rfl
  have hW : lenW w M W θ = Module.length (Tw w)
      (↥(Submodule.span (Tw w) (TieLDA.tm K K₁ '' (M : Set V))) ⧸
        ((Submodule.span (Tw w)
          (Submodule.span K₁ (TieLDA.tm K K₁ '' (W : Set V)) : Set (K₁ ⊗[K] V)) ⊓
          Submodule.span (Tw w) (TieLDA.tm K K₁ '' (M : Set V))) ⊔
          Submodule.span (Tw w) (Set.range fun j => TieLDA.tm K K₁ (θ' j))).comap
          (Submodule.span (Tw w) (TieLDA.tm K K₁ '' (M : Set V))).subtype) := rfl
  rw [hW, hMw, hNw, TieLDA.length_quot_eq (Tw w) hRT X Y hXfg hYX, hA]

  have hfinX : Module.Finite (Localization.AtPrime la.asIdeal) X := Module.Finite.iff_fg.2 hXfg
  by_cases hN : Module.length (Localization.AtPrime la.asIdeal) (X ⧸ Y.comap X.subtype) = ⊤
  · have he : ((w.asIdeal.ramificationIdx (𝓞 K) : ℕ) : ℕ∞) ≠ 0 := by
      exact_mod_cast ramificationIdx_ne_zero' la w hw
    rw [TieLDA.length_tensor_eq_top (T := Tw w) _ hN, hN, ENat.mul_top he]
  · obtain ⟨ϖ, ϖ₁, u, hϖ, hϖ₁, hrel⟩ := exists_rel la w hw
    exact hL (Localization.AtPrime la.asIdeal) (Tw w) (X ⧸ Y.comap X.subtype) ϖ ϖ₁ u _ hϖ hϖ₁
      hrel hN

end TieLD

open TieLD in
/- English proof (translation)
Unfold `ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LenDescentStatement`. Introduce `K K₁ V _ _ _ _ _ _ _ _ _ _ M hMfg _ W ρ θ la w hw`. Conclude with `TieLD.main_eq h M hMfg W θ la w hw`.
-/
theorem lenDescent_of_lengthBaseChangeLocal (h : Formalism.LatticeBaseChangeAlt.LengthBaseChangeLocal) :
    ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LenDescentStatement := by
  unfold ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LenDescentStatement
  intro K K₁ V _ _ _ _ _ _ _ _ _ _ M hMfg _ W ρ θ la w hw
  exact TieLD.main_eq h M hMfg W θ la w hw

/- English proof (translation)
The claim follows from `lenDescent_of_lengthBaseChangeLocal Formalism.LatticeBaseChangeAlt.lengthBaseChangeLocal`.
-/
theorem lenDescent_holds : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LenDescentStatement :=
  lenDescent_of_lengthBaseChangeLocal Formalism.LatticeBaseChangeAlt.lengthBaseChangeLocal

end Formalism.L2.Pj.QAt
