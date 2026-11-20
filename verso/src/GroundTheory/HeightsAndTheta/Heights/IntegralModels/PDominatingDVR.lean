import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

/- English proof (translation)
Rewrite using `[IsFractionRing, isLocalization_iff]`. Use `⟨fun y => ?_, fun z => ?_, fun {u v} h => ⟨1, ?_⟩⟩` and prove the remaining obligations. Establish `hy : (y : B) ≠ 0` using `nonZeroDivisors.coe_ne_zero y`. Conclude with `isUnit_iff_ne_zero.2 fun h => hy (Subtype.ext h)`. Take `⟨⟨a, s⟩, h⟩` from `IsLocalization.surj (nonZeroDivisors A) z`.

Establish `hs : algebraMap A B s ≠ 0` using `fun h0 => IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2 (congrArg Subtype.val h0)`. Conclude with `⟨⟨algebraMap A B a, ⟨_, mem_nonZeroDivisors_of_ne_zero hs⟩⟩, h⟩`. Simplify using `using Subtype.ext h`.
-/
theorem isFractionRing_of_subalgebra {A K : Type*} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] (B : Subalgebra A K) : IsFractionRing B K := by
  rw [IsFractionRing, isLocalization_iff]
  refine ⟨fun y => ?_, fun z => ?_, fun {u v} h => ⟨1, ?_⟩⟩
  · have hy : (y : B) ≠ 0 := nonZeroDivisors.coe_ne_zero y
    exact isUnit_iff_ne_zero.2 fun h => hy (Subtype.ext h)
  · obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (nonZeroDivisors A) z
    have hs : algebraMap A B s ≠ 0 := fun h0 =>
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2 (congrArg Subtype.val h0)
    exact ⟨⟨algebraMap A B a, ⟨_, mem_nonZeroDivisors_of_ne_zero hs⟩⟩, h⟩
  · simpa using Subtype.ext h

set_option maxHeartbeats 400000 in

/- English proof (translation)
Introduce `A _ _ _ _ hAf K _ _ _`. Take `⟨n, x, hx⟩` from `Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian (IsLocalRing.maximalIdeal A))`. Establish `hx' : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal A` using `hx`. Establish `hx0 : ∃ j, x j ≠ 0`. Assume the negation of the conclusion as `h`.

Use `push Not at h`. Apply `hAf` to reduce the goal to its premises. Rewrite using `[IsLocalRing.isField_iff_maximalIdeal_eq, ← hx']`. Conclude with `Submodule.span_eq_bot.mpr (by rintro _ ⟨j, rfl⟩; exact h j)`. Take `⟨i, hxi, hunit, -⟩` from `hBU A K n x hx' hx0`.

Use `set B := blowUpChart K x i`. Establish `: IsNoetherianRing B` using `isNoetherianRing_of_fg (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)`. Establish `: IsFractionRing B K` using `isFractionRing_of_subalgebra B`. Use `set xi : B := algebraMap A B (x i)`. Establish `hspan : Ideal.span {xi} ≠ ⊤` using `fun h => hunit (Ideal.span_singleton_eq_top.mp h)`.

Take `⟨q, hq⟩` from `Ideal.nonempty_minimalPrimes hspan`. Establish `: q.IsPrime` using `hq.1.1`. Establish `hxiq : xi ∈ q` using `hq.1.2 (Ideal.mem_span_singleton_self _)`. Establish `hxi0 : xi ≠ 0` using `fun h => hxi (IsFractionRing.injective A K (by`. Simplify `congrArg Subtype.val h))` using `[xi]`.

Establish `hq1 : q.height = 1` using `le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ q hq) ((Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hxi0)).trans (Ideal.height_mono hq.1.2))`. Establish `hmq : (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤ q`. Rewrite using `[← hx', Ideal.map_span, Ideal.span_le]`. Introduce and unpack `_ ⟨_, ⟨j, rfl⟩, rfl⟩`. Establish `e : algebraMap A B (x j) = ⟨algebraMap A K (x j) / algebraMap A K (x i), Algebra.subset_adjoin ⟨j, rfl⟩⟩ * xi`.

Apply `Subtype.ext` to reduce the goal to its premises. Establish `: algebraMap A K (x i) ≠ 0` using `fun h => hxi (IsFractionRing.injective A K (by simpa using h))`. Simplify using `[xi, div_mul_cancel₀ _ this]`. Conclude with `e ▸ q.mul_mem_left _ hxiq`. Use `set R := Localization.subalgebra.ofField K q.primeCompl q.primeCompl_le_nonZeroDivisors`.

Establish `: IsLocalization.AtPrime R q` using `(inferInstance : IsLocalization q.primeCompl R)`. Establish `: IsLocalRing R` using `IsLocalization.AtPrime.isLocalRing R q`. Establish `: IsNoetherianRing R` using `IsLocalization.isNoetherianRing q.primeCompl R inferInstance`. Establish `hdimR : ringKrullDim R = 1`. Rewrite using `[IsLocalization.AtPrime.ringKrullDim_eq_height q R, hq1]`.

Both sides reduce to the same expression. Use `set C := integralClosure R K`. Establish `: IsDedekindDomain C` using `hKA.2 R hdimR K`. Establish `: IsFractionRing C K` using `isFractionRing_of_subalgebra C`. Establish `hinj : Function.Injective (algebraMap R C)` using `fun a b h => by`.

Establish `h' : ((algebraMap R C a : C) : K) = ((algebraMap R C b : C) : K)` using `congrArg _ h`. Conclude with `IsFractionRing.injective R K h'`. Take `⟨P, hPmax, hPc⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := C) (IsLocalRing.maximalIdeal R) (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)`. Establish `: P.IsPrime` using `hPmax.isPrime`. Establish `hPbot : P ≠ ⊥`.

Introduce and unpack `rfl`. Establish `hF : IsField R`. Rewrite using `[IsLocalRing.isField_iff_maximalIdeal_eq, ← hPc, Ideal.comap_bot_of_injective _ hinj]`. Establish `h0` using `ringKrullDim_eq_zero_of_isField hF`. Rewrite `h0` using `[hdimR]`.

Conclude with `one_ne_zero h0`. Use `set V := Localization.subalgebra.ofField K P.primeCompl P.primeCompl_le_nonZeroDivisors`. Use `letI : CommRing V := Subalgebra.toCommRing (R := C) (A := K) V`. Establish `: IsDomain V` using `Subalgebra.isDomain (R := C) (A := K) V`. Establish `: IsLocalization.AtPrime V P` using `(inferInstance : IsLocalization P.primeCompl V)`.

Establish `hV : IsDiscreteValuationRing V` using `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hPbot V`. Set `φ : A →+* V` to `(algebraMap C V).comp ((algebraMap R C).comp ((algebraMap B R).comp (algebraMap A B)))`. Establish `hφ : ∀ a, (φ a : K) = algebraMap A K a` using `fun a => rfl`. Use `⟨Subalgebra.toSubring (R := C) V, hV, fun a => ?_, fun a => ?_⟩` and prove the remaining obligations. Use `show algebraMap A K a ∈ V`.

Conclude with `hφ a ▸ (φ a).2`. Use `show ¬ IsUnit (φ a) ↔ _`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Use `⟨fun h ha => h (ha.map φ), fun ha hu => ?_⟩` and prove the remaining obligations. Establish `hb : algebraMap A B a ∈ q` using `hmq (Ideal.mem_map_of_mem _ (by`.

Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]))` and apply the resulting hypothesis. Establish `hr : algebraMap B R (algebraMap A B a) ∈ IsLocalRing.maximalIdeal R` using `(IsLocalization.AtPrime.to_map_mem_maximal_iff R q _).mpr hb`. Rewrite `hr` using `[← hPc, Ideal.mem_comap]`. Conclude with `(IsLocalization.AtPrime.isUnit_to_map_iff V P _).mp hu hr`.
-/
theorem DominatingDVR.proof (hKA : KrullAkizuki.Statement) (hBU : BlowUpChart.Statement) :
    DominatingDVR.Statement := by
  intro A _ _ _ _ hAf K _ _ _

  obtain ⟨n, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (IsLocalRing.maximalIdeal A))
  have hx' : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal A := hx
  have hx0 : ∃ j, x j ≠ 0 := by
    by_contra h
    push Not at h
    apply hAf
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← hx']
    exact Submodule.span_eq_bot.mpr (by rintro _ ⟨j, rfl⟩; exact h j)
  obtain ⟨i, hxi, hunit, -⟩ := hBU A K n x hx' hx0

  set B := blowUpChart K x i
  have : IsNoetherianRing B :=
    isNoetherianRing_of_fg (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)
  have : IsFractionRing B K := isFractionRing_of_subalgebra B

  set xi : B := algebraMap A B (x i)
  have hspan : Ideal.span {xi} ≠ ⊤ := fun h => hunit (Ideal.span_singleton_eq_top.mp h)
  obtain ⟨q, hq⟩ := Ideal.nonempty_minimalPrimes hspan
  have : q.IsPrime := hq.1.1
  have hxiq : xi ∈ q := hq.1.2 (Ideal.mem_span_singleton_self _)
  have hxi0 : xi ≠ 0 := fun h => hxi (IsFractionRing.injective A K (by
    simpa [xi] using congrArg Subtype.val h))
  have hq1 : q.height = 1 := le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ q hq)
    ((Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hxi0)).trans (Ideal.height_mono hq.1.2))
  have hmq : (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤ q := by
    rw [← hx', Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    have e : algebraMap A B (x j) =
        ⟨algebraMap A K (x j) / algebraMap A K (x i), Algebra.subset_adjoin ⟨j, rfl⟩⟩ * xi := by
      apply Subtype.ext
      have : algebraMap A K (x i) ≠ 0 := fun h => hxi (IsFractionRing.injective A K (by simpa using h))
      simp [xi, div_mul_cancel₀ _ this]
    exact e ▸ q.mul_mem_left _ hxiq

  set R := Localization.subalgebra.ofField K q.primeCompl q.primeCompl_le_nonZeroDivisors
  have : IsLocalization.AtPrime R q := (inferInstance : IsLocalization q.primeCompl R)
  have : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R q
  have : IsNoetherianRing R := IsLocalization.isNoetherianRing q.primeCompl R inferInstance
  have hdimR : ringKrullDim R = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q R, hq1]
    rfl

  set C := integralClosure R K
  have : IsDedekindDomain C := hKA.2 R hdimR K
  have : IsFractionRing C K := isFractionRing_of_subalgebra C
  have hinj : Function.Injective (algebraMap R C) := fun a b h =>
    by
    have h' : ((algebraMap R C a : C) : K) = ((algebraMap R C b : C) : K) := congrArg _ h
    exact IsFractionRing.injective R K h'
  obtain ⟨P, hPmax, hPc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := C)
    (IsLocalRing.maximalIdeal R) (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  have : P.IsPrime := hPmax.isPrime
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    have hF : IsField R := by
      rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← hPc, Ideal.comap_bot_of_injective _ hinj]
    have h0 := ringKrullDim_eq_zero_of_isField hF
    rw [hdimR] at h0
    exact one_ne_zero h0

  set V := Localization.subalgebra.ofField K P.primeCompl P.primeCompl_le_nonZeroDivisors
  letI : CommRing V := Subalgebra.toCommRing (R := C) (A := K) V
  have : IsDomain V := Subalgebra.isDomain (R := C) (A := K) V
  have : IsLocalization.AtPrime V P := (inferInstance : IsLocalization P.primeCompl V)
  have hV : IsDiscreteValuationRing V :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hPbot V
  let φ : A →+* V :=
    (algebraMap C V).comp ((algebraMap R C).comp ((algebraMap B R).comp (algebraMap A B)))
  have hφ : ∀ a, (φ a : K) = algebraMap A K a := fun a => rfl
  refine ⟨Subalgebra.toSubring (R := C) V, hV, fun a => ?_, fun a => ?_⟩
  · show algebraMap A K a ∈ V
    exact hφ a ▸ (φ a).2
  show ¬ IsUnit (φ a) ↔ _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  refine ⟨fun h ha => h (ha.map φ), fun ha hu => ?_⟩
  have hb : algebraMap A B a ∈ q := hmq (Ideal.mem_map_of_mem _ (by
    rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]))
  have hr : algebraMap B R (algebraMap A B a) ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff R q _).mpr hb
  rw [← hPc, Ideal.mem_comap] at hr
  exact (IsLocalization.AtPrime.isUnit_to_map_iff V P _).mp hu hr

end GroundTheory.Heights₂.Heights.Model
