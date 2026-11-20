import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemRiemannRochSpaceIffRegularAtEverywhere
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IndefiniteRowSideFullHecke.FrameCoefficientData GlobalTheory.NonGenericCompare
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.LocFieldOfDVR

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology
open scoped WithZero

/- English proof (translation)
Take `⟨a', rfl⟩` from `WithZero.ne_zero_iff_exists.mp ha`. Take `⟨c', rfl⟩` from `WithZero.ne_zero_iff_exists.mp hc`. Use `⟨(Multiplicative.toAdd c').natAbs + 1, ?_⟩` and prove the remaining obligations. Rewrite using `[← WithZero.coe_pow, WithZero.coe_lt_coe]`. Rewrite `ha1` using `[← WithZero.coe_one, WithZero.coe_lt_coe]`.

Rewrite using `[← Multiplicative.toAdd_lt, toAdd_pow, nsmul_eq_mul]`. Rewrite `ha1` using `[← Multiplicative.toAdd_lt, toAdd_one]`. Use `push_cast`. Establish `ha2 : Multiplicative.toAdd a' ≤ -1` using `by omega`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left ha2 (by positivity : (0 : ℤ) ≤ |Multiplicative.toAdd c'| + 1), neg_abs_le (Multiplicative.toAdd c')]`.
-/
theorem exists_pow_lt_of_lt_one (a c : ℤᵐ⁰) (ha : a ≠ 0) (ha1 : a < 1) (hc : c ≠ 0) :
    ∃ n : ℕ, a ^ n < c := by
  obtain ⟨a', rfl⟩ := WithZero.ne_zero_iff_exists.mp ha
  obtain ⟨c', rfl⟩ := WithZero.ne_zero_iff_exists.mp hc
  refine ⟨(Multiplicative.toAdd c').natAbs + 1, ?_⟩
  rw [← WithZero.coe_pow, WithZero.coe_lt_coe]
  rw [← WithZero.coe_one, WithZero.coe_lt_coe] at ha1
  rw [← Multiplicative.toAdd_lt, toAdd_pow, nsmul_eq_mul]
  rw [← Multiplicative.toAdd_lt, toAdd_one] at ha1
  push_cast
  have ha2 : Multiplicative.toAdd a' ≤ -1 := by omega
  nlinarith [mul_le_mul_of_nonneg_left ha2 (by positivity : (0 : ℤ) ≤ |Multiplicative.toAdd c'| + 1),
    neg_abs_le (Multiplicative.toAdd c')]

variable (o F : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [Field F] [Algebra o F]
  [IsFractionRing o F]

abbrev val : Valuation F ℤᵐ⁰ := (IsDiscreteValuationRing.maximalIdeal o).valuation F

abbrev valued : Valued F ℤᵐ⁰ := Valued.mk' (val o F)

def equivInt : o ≃+* (val o F).integer :=
  RingEquiv.ofBijective
    ((algebraMap o F).codRestrict (val o F).integer (fun a => valuation_le_one _ a))
    ⟨fun a b h => IsFractionRing.injective o F (congrArg Subtype.val h),
     fun x => by
      obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one x.2
      exact ⟨a, Subtype.ext ha⟩⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem equivInt_val (a : o) : ((equivInt o F a : (val o F).integer) : F) = algebraMap o F a := rfl

variable {o F}

/- English proof (translation)
Rewrite using `[← Ideal.map_pow, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton, (Valuation.integer.integers _).dvd_iff_le]`. Simplify using `only [map_pow, equivInt_val]`. Conclude with `Iff.rfl`.
-/
theorem mem_pow_iff {ϖ : o} (hϖ : Irreducible ϖ) (n : ℕ) (x : (val o F).integer) :
    x ∈ ((IsLocalRing.maximalIdeal o).map (equivInt o F)) ^ n ↔
      val o F (x : F) ≤ val o F (algebraMap o F ϖ) ^ n := by
  rw [← Ideal.map_pow, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.map_span,
    Set.image_singleton, Ideal.mem_span_singleton, (Valuation.integer.integers _).dvd_iff_le]
  simp only [map_pow, equivInt_val]
  exact Iff.rfl

end GlobalTheory.LocFieldOfDVR

namespace GlobalTheory.LocFieldOfDVR
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology
open scoped WithZero
variable {o F : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [Field F] [Algebra o F]
  [IsFractionRing o F]

/- English proof (translation)
Use `letI := valued o F`. Use `set J := (IsLocalRing.maximalIdeal o).map (equivInt o F)`. Use `set π := algebraMap o F ϖ`. Establish `hπ0 : val o F π ≠ 0`. Simplify using `only [π, ne_eq, map_eq_zero]`.

Conclude with `(IsFractionRing.injective o F).ne_iff' (map_zero _) |>.mpr hϖ.ne_zero`. Establish `hπ1 : val o F π < 1` using `(valuation_lt_one_iff_mem _ ϖ).mpr (by simpa [IsDiscreteValuationRing.maximalIdeal] using hϖ.not_isUnit)`. Rewrite using `[isAdic_iff]`. Use `⟨fun n => ?_, fun s hs => ?_⟩` and prove the remaining obligations. Use `AddSubgroup.isOpen_of_mem_nhds (J ^ n).toAddSubgroup (g := 0) ?_` and prove the remaining obligations.

Rewrite using `[mem_nhds_subtype]`. Use `⟨{y | val o F y < val o F π ^ n}, ?_, fun y hy => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ ∈ 𝓝 (0 : F)`. Rewrite using `[Valued.mem_nhds_zero]`. Establish `hπne : π ≠ 0` using `by rintro h; simp [h] at hπ0`.

Use `⟨Units.mk0 ((val o F).restrict (π ^ n)) (by simp [hπne]), fun y hy => ?_⟩` and prove the remaining obligations. Simplify using `only [Units.val_mk0, Set.mem_setOf_eq] at hy ⊢`. Establish `hy' : (val o F).restrict y < (val o F).restrict (π ^ n)` using `hy`. Rewrite `hy'` using `[Valuation.restrict_lt_iff]`. Simplify `hy'` using `[map_pow]`.

Conclude with `(mem_pow_iff hϖ n y).mpr (le_of_lt hy)`. Take `⟨u, hu, hus⟩` from `(mem_nhds_subtype _ _ _).mp hs`. Take `⟨γ, hγ⟩` from `Valued.mem_nhds_zero.mp hu`. Establish `hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0` using `by simp`. Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one _ _ hπ0 hπ1 hγ0`.

Use `⟨n, fun y hy => hus (hγ ?_)⟩` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]`. Conclude with `((mem_pow_iff hϖ n y).mp hy).trans_lt hn`.
-/
theorem isAdic_map {ϖ : o} (hϖ : Irreducible ϖ) :
    letI := valued o F
    IsAdic ((IsLocalRing.maximalIdeal o).map (equivInt o F)) := by
  letI := valued o F
  set J := (IsLocalRing.maximalIdeal o).map (equivInt o F)
  set π := algebraMap o F ϖ
  have hπ0 : val o F π ≠ 0 := by
    simp only [π, ne_eq, map_eq_zero]
    exact (IsFractionRing.injective o F).ne_iff' (map_zero _) |>.mpr hϖ.ne_zero
  have hπ1 : val o F π < 1 := (valuation_lt_one_iff_mem _ ϖ).mpr
    (by simpa [IsDiscreteValuationRing.maximalIdeal] using hϖ.not_isUnit)
  rw [isAdic_iff]
  refine ⟨fun n => ?_, fun s hs => ?_⟩
  · refine AddSubgroup.isOpen_of_mem_nhds (J ^ n).toAddSubgroup (g := 0) ?_
    rw [mem_nhds_subtype]
    refine ⟨{y | val o F y < val o F π ^ n}, ?_, fun y hy => ?_⟩
    · change _ ∈ 𝓝 (0 : F)
      rw [Valued.mem_nhds_zero]
      have hπne : π ≠ 0 := by rintro h; simp [h] at hπ0
      refine ⟨Units.mk0 ((val o F).restrict (π ^ n)) (by simp [hπne]), fun y hy => ?_⟩
      simp only [Units.val_mk0, Set.mem_setOf_eq] at hy ⊢
      have hy' : (val o F).restrict y < (val o F).restrict (π ^ n) := hy
      rw [Valuation.restrict_lt_iff] at hy'
      simpa [map_pow] using hy'
    · exact (mem_pow_iff hϖ n y).mpr (le_of_lt hy)
  · obtain ⟨u, hu, hus⟩ := (mem_nhds_subtype _ _ _).mp hs
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hu
    have hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one _ _ hπ0 hπ1 hγ0
    refine ⟨n, fun y hy => hus (hγ ?_)⟩
    simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
    exact ((mem_pow_iff hϖ n y).mp hy).trans_lt hn

end GlobalTheory.LocFieldOfDVR

namespace GlobalTheory.LocFieldOfDVR
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology
open scoped WithZero
variable {o F : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [Field F] [Algebra o F]
  [IsFractionRing o F]

/- English proof (translation)
Use `letI := valued o F`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible o`. Use `letI : (Valued.v : Valuation F ℤᵐ⁰).RankOne := Valuation.IsRankOneDiscrete.rankOne (val o F) (e := 2) one_lt_two`. Establish `hI` using `isAdic_map (F := F) hϖ`. Establish `hpre : IsPrecomplete ((IsLocalRing.maximalIdeal o).map (equivInt o F)) (val o F).integer` using `(IsPrecomplete.congr_ringEquiv _ _).mpr inferInstance`.

Use `haveI : IsUniformAddGroup (val o F).integer := inferInstanceAs (IsUniformAddGroup (val o F).integer.toAddSubgroup)`. Establish `hcomp : CompleteSpace (val o F).integer` using `(IsAdic.isPrecomplete_iff hI).mp hpre`. Establish `hdvr : IsDiscreteValuationRing (Valued.integer F)` using `inferInstanceAs (IsDiscreteValuationRing (val o F).integer)`. Establish `hfin : Finite (IsLocalRing.ResidueField (Valued.integer F))` using `Finite.of_equiv _ (IsLocalRing.ResidueField.mapEquiv (equivInt o F)).toEquiv`. Conclude with `Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr ⟨hcomp, hdvr, hfin⟩`.
-/
theorem compactSpace_integer [IsAdicComplete (IsLocalRing.maximalIdeal o) o]
    [Finite (IsLocalRing.ResidueField o)] :
    letI := valued o F
    CompactSpace (Valued.integer F) := by
  letI := valued o F
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible o
  letI : (Valued.v : Valuation F ℤᵐ⁰).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne (val o F) (e := 2) one_lt_two
  have hI := isAdic_map (F := F) hϖ
  have hpre : IsPrecomplete ((IsLocalRing.maximalIdeal o).map (equivInt o F)) (val o F).integer :=
    (IsPrecomplete.congr_ringEquiv _ _).mpr inferInstance
  haveI : IsUniformAddGroup (val o F).integer :=
    inferInstanceAs (IsUniformAddGroup (val o F).integer.toAddSubgroup)
  have hcomp : CompleteSpace (val o F).integer := (IsAdic.isPrecomplete_iff hI).mp hpre
  have hdvr : IsDiscreteValuationRing (Valued.integer F) :=
    inferInstanceAs (IsDiscreteValuationRing (val o F).integer)
  have hfin : Finite (IsLocalRing.ResidueField (Valued.integer F)) :=
    Finite.of_equiv _ (IsLocalRing.ResidueField.mapEquiv (equivInt o F)).toEquiv
  exact Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr
    ⟨hcomp, hdvr, hfin⟩

/- English proof (translation)
Use `letI := valued o F`. Use `compactSpace_integer (o := o) (F := F)` as an intermediate fact. Conclude with `IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup (isCompact_iff_compactSpace.mpr this) ((Valued.isOpen_integer F).mem_nhds (zero_mem _))`.
-/
theorem locallyCompactSpace [IsAdicComplete (IsLocalRing.maximalIdeal o) o]
    [Finite (IsLocalRing.ResidueField o)] :
    letI := valued o F
    LocallyCompactSpace F := by
  letI := valued o F
  have := compactSpace_integer (o := o) (F := F)
  exact IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup
    (isCompact_iff_compactSpace.mpr this) ((Valued.isOpen_integer F).mem_nhds (zero_mem _))

end GlobalTheory.LocFieldOfDVR

namespace GlobalTheory.LocFieldOfDVR
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology
open scoped WithZero

/- English proof (translation)
Introduce `o F _ _ _ _ _ _ _ _`. Use `letI := valued o F`. Use `letI vr : ValuativeRel F := .ofValuation (val o F)`. Use `haveI : (val o F).Compatible := .ofValuation _`. Use `⟨vr, inferInstance, ?_, fun x => ?_⟩` and prove the remaining obligations.

Establish `h1 : IsValuativeTopology F` using `IsValuativeTopology.of_mem_nhds_iff_vle (val o F) (fun {s x} => Valued.mem_nhds)`. Establish `h2 : ValuativeRel.IsNontrivial F` using `(ValuativeRel.isNontrivial_iff_isNontrivial (val o F)).mpr inferInstance`. Establish `h3 : LocallyCompactSpace F` using `locallyCompactSpace (o := o) (F := F)`. Conclude with `{}`. Rewrite using `[Valuation.mem_integer_iff, ← (ValuativeRel.valuation F).vle_one_iff, (val o F).vle_one_iff]`.

Conclude with `⟨IsDiscreteValuationRing.exists_lift_of_le_one, fun ⟨a, ha⟩ => ha ▸ valuation_le_one _ a⟩`.
-/
theorem exists_isNonarchimedeanLocalField : ∀ (o F : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [IsAdicComplete (IsLocalRing.maximalIdeal o) o] [Finite (IsLocalRing.ResidueField o)] [Field F] [Algebra o F] [IsFractionRing o F], ∃ (_ : ValuativeRel F) (_ : TopologicalSpace F), IsNonarchimedeanLocalField F ∧ ∀ x : F, x ∈ 𝒪[F] ↔ ∃ a : o, algebraMap o F a = x := by
  intro o F _ _ _ _ _ _ _ _
  letI := valued o F
  letI vr : ValuativeRel F := .ofValuation (val o F)
  haveI : (val o F).Compatible := .ofValuation _
  refine ⟨vr, inferInstance, ?_, fun x => ?_⟩
  · have h1 : IsValuativeTopology F :=
      IsValuativeTopology.of_mem_nhds_iff_vle (val o F) (fun {s x} => Valued.mem_nhds)
    have h2 : ValuativeRel.IsNontrivial F :=
      (ValuativeRel.isNontrivial_iff_isNontrivial (val o F)).mpr inferInstance
    have h3 : LocallyCompactSpace F := locallyCompactSpace (o := o) (F := F)
    exact {}
  · rw [Valuation.mem_integer_iff, ← (ValuativeRel.valuation F).vle_one_iff, (val o F).vle_one_iff]
    exact ⟨IsDiscreteValuationRing.exists_lift_of_le_one,
      fun ⟨a, ha⟩ => ha ▸ valuation_le_one _ a⟩

end GlobalTheory.LocFieldOfDVR
