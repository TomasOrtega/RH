import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

noncomputable section

namespace UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Introduce `R _ l hl 𝔭 _`. Take `⟨q, hq, hq𝔭⟩` from `Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := 𝔭) bot_le`. Establish `hlq : l ∉ q` using `fun h => Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hq) h hl`. Use `haveI : q.IsPrime := hq.1.1`. Set `K` to `AlgebraicClosure (FractionRing (R ⧸ q))`.

Set `ι : R →+* K` to `(algebraMap (FractionRing (R ⧸ q)) K).comp ((algebraMap (R ⧸ q) (FractionRing (R ⧸ q))).comp (Ideal.Quotient.mk q))`. Establish `hι : ∀ r, ι r = 0 ↔ r ∈ q`. Introduce `r`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `h1 : algebraMap (R ⧸ q) (FractionRing (R ⧸ q)) (Ideal.Quotient.mk q r) = 0` using `(map_eq_zero (algebraMap (FractionRing (R ⧸ q)) K)).mp h`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp (IsFractionRing.to_map_eq_zero_iff.mp h1)`. Introduce `h`. Simplify using `[ι, Ideal.Quotient.eq_zero_iff_mem.mpr h]`. Establish `hunit : ∀ s : 𝔭.primeCompl, IsUnit (ι s)` using `fun s => isUnit_iff_ne_zero.mpr (fun h => s.2 (hq𝔭 ((hι s).mp h)))`.

Set `φ : Localization.AtPrime 𝔭 →+* K` to `IsLocalization.lift (M := 𝔭.primeCompl) hunit`. Establish `hφ : ∀ r, φ (algebraMap R _ r) = ι r` using `fun r => IsLocalization.lift_eq hunit r`. Take `⟨B, hsub, hloc⟩` from `(LocalSubring.range φ).exists_le_valuationSubring`. Establish `hmemL : ∀ x, φ x ∈ (LocalSubring.range φ).toSubring` using `fun x => by`. Rewrite using `[LocalSubring.range_toSubring]`.

Conclude with `⟨x, rfl⟩`. Set `ψ' : Localization.AtPrime 𝔭 →+* B` to `φ.codRestrict B (fun x => hsub (hmemL x))`. Set `ψ : R →+* B` to `ψ'.comp (algebraMap R (Localization.AtPrime 𝔭))`. Establish `hψ : ∀ r, (ψ r : K) = ι r` using `fun r => hφ r`. Use `haveI : IsAlgClosed (FractionRing B) := IsAlgClosed.of_ringEquiv K _ (FractionRing.algEquiv B K).symm.toRingEquiv`.

Use `⟨B, inferInstance, inferInstance, inferInstance, inferInstance, ψ.toAlgebra, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Express the relevant statement in the definitionally equal form `ψ l = 0 at h`. Apply `hlq` to reduce the goal to its premises. Rewrite using `[← hι, ← hψ, h, ZeroMemClass.coe_zero]`.

Use extensionality with `r`. Rewrite using `[Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Express the relevant statement in the definitionally equal form `¬ IsUnit (ψ r) ↔ r ∈ 𝔭`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Assume the negation of the conclusion as `hr`. Conclude with `h ((IsLocalization.map_units (Localization.AtPrime 𝔭) (⟨r, hr⟩ : 𝔭.primeCompl)).map ψ')`. Introduce `hr hu`. Establish `hxm : algebraMap R (Localization.AtPrime 𝔭) r ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭)` using `(IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔭) 𝔭 r).mpr hr`. Set `y : (LocalSubring.range φ).toSubring` to `⟨φ (algebraMap R (Localization.AtPrime 𝔭) r), hmemL _⟩`.

Establish `hy : IsUnit y` using `hloc.map_nonunit y hu`. Take `⟨z, hz⟩` from `isUnit_iff_exists_inv.mp hy`. Take `⟨w, hw⟩ : ∃ w, φ w = z` from `(LocalSubring.range_toSubring φ).le z.2`. Establish `h1 : φ (algebraMap R (Localization.AtPrime 𝔭) r) * (z : K) = 1` using `congrArg Subtype.val hz`. Establish `hker : algebraMap R (Localization.AtPrime 𝔭) r * w - 1 ∈ RingHom.ker φ`.

Rewrite using `[RingHom.mem_ker, map_sub, map_mul, map_one, hw, h1, sub_self]`. Establish `hkerle : RingHom.ker φ ≤ IsLocalRing.maximalIdeal _` using `IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top φ)`. Establish `h1m : (1 : Localization.AtPrime 𝔭) ∈ IsLocalRing.maximalIdeal _`. Establish `hs` using `Ideal.sub_mem _ (Ideal.mul_mem_right w _ hxm) (hkerle hker)`. Simplify using `using hs`.

Conclude with `(IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr h1m)`.
-/
theorem valLift_of : ValLift := by
  intro R _ l hl 𝔭 _
  classical
  obtain ⟨q, hq, hq𝔭⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := 𝔭) bot_le
  have hlq : l ∉ q := fun h =>
    Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hq) h hl
  haveI : q.IsPrime := hq.1.1
  let K := AlgebraicClosure (FractionRing (R ⧸ q))
  let ι : R →+* K := (algebraMap (FractionRing (R ⧸ q)) K).comp
    ((algebraMap (R ⧸ q) (FractionRing (R ⧸ q))).comp (Ideal.Quotient.mk q))
  have hι : ∀ r, ι r = 0 ↔ r ∈ q := by
    intro r
    constructor
    · intro h
      have h1 : algebraMap (R ⧸ q) (FractionRing (R ⧸ q)) (Ideal.Quotient.mk q r) = 0 :=
        (map_eq_zero (algebraMap (FractionRing (R ⧸ q)) K)).mp h
      exact Ideal.Quotient.eq_zero_iff_mem.mp (IsFractionRing.to_map_eq_zero_iff.mp h1)
    · intro h
      simp [ι, Ideal.Quotient.eq_zero_iff_mem.mpr h]
  have hunit : ∀ s : 𝔭.primeCompl, IsUnit (ι s) := fun s =>
    isUnit_iff_ne_zero.mpr (fun h => s.2 (hq𝔭 ((hι s).mp h)))
  let φ : Localization.AtPrime 𝔭 →+* K := IsLocalization.lift (M := 𝔭.primeCompl) hunit
  have hφ : ∀ r, φ (algebraMap R _ r) = ι r := fun r => IsLocalization.lift_eq hunit r
  obtain ⟨B, hsub, hloc⟩ := (LocalSubring.range φ).exists_le_valuationSubring
  have hmemL : ∀ x, φ x ∈ (LocalSubring.range φ).toSubring := fun x => by
    rw [LocalSubring.range_toSubring]; exact ⟨x, rfl⟩
  let ψ' : Localization.AtPrime 𝔭 →+* B := φ.codRestrict B (fun x => hsub (hmemL x))
  let ψ : R →+* B := ψ'.comp (algebraMap R (Localization.AtPrime 𝔭))
  have hψ : ∀ r, (ψ r : K) = ι r := fun r => hφ r
  haveI : IsAlgClosed (FractionRing B) :=
    IsAlgClosed.of_ringEquiv K _ (FractionRing.algEquiv B K).symm.toRingEquiv
  refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, ψ.toAlgebra, ?_, ?_⟩
  · intro h
    change ψ l = 0 at h
    apply hlq
    rw [← hι, ← hψ, h, ZeroMemClass.coe_zero]
  · ext r
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    change ¬ IsUnit (ψ r) ↔ r ∈ 𝔭
    constructor
    · intro h
      by_contra hr
      exact h ((IsLocalization.map_units (Localization.AtPrime 𝔭) (⟨r, hr⟩ : 𝔭.primeCompl)).map ψ')
    · intro hr hu
      have hxm : algebraMap R (Localization.AtPrime 𝔭) r ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) :=
        (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔭) 𝔭 r).mpr hr
      let y : (LocalSubring.range φ).toSubring :=
        ⟨φ (algebraMap R (Localization.AtPrime 𝔭) r), hmemL _⟩
      have hy : IsUnit y := hloc.map_nonunit y hu
      obtain ⟨z, hz⟩ := isUnit_iff_exists_inv.mp hy
      obtain ⟨w, hw⟩ : ∃ w, φ w = z := (LocalSubring.range_toSubring φ).le z.2
      have h1 : φ (algebraMap R (Localization.AtPrime 𝔭) r) * (z : K) = 1 := congrArg Subtype.val hz
      have hker : algebraMap R (Localization.AtPrime 𝔭) r * w - 1 ∈ RingHom.ker φ := by
        rw [RingHom.mem_ker, map_sub, map_mul, map_one, hw, h1, sub_self]
      have hkerle : RingHom.ker φ ≤ IsLocalRing.maximalIdeal _ :=
        IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top φ)
      have h1m : (1 : Localization.AtPrime 𝔭) ∈ IsLocalRing.maximalIdeal _ := by
        have hs := Ideal.sub_mem _ (Ideal.mul_mem_right w _ hxm) (hkerle hker)
        simpa using hs
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr h1m)

end UpperTheory.Gal.crystallineComparison
