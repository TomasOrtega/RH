import Mathlib
import GroundTheory.PAdicHodge.KerTheta
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Ideal WittVector IsLocalRing

section Abstract

variable {B : Type*} [CommRing B]

/- English proof (translation)
Use extensionality with `x`. Establish `h1 : I ^ n ≤ (I ^ n • ⊤ : Ideal A)` using `by simp`. Establish `h2 : (I ^ n • ⊤ : Ideal A) ≤ I ^ n` using `by simp`. Use `trans x ∈ (AdicCompletion.eval I A n).ker`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Rewrite `hx` using `[RingHom.mem_ker]`. Rewrite using `[LinearMap.mem_ker, ← AdicCompletion.factor_evalₐ_eq_eval I x h1]`. Simplify using `only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hx`. Simplify using `[hx]`.

Introduce `hx`. Rewrite `hx` using `[LinearMap.mem_ker]`. Rewrite using `[RingHom.mem_ker]`. Simplify using `only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]`. Rewrite using `[← AdicCompletion.factor_eval_eq_evalₐ I x h2, hx, map_zero]`.

Rewrite using `[← AdicCompletion.pow_smul_top_eq_ker_eval fg, Ideal.smul_top_eq_map]`. Both sides reduce to the same expression.
-/
theorem ker_adicCompletion_evalₐ {A : Type*} [CommRing A] {I : Ideal A} (fg : I.FG) (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ I n).toRingHom =
      (I ^ n).map (algebraMap A (AdicCompletion I A)) := by
  ext x
  have h1 : I ^ n ≤ (I ^ n • ⊤ : Ideal A) := by simp
  have h2 : (I ^ n • ⊤ : Ideal A) ≤ I ^ n := by simp
  trans x ∈ (AdicCompletion.eval I A n).ker
  · constructor
    · intro hx
      rw [RingHom.mem_ker] at hx
      rw [LinearMap.mem_ker, ← AdicCompletion.factor_evalₐ_eq_eval I x h1]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hx
      simp [hx]
    · intro hx
      rw [LinearMap.mem_ker] at hx
      rw [RingHom.mem_ker]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [← AdicCompletion.factor_eval_eq_evalₐ I x h2, hx, map_zero]
  · rw [← AdicCompletion.pow_smul_top_eq_ker_eval fg, Ideal.smul_top_eq_map]
    rfl

/- English proof (translation)
Use `hmax` as an intermediate fact. Establish `: IsLocalRing B` using `isLocalRing_of_isAdicComplete_maximal (span {π})`. Establish `hm : maximalIdeal B = span {π}` using `(IsLocalRing.eq_maximalIdeal hmax).symm`. Establish `hex : ∃ n, ¬ π ^ n ∣ x`. Assume the negation of the conclusion as `h`.

Use `push Not at h`. Apply `hx` to reduce the goal to its premises. Use `IsHausdorff.haus' (I := span {π}) x fun n => ?_` and prove the remaining obligations. Rewrite using `[smodEq_span_singleton_pow_iff, sub_zero]`. Conclude with `h n`.

Establish `hN0 : Nat.find hex ≠ 0`. Introduce `h0`. Use `Nat.find_spec hex` as an intermediate fact. Rewrite `this` using `[h0, pow_zero]`. Conclude with `this (one_dvd x)`.

Take `⟨k, hk⟩` from `Nat.exists_eq_succ_of_ne_zero hN0`. Establish `hdvd : π ^ k ∣ x`. Use `Nat.find_min hex (show k < Nat.find hex by omega)` as an intermediate fact. Use `push Not at this`. Conclude with `this`.

Take `⟨u, rfl⟩` from `hdvd`. Establish `hu : IsUnit u`. Assume the negation of the conclusion as `hu`. Establish `: u ∈ maximalIdeal B` using `(IsLocalRing.mem_maximalIdeal u).mpr hu`. Rewrite `this` using `[hm, mem_span_singleton]`.

Take `⟨c, rfl⟩` from `this`. Use `Nat.find_spec hex` as an intermediate fact. Rewrite `this` using `[hk]`. Conclude with `this ⟨c, by rw [pow_succ]; ring⟩`. Conclude with `⟨k, hu.unit, rfl⟩`.
-/
theorem exists_eq_pow_mul_unit_of_isAdicComplete {π : B} [IsAdicComplete (span {π}) B]
    (hmax : (span {π}).IsMaximal) {x : B} (hx : x ≠ 0) : ∃ (n : ℕ) (u : Bˣ), x = π ^ n * u := by
  classical
  have := hmax
  have : IsLocalRing B := isLocalRing_of_isAdicComplete_maximal (span {π})
  have hm : maximalIdeal B = span {π} := (IsLocalRing.eq_maximalIdeal hmax).symm
  have hex : ∃ n, ¬ π ^ n ∣ x := by
    by_contra h
    push Not at h
    apply hx
    refine IsHausdorff.haus' (I := span {π}) x fun n => ?_
    rw [smodEq_span_singleton_pow_iff, sub_zero]
    exact h n
  have hN0 : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0, pow_zero] at this
    exact this (one_dvd x)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  have hdvd : π ^ k ∣ x := by
    have := Nat.find_min hex (show k < Nat.find hex by omega)
    push Not at this
    exact this
  obtain ⟨u, rfl⟩ := hdvd
  have hu : IsUnit u := by
    by_contra hu
    have : u ∈ maximalIdeal B := (IsLocalRing.mem_maximalIdeal u).mpr hu
    rw [hm, mem_span_singleton] at this
    obtain ⟨c, rfl⟩ := this
    have := Nat.find_spec hex
    rw [hk] at this
    exact this ⟨c, by rw [pow_succ]; ring⟩
  exact ⟨k, hu.unit, rfl⟩

/- English proof (translation)
Establish `: Nontrivial B` using `⟨⟨1, 0, by simpa using hpow 0⟩⟩`. Establish `: NoZeroDivisors B`. Use `⟨fun {x y} hxy => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Take `⟨a, u, rfl⟩` from `exists_eq_pow_mul_unit_of_isAdicComplete hmax h.1`. Take `⟨b, v, rfl⟩` from `exists_eq_pow_mul_unit_of_isAdicComplete hmax h.2`. Apply `hpow (a + b)` to reduce the goal to its premises. Establish `: π ^ (a + b) * ((u * v : Bˣ) : B) = 0` using `by rw [Units.val_mul, ← hxy]; ring`. Conclude with `(Units.mul_left_eq_zero (u * v)).mp this`.

Conclude with `NoZeroDivisors.to_isDomain B`.
-/
theorem isDomain_of_isAdicComplete {π : B} [IsAdicComplete (span {π}) B]
    (hmax : (span {π}).IsMaximal) (hpow : ∀ n : ℕ, π ^ n ≠ 0) : IsDomain B := by
  have : Nontrivial B := ⟨⟨1, 0, by simpa using hpow 0⟩⟩
  have : NoZeroDivisors B := by
    refine ⟨fun {x y} hxy => ?_⟩
    by_contra h
    push Not at h
    obtain ⟨a, u, rfl⟩ := exists_eq_pow_mul_unit_of_isAdicComplete hmax h.1
    obtain ⟨b, v, rfl⟩ := exists_eq_pow_mul_unit_of_isAdicComplete hmax h.2
    apply hpow (a + b)
    have : π ^ (a + b) * ((u * v : Bˣ) : B) = 0 := by rw [Units.val_mul, ← hxy]; ring
    exact (Units.mul_left_eq_zero (u * v)).mp this
  exact NoZeroDivisors.to_isDomain B

/- English proof (translation)
The claim follows from `isDomain_of_isAdicComplete hmax hpow IsDiscreteValuationRing B ∧ Irreducible π := by have := isDomain_of_isAdicComplete hmax hpow have := hmax have : IsLocalRing B := isLocalRing_of_isAdicComplete_maximal (span {π}) have hm : maximalIdeal B = span {π} := (IsLocalRing.eq_maximalId …`.
-/
theorem isDiscreteValuationRing_of_isAdicComplete {π : B} [IsAdicComplete (span {π}) B]
    (hmax : (span {π}).IsMaximal) (hpow : ∀ n : ℕ, π ^ n ≠ 0) :
    haveI := isDomain_of_isAdicComplete hmax hpow
    IsDiscreteValuationRing B ∧ Irreducible π := by
  have := isDomain_of_isAdicComplete hmax hpow
  have := hmax
  have : IsLocalRing B := isLocalRing_of_isAdicComplete_maximal (span {π})
  have hm : maximalIdeal B = span {π} := (IsLocalRing.eq_maximalIdeal hmax).symm
  have hπ0 : π ≠ 0 := by simpa using hpow 1
  have hnu : ¬ IsUnit π := by
    intro h
    exact hmax.ne_top (Ideal.span_singleton_eq_top.mpr h)
  have hirr : Irreducible π := by
    refine ⟨hnu, ?_⟩
    intro a b hab
    by_contra h
    push Not at h
    have ha : a ∈ span {π} := hm ▸ (IsLocalRing.mem_maximalIdeal a).mpr h.1
    have hb : b ∈ span {π} := hm ▸ (IsLocalRing.mem_maximalIdeal b).mpr h.2
    rw [mem_span_singleton] at ha hb
    obtain ⟨c, rfl⟩ := ha
    obtain ⟨d, rfl⟩ := hb
    apply hnu
    have h1 : π * (1 - π * (c * d)) = 0 := by
      have : π = π * c * (π * d) := hab
      linear_combination this
    have h2 : 1 - π * (c * d) = 0 := (mul_eq_zero.mp h1).resolve_left hπ0
    exact isUnit_iff_exists_inv.mpr ⟨c * d, by linear_combination -h2⟩
  refine ⟨IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨π, hirr, ?_⟩, hirr⟩
  intro x hx
  obtain ⟨n, u, rfl⟩ := exists_eq_pow_mul_unit_of_isAdicComplete hmax hx
  exact ⟨n, u, rfl⟩

/- English proof (translation)
The claim follows from `(IsLocalRing.eq_maximalIdeal hmax).symm`.
-/
theorem maximalIdeal_eq_span_of_isMaximal [IsLocalRing B] {π : B} (hmax : (span {π}).IsMaximal) :
    maximalIdeal B = span {π} :=
  (IsLocalRing.eq_maximalIdeal hmax).symm

end Abstract

section General

variable (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (span {(p : R)}) R]

local notation "𝕎R♭" => WittVector p (PreTilt R p)
local notation "𝔸" => Localization.Away (p : WittVector p (PreTilt R p))

def toBDeRhamPlus : 𝔸 →+* BDeRhamPlus R p :=
  algebraMap 𝔸 (AdicCompletion (RingHom.ker (fontaineThetaInvertP R p)) 𝔸)

def wittToBDeRhamPlus : 𝕎R♭ →+* BDeRhamPlus R p :=
  (toBDeRhamPlus R p).comp (algebraMap 𝕎R♭ 𝔸)

def thetaBDeRhamPlus : BDeRhamPlus R p →+* Localization.Away (p : R) :=
  (RingHom.kerLift (fontaineThetaInvertP R p)).comp
    (AdicCompletion.evalOneₐ (RingHom.ker (fontaineThetaInvertP R p))).toRingHom

@[simp]
/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem thetaBDeRhamPlus_toBDeRhamPlus (x : 𝔸) :
    thetaBDeRhamPlus R p (toBDeRhamPlus R p x) = fontaineThetaInvertP R p x :=
  rfl

@[simp]
/- English proof (translation)
The claim follows from `IsLocalization.lift_eq _ x @[simp]`.
-/
theorem fontaineThetaInvertP_algebraMap (x : 𝕎R♭) :
    fontaineThetaInvertP R p (algebraMap 𝕎R♭ 𝔸 x) =
      algebraMap R (Localization.Away (p : R)) (fontaineTheta R p x) :=
  IsLocalization.lift_eq _ x

@[simp]
/- English proof (translation)
The claim follows from `fontaineThetaInvertP_algebraMap R p x`.
-/
theorem thetaBDeRhamPlus_wittToBDeRhamPlus (x : 𝕎R♭) :
    thetaBDeRhamPlus R p (wittToBDeRhamPlus R p x) =
      algebraMap R (Localization.Away (p : R)) (fontaineTheta R p x) :=
  fontaineThetaInvertP_algebraMap R p x

/- English proof (translation)
Introduce `z`. Take `⟨⟨r, ⟨_, n, rfl⟩⟩, rfl⟩` from `IsLocalization.mk'_surjective (Submonoid.powers (p : R)) z`. Take `⟨w, rfl⟩` from `hθ r`. Use `⟨IsLocalization.mk' 𝔸 w (⟨(p : 𝕎R♭) ^ n, n, rfl⟩ : Submonoid.powers (p : 𝕎R♭)), ?_⟩` and prove the remaining obligations. Use `symm`.

Establish `hpn : algebraMap R (Localization.Away (p : R)) ((p : R) ^ n) = fontaineThetaInvertP R p (algebraMap 𝕎R♭ 𝔸 ((p : 𝕎R♭) ^ n))`. Rewrite using `[fontaineThetaInvertP_algebraMap]`. Simplify using the standard rewrite rules. Rewrite using `[IsLocalization.mk'_eq_iff_eq_mul]`. Simplify using `only`.

Rewrite using `[hpn, ← map_mul, IsLocalization.mk'_spec, fontaineThetaInvertP_algebraMap]`.
-/
theorem surjective_fontaineThetaInvertP (hθ : Function.Surjective (fontaineTheta R p)) :
    Function.Surjective (fontaineThetaInvertP R p) := by
  intro z
  obtain ⟨⟨r, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (p : R)) z
  obtain ⟨w, rfl⟩ := hθ r
  refine ⟨IsLocalization.mk' 𝔸 w (⟨(p : 𝕎R♭) ^ n, n, rfl⟩ : Submonoid.powers (p : 𝕎R♭)), ?_⟩
  symm
  have hpn : algebraMap R (Localization.Away (p : R)) ((p : R) ^ n) =
      fontaineThetaInvertP R p (algebraMap 𝕎R♭ 𝔸 ((p : 𝕎R♭) ^ n)) := by
    rw [fontaineThetaInvertP_algebraMap]
    simp
  rw [IsLocalization.mk'_eq_iff_eq_mul]
  simp only
  rw [hpn, ← map_mul, IsLocalization.mk'_spec, fontaineThetaInvertP_algebraMap]

/- English proof (translation)
Introduce `z`. Take `⟨x, rfl⟩` from `surjective_fontaineThetaInvertP R p (surjective_fontaineTheta hF) z`. Conclude with `⟨toBDeRhamPlus R p x, rfl⟩`.
-/
theorem surjective_thetaBDeRhamPlus (hF : Function.Surjective (frobenius (ModP R p) p)) :
    Function.Surjective (thetaBDeRhamPlus R p) := by
  intro z
  obtain ⟨x, rfl⟩ := surjective_fontaineThetaInvertP R p (surjective_fontaineTheta hF) z
  exact ⟨toBDeRhamPlus R p x, rfl⟩

variable {R p}

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `z hz`. Rewrite `hz` using `[RingHom.mem_ker]`. Take `⟨⟨w, ⟨_, n, rfl⟩⟩, rfl⟩` from `IsLocalization.mk'_surjective (Submonoid.powers (p : 𝕎R♭)) z`. Establish `h1 : algebraMap R (Localization.Away (p : R)) (fontaineTheta R p w) = 0`.

Rewrite using `[← fontaineThetaInvertP_algebraMap, ← IsLocalization.mk'_spec 𝔸 w (⟨(p : 𝕎R♭) ^ n, n, rfl⟩ : Submonoid.powers (p : 𝕎R♭)), map_mul, hz, zero_mul]`. Take `⟨⟨_, k, rfl⟩, hk⟩` from `(IsLocalization.map_eq_zero_iff (Submonoid.powers (p : R)) _ _).mp h1`. Establish `h2 : (p : 𝕎R♭) ^ k * w ∈ span {ξ}`. Rewrite using `[← hξ, RingHom.mem_ker, map_mul, map_pow, map_natCast]`. Conclude with `hk`.

Take `⟨c, hc⟩` from `mem_span_singleton'.mp h2`. Establish `hu : IsUnit (algebraMap 𝕎R♭ 𝔸 ((p : 𝕎R♭) ^ k * (p : 𝕎R♭) ^ n))` using `IsLocalization.map_units 𝔸 (⟨_, mul_mem (pow_mem (Submonoid.mem_powers _) k) (pow_mem (Submonoid.mem_powers _) n)⟩ : Submonoid.powers (p : 𝕎R♭))`. Rewrite using `[mem_span_singleton, ← hu.dvd_mul_right]`. Use `⟨algebraMap 𝕎R♭ 𝔸 c, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, fontaineThetaInvertP_algebraMap]`. Establish `: ξ ∈ RingHom.ker (fontaineTheta R p)` using `hξ ▸ mem_span_singleton_self ξ`. Rewrite `this` using `[RingHom.mem_ker]`. Rewrite using `[this, map_zero]`.
-/
theorem ker_fontaineThetaInvertP {ξ : 𝕎R♭} (hξ : RingHom.ker (fontaineTheta R p) = span {ξ}) :
    RingHom.ker (fontaineThetaInvertP R p) = span {algebraMap 𝕎R♭ 𝔸 ξ} := by
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker] at hz
    obtain ⟨⟨w, ⟨_, n, rfl⟩⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (Submonoid.powers (p : 𝕎R♭)) z
    have h1 : algebraMap R (Localization.Away (p : R)) (fontaineTheta R p w) = 0 := by
      rw [← fontaineThetaInvertP_algebraMap,
        ← IsLocalization.mk'_spec 𝔸 w (⟨(p : 𝕎R♭) ^ n, n, rfl⟩ : Submonoid.powers (p : 𝕎R♭)),
        map_mul, hz, zero_mul]
    obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (p : R)) _ _).mp h1
    have h2 : (p : 𝕎R♭) ^ k * w ∈ span {ξ} := by
      rw [← hξ, RingHom.mem_ker, map_mul, map_pow, map_natCast]
      exact hk
    obtain ⟨c, hc⟩ := mem_span_singleton'.mp h2
    have hu : IsUnit (algebraMap 𝕎R♭ 𝔸 ((p : 𝕎R♭) ^ k * (p : 𝕎R♭) ^ n)) :=
      IsLocalization.map_units 𝔸 (⟨_, mul_mem (pow_mem (Submonoid.mem_powers _) k)
        (pow_mem (Submonoid.mem_powers _) n)⟩ : Submonoid.powers (p : 𝕎R♭))
    rw [mem_span_singleton, ← hu.dvd_mul_right]
    refine ⟨algebraMap 𝕎R♭ 𝔸 c, ?_⟩
    calc IsLocalization.mk' 𝔸 w (⟨(p : 𝕎R♭) ^ n, n, rfl⟩ : Submonoid.powers (p : 𝕎R♭)) *
          algebraMap 𝕎R♭ 𝔸 ((p : 𝕎R♭) ^ k * (p : 𝕎R♭) ^ n)
        = algebraMap 𝕎R♭ 𝔸 ((p : 𝕎R♭) ^ k) *
          (IsLocalization.mk' 𝔸 w (⟨(p : 𝕎R♭) ^ n, n, rfl⟩ : Submonoid.powers (p : 𝕎R♭)) *
            algebraMap 𝕎R♭ 𝔸 ((p : 𝕎R♭) ^ n)) := by rw [map_mul]; ring
      _ = algebraMap 𝕎R♭ 𝔸 ((p : 𝕎R♭) ^ k * w) := by rw [IsLocalization.mk'_spec, map_mul]
      _ = algebraMap 𝕎R♭ 𝔸 ξ * algebraMap 𝕎R♭ 𝔸 c := by rw [← hc, map_mul, mul_comm]
  · rw [span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
      fontaineThetaInvertP_algebraMap]
    have : ξ ∈ RingHom.ker (fontaineTheta R p) := hξ ▸ mem_span_singleton_self ξ
    rw [RingHom.mem_ker] at this
    rw [this, map_zero]

/- English proof (translation)
Assemble the required witnesses or components as `⟨{algebraMap 𝕎R♭ 𝔸 ξ}, by rw [ker_fontaineThetaInvertP hξ, Finset.coe_singleton]⟩`.
-/
theorem fg_ker_fontaineThetaInvertP {ξ : 𝕎R♭} (hξ : RingHom.ker (fontaineTheta R p) = span {ξ}) :
    (RingHom.ker (fontaineThetaInvertP R p)).FG :=
  ⟨{algebraMap 𝕎R♭ 𝔸 ξ}, by rw [ker_fontaineThetaInvertP hξ, Finset.coe_singleton]⟩

/- English proof (translation)
Establish `h` using `AdicCompletion.ker_evalOneₐ_eq_map _ (fg_ker_fontaineThetaInvertP hξ)`. Establish `h' : span {wittToBDeRhamPlus R p ξ} = (RingHom.ker (fontaineThetaInvertP R p)).map (toBDeRhamPlus R p)`. Rewrite using `[ker_fontaineThetaInvertP hξ, Ideal.map_span, Set.image_singleton]`. Both sides reduce to the same expression. Rewrite using `[h']`.

Use extensionality with `x`. Establish `h2 : ∀ y : AdicCompletion (RingHom.ker (fontaineThetaInvertP R p)) 𝔸, y ∈ (RingHom.ker (fontaineThetaInvertP R p)).map (algebraMap 𝔸 (AdicCompletion (RingHom.ker (fontaineThetaInvertP R p)) 𝔸)) ↔ AdicCompletion.evalOneₐ (RingHom.ker (fontaineThetaInvertP R p)) y = 0` using `fun y => by`. Rewrite using `[← h, RingHom.mem_ker]`. Both sides reduce to the same expression. Establish `hx : thetaBDeRhamPlus R p x = 0 ↔ AdicCompletion.evalOneₐ (RingHom.ker (fontaineThetaInvertP R p)) x = 0` using `map_eq_zero_iff (RingHom.kerLift (fontaineThetaInvertP R p)) (RingHom.kerLift_injective _)`.

Conclude with `(RingHom.mem_ker.trans hx).trans (h2 x).symm`.
-/
theorem ker_thetaBDeRhamPlus {ξ : 𝕎R♭} (hξ : RingHom.ker (fontaineTheta R p) = span {ξ}) :
    RingHom.ker (thetaBDeRhamPlus R p) = span {wittToBDeRhamPlus R p ξ} := by
  have h := AdicCompletion.ker_evalOneₐ_eq_map _ (fg_ker_fontaineThetaInvertP hξ)
  have h' : span {wittToBDeRhamPlus R p ξ} =
      (RingHom.ker (fontaineThetaInvertP R p)).map (toBDeRhamPlus R p) := by
    rw [ker_fontaineThetaInvertP hξ, Ideal.map_span, Set.image_singleton]
    rfl
  rw [h']
  ext x
  have h2 : ∀ y : AdicCompletion (RingHom.ker (fontaineThetaInvertP R p)) 𝔸,
      y ∈ (RingHom.ker (fontaineThetaInvertP R p)).map
        (algebraMap 𝔸 (AdicCompletion (RingHom.ker (fontaineThetaInvertP R p)) 𝔸)) ↔
        AdicCompletion.evalOneₐ (RingHom.ker (fontaineThetaInvertP R p)) y = 0 := fun y => by
    rw [← h, RingHom.mem_ker]
    rfl
  have hx : thetaBDeRhamPlus R p x = 0 ↔
      AdicCompletion.evalOneₐ (RingHom.ker (fontaineThetaInvertP R p)) x = 0 :=
    map_eq_zero_iff (RingHom.kerLift (fontaineThetaInvertP R p)) (RingHom.kerLift_injective _)
  exact (RingHom.mem_ker.trans hx).trans (h2 x).symm

/- English proof (translation)
Establish `h` using `AdicCompletion.isAdicComplete_self _ (fg_ker_fontaineThetaInvertP hξ)`. Establish `h' : span {wittToBDeRhamPlus R p ξ} = (RingHom.ker (fontaineThetaInvertP R p)).map (toBDeRhamPlus R p)`. Rewrite using `[ker_fontaineThetaInvertP hξ, Ideal.map_span, Set.image_singleton]`. Both sides reduce to the same expression. Rewrite using `[h']`.

Conclude with `h`.
-/
theorem isAdicComplete_bDeRhamPlus {ξ : 𝕎R♭} (hξ : RingHom.ker (fontaineTheta R p) = span {ξ}) :
    IsAdicComplete (span {wittToBDeRhamPlus R p ξ}) (BDeRhamPlus R p) := by
  have h := AdicCompletion.isAdicComplete_self _ (fg_ker_fontaineThetaInvertP hξ)
  have h' : span {wittToBDeRhamPlus R p ξ} =
      (RingHom.ker (fontaineThetaInvertP R p)).map (toBDeRhamPlus R p) := by
    rw [ker_fontaineThetaInvertP hξ, Ideal.map_span, Set.image_singleton]
    rfl
  rw [h']
  exact h

/- English proof (translation)
Establish `h` using `ker_adicCompletion_evalₐ (fg_ker_fontaineThetaInvertP hξ) n`. Establish `h' : span {wittToBDeRhamPlus R p ξ ^ n} = (RingHom.ker (fontaineThetaInvertP R p) ^ n).map (toBDeRhamPlus R p)`. Rewrite using `[ker_fontaineThetaInvertP hξ, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, map_pow]`. Both sides reduce to the same expression. Rewrite using `[h']`.

Establish `h2 : ∀ y : AdicCompletion (RingHom.ker (fontaineThetaInvertP R p)) 𝔸, y ∈ (RingHom.ker (fontaineThetaInvertP R p) ^ n).map (algebraMap 𝔸 (AdicCompletion (RingHom.ker (fontaineThetaInvertP R p)) 𝔸)) ↔ AdicCompletion.evalₐ (RingHom.ker (fontaineThetaInvertP R p)) n y = 0` using `fun y => by`. Rewrite using `[← h, RingHom.mem_ker]`. Both sides reduce to the same expression. Use `(h2 (algebraMap 𝔸 _ a)).trans ?_` and prove the remaining obligations. Rewrite using `[AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, AdicCompletion.evalₐ_of, Ideal.Quotient.eq_zero_iff_mem, ker_fontaineThetaInvertP hξ, Ideal.span_singleton_pow, mem_span_singleton]`.
-/
theorem toBDeRhamPlus_mem_span_pow_iff {ξ : 𝕎R♭}
    (hξ : RingHom.ker (fontaineTheta R p) = span {ξ}) (a : 𝔸) (n : ℕ) :
    toBDeRhamPlus R p a ∈ span {wittToBDeRhamPlus R p ξ ^ n} ↔ algebraMap 𝕎R♭ 𝔸 ξ ^ n ∣ a := by
  have h := ker_adicCompletion_evalₐ (fg_ker_fontaineThetaInvertP hξ) n
  have h' : span {wittToBDeRhamPlus R p ξ ^ n} =
      (RingHom.ker (fontaineThetaInvertP R p) ^ n).map (toBDeRhamPlus R p) := by
    rw [ker_fontaineThetaInvertP hξ, Ideal.span_singleton_pow, Ideal.map_span,
      Set.image_singleton, map_pow]
    rfl
  rw [h']
  have h2 : ∀ y : AdicCompletion (RingHom.ker (fontaineThetaInvertP R p)) 𝔸,
      y ∈ (RingHom.ker (fontaineThetaInvertP R p) ^ n).map
        (algebraMap 𝔸 (AdicCompletion (RingHom.ker (fontaineThetaInvertP R p)) 𝔸)) ↔
        AdicCompletion.evalₐ (RingHom.ker (fontaineThetaInvertP R p)) n y = 0 := fun y => by
    rw [← h, RingHom.mem_ker]
    rfl
  refine (h2 (algebraMap 𝔸 _ a)).trans ?_
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    AdicCompletion.evalₐ_of, Ideal.Quotient.eq_zero_iff_mem, ker_fontaineThetaInvertP hξ,
    Ideal.span_singleton_pow, mem_span_singleton]

omit [IsAdicComplete (span {(p : R)}) R] in

/- English proof (translation)
Take `⟨⟨w, s⟩, rfl⟩` from `IsLocalization.mk'_surjective (Submonoid.powers (p : 𝕎R♭)) y`. Rewrite `h` using `[IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_zero_iff]`. Take `⟨m, hm⟩` from `h`. Rewrite using `[IsLocalization.mk'_eq_zero_iff]`. Use `⟨m, mem_nonZeroDivisors_iff_left.mp hx _ ?_⟩` and prove the remaining obligations.

Rewrite using `[← hm]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eq_zero_of_algebraMap_mul_eq_zero {x : 𝕎R♭} (hx : x ∈ nonZeroDivisors 𝕎R♭) {y : 𝔸}
    (h : algebraMap 𝕎R♭ 𝔸 x * y = 0) : y = 0 := by
  obtain ⟨⟨w, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (p : 𝕎R♭)) y
  rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_zero_iff] at h
  obtain ⟨m, hm⟩ := h
  rw [IsLocalization.mk'_eq_zero_iff]
  refine ⟨m, mem_nonZeroDivisors_iff_left.mp hx _ ?_⟩
  rw [← hm]
  ring

end General

section DVR

variable {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (span {(p : R)}) R]

local notation "𝕎R♭" => WittVector p (PreTilt R p)
local notation "𝔸" => Localization.Away (p : WittVector p (PreTilt R p))

/- English proof (translation)
The claim follows from `Ideal.Quotient.maximal_of_isField _ (MulEquiv.isField hK (RingHom.quotientKerEquivOfSurjective (surjective_thetaBDeRhamPlus R p hF)).toMulEquiv)`.
-/
theorem isMaximal_ker_thetaBDeRhamPlus (hF : Function.Surjective (frobenius (ModP R p) p))
    (hK : IsField (Localization.Away (p : R))) : (RingHom.ker (thetaBDeRhamPlus R p)).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _ (MulEquiv.isField hK
    (RingHom.quotientKerEquivOfSurjective (surjective_thetaBDeRhamPlus R p hF)).toMulEquiv)

/- English proof (translation)
Introduce `h0`. Establish `hmem : toBDeRhamPlus R p (algebraMap 𝕎R♭ 𝔸 ξ ^ n) ∈ span {wittToBDeRhamPlus R p ξ ^ (n + 1)}`. Rewrite using `[map_pow]`. Express the relevant statement in the definitionally equal form `wittToBDeRhamPlus R p ξ ^ n ∈ _`. Rewrite using `[h0]`.

Conclude with `zero_mem _`. Rewrite `hmem` using `[toBDeRhamPlus_mem_span_pow_iff hξ]`. Take `⟨c, hc⟩` from `hmem`. Establish `h1 : algebraMap 𝕎R♭ 𝔸 (ξ ^ n) * (1 - algebraMap 𝕎R♭ 𝔸 ξ * c) = 0`. Rewrite using `[map_pow, mul_sub, mul_one, ← mul_assoc, ← pow_succ, ← hc, sub_self]`.

Establish `h2` using `eq_zero_of_algebraMap_mul_eq_zero (pow_mem hξ0 n) h1`. Establish `hone : (1 : 𝔸) ∈ RingHom.ker (fontaineThetaInvertP R p)`. Rewrite using `[ker_fontaineThetaInvertP hξ, mem_span_singleton]`. Conclude with `⟨c, by linear_combination h2⟩`. Rewrite `hone` using `[RingHom.mem_ker, map_one]`.

Conclude with `one_ne_zero hone`.
-/
theorem pow_wittToBDeRhamPlus_ne_zero [Nontrivial (Localization.Away (p : R))] {ξ : 𝕎R♭}
    (hξ : RingHom.ker (fontaineTheta R p) = span {ξ}) (hξ0 : ξ ∈ nonZeroDivisors 𝕎R♭) (n : ℕ) :
    wittToBDeRhamPlus R p ξ ^ n ≠ 0 := by
  intro h0
  have hmem : toBDeRhamPlus R p (algebraMap 𝕎R♭ 𝔸 ξ ^ n) ∈
      span {wittToBDeRhamPlus R p ξ ^ (n + 1)} := by
    rw [map_pow]
    change wittToBDeRhamPlus R p ξ ^ n ∈ _
    rw [h0]
    exact zero_mem _
  rw [toBDeRhamPlus_mem_span_pow_iff hξ] at hmem
  obtain ⟨c, hc⟩ := hmem
  have h1 : algebraMap 𝕎R♭ 𝔸 (ξ ^ n) * (1 - algebraMap 𝕎R♭ 𝔸 ξ * c) = 0 := by
    rw [map_pow, mul_sub, mul_one, ← mul_assoc, ← pow_succ, ← hc, sub_self]
  have h2 := eq_zero_of_algebraMap_mul_eq_zero (pow_mem hξ0 n) h1
  have hone : (1 : 𝔸) ∈ RingHom.ker (fontaineThetaInvertP R p) := by
    rw [ker_fontaineThetaInvertP hξ, mem_span_singleton]
    exact ⟨c, by linear_combination h2⟩
  rw [RingHom.mem_ker, map_one] at hone
  exact one_ne_zero hone

/- English proof (translation)
Use `isAdicComplete_bDeRhamPlus hξ` as an intermediate fact. Establish `: (span {wittToBDeRhamPlus R p ξ}).IsMaximal` using `ker_thetaBDeRhamPlus hξ ▸ isMaximal_ker_thetaBDeRhamPlus hF hK`. Conclude with `isLocalRing_of_isAdicComplete_maximal (span {wittToBDeRhamPlus R p ξ})`.
-/
theorem isLocalRing_bDeRhamPlus {ξ : 𝕎R♭} (hξ : RingHom.ker (fontaineTheta R p) = span {ξ})
    (hF : Function.Surjective (frobenius (ModP R p) p)) (hK : IsField (Localization.Away (p : R))) :
    IsLocalRing (BDeRhamPlus R p) := by
  have := isAdicComplete_bDeRhamPlus hξ
  have : (span {wittToBDeRhamPlus R p ξ}).IsMaximal :=
    ker_thetaBDeRhamPlus hξ ▸ isMaximal_ker_thetaBDeRhamPlus hF hK
  exact isLocalRing_of_isAdicComplete_maximal (span {wittToBDeRhamPlus R p ξ})

/- English proof (translation)
Use `isAdicComplete_bDeRhamPlus hξ` as an intermediate fact. Use `hK.nontrivial` as an intermediate fact. Conclude with `isDomain_of_isAdicComplete (ker_thetaBDeRhamPlus hξ ▸ isMaximal_ker_thetaBDeRhamPlus hF hK) (pow_wittToBDeRhamPlus_ne_zero hξ hξ0)`.
-/
theorem isDomain_bDeRhamPlus {ξ : 𝕎R♭} (hξ : RingHom.ker (fontaineTheta R p) = span {ξ})
    (hξ0 : ξ ∈ nonZeroDivisors 𝕎R♭) (hF : Function.Surjective (frobenius (ModP R p) p))
    (hK : IsField (Localization.Away (p : R))) : IsDomain (BDeRhamPlus R p) := by
  have := isAdicComplete_bDeRhamPlus hξ
  have := hK.nontrivial
  exact isDomain_of_isAdicComplete
    (ker_thetaBDeRhamPlus hξ ▸ isMaximal_ker_thetaBDeRhamPlus hF hK)
    (pow_wittToBDeRhamPlus_ne_zero hξ hξ0)

/- English proof (translation)
The claim follows from `isDomain_bDeRhamPlus hξ hξ0 hF hK IsDiscreteValuationRing (BDeRhamPlus R p) := by have := isAdicComplete_bDeRhamPlus hξ have := hK.nontrivial exact (isDiscreteValuationRing_of_isAdicComplete (ker_thetaBDeRhamPlus hξ ▸ isMaximal_ker_thetaBDeRhamPlus hF hK) (pow_wittToBDeRhamPlus_n …`.
-/
theorem isDiscreteValuationRing_bDeRhamPlus {ξ : 𝕎R♭}
    (hξ : RingHom.ker (fontaineTheta R p) = span {ξ}) (hξ0 : ξ ∈ nonZeroDivisors 𝕎R♭)
    (hF : Function.Surjective (frobenius (ModP R p) p)) (hK : IsField (Localization.Away (p : R))) :
    haveI := isDomain_bDeRhamPlus hξ hξ0 hF hK
    IsDiscreteValuationRing (BDeRhamPlus R p) := by
  have := isAdicComplete_bDeRhamPlus hξ
  have := hK.nontrivial
  exact (isDiscreteValuationRing_of_isAdicComplete
    (ker_thetaBDeRhamPlus hξ ▸ isMaximal_ker_thetaBDeRhamPlus hF hK)
    (pow_wittToBDeRhamPlus_ne_zero hξ hξ0)).1

/- English proof (translation)
Use `isAdicComplete_bDeRhamPlus hξ` as an intermediate fact. Use `hK.nontrivial` as an intermediate fact. Conclude with `(isDiscreteValuationRing_of_isAdicComplete (ker_thetaBDeRhamPlus hξ ▸ isMaximal_ker_thetaBDeRhamPlus hF hK) (pow_wittToBDeRhamPlus_ne_zero hξ hξ0)).2`.
-/
theorem irreducible_wittToBDeRhamPlus {ξ : 𝕎R♭}
    (hξ : RingHom.ker (fontaineTheta R p) = span {ξ}) (hξ0 : ξ ∈ nonZeroDivisors 𝕎R♭)
    (hF : Function.Surjective (frobenius (ModP R p) p)) (hK : IsField (Localization.Away (p : R))) :
    Irreducible (wittToBDeRhamPlus R p ξ) := by
  have := isAdicComplete_bDeRhamPlus hξ
  have := hK.nontrivial
  exact (isDiscreteValuationRing_of_isAdicComplete
    (ker_thetaBDeRhamPlus hξ ▸ isMaximal_ker_thetaBDeRhamPlus hF hK)
    (pow_wittToBDeRhamPlus_ne_zero hξ hξ0)).2

/- English proof (translation)
The claim follows from `isLocalRing_bDeRhamPlus hξ hF hK maximalIdeal (BDeRhamPlus R p) = RingHom.ker (thetaBDeRhamPlus R p) := haveI := isLocalRing_bDeRhamPlus hξ hF hK (IsLocalRing.eq_maximalIdeal (isMaximal_ker_thetaBDeRhamPlus hF hK)).symm`.
-/
theorem maximalIdeal_bDeRhamPlus {ξ : 𝕎R♭} (hξ : RingHom.ker (fontaineTheta R p) = span {ξ})
    (hF : Function.Surjective (frobenius (ModP R p) p)) (hK : IsField (Localization.Away (p : R))) :
    haveI := isLocalRing_bDeRhamPlus hξ hF hK
    maximalIdeal (BDeRhamPlus R p) = RingHom.ker (thetaBDeRhamPlus R p) :=
  haveI := isLocalRing_bDeRhamPlus hξ hF hK
  (IsLocalRing.eq_maximalIdeal (isMaximal_ker_thetaBDeRhamPlus hF hK)).symm

/- English proof (translation)
The claim follows from `isLocalRing_bDeRhamPlus hξ hF hK maximalIdeal (BDeRhamPlus R p) = span {wittToBDeRhamPlus R p ξ} := (maximalIdeal_bDeRhamPlus hξ hF hK).trans (ker_thetaBDeRhamPlus hξ)`.
-/
theorem maximalIdeal_bDeRhamPlus_eq_span {ξ : 𝕎R♭}
    (hξ : RingHom.ker (fontaineTheta R p) = span {ξ})
    (hF : Function.Surjective (frobenius (ModP R p) p)) (hK : IsField (Localization.Away (p : R))) :
    haveI := isLocalRing_bDeRhamPlus hξ hF hK
    maximalIdeal (BDeRhamPlus R p) = span {wittToBDeRhamPlus R p ξ} :=
  (maximalIdeal_bDeRhamPlus hξ hF hK).trans (ker_thetaBDeRhamPlus hξ)

def residueFieldBDeRhamPlusEquiv {ξ : 𝕎R♭} (hξ : RingHom.ker (fontaineTheta R p) = span {ξ})
    (hF : Function.Surjective (frobenius (ModP R p) p)) (hK : IsField (Localization.Away (p : R))) :
    haveI := isLocalRing_bDeRhamPlus hξ hF hK
    ResidueField (BDeRhamPlus R p) ≃+* Localization.Away (p : R) :=
  haveI := isLocalRing_bDeRhamPlus hξ hF hK
  (Ideal.quotEquivOfEq (maximalIdeal_bDeRhamPlus hξ hF hK)).trans
    (RingHom.quotientKerEquivOfSurjective (surjective_thetaBDeRhamPlus R p hF))

/- English proof (translation)
The claim follows from `isLocalRing_bDeRhamPlus hξ hF hK residueFieldBDeRhamPlusEquiv hξ hF hK (residue (BDeRhamPlus R p) x) = thetaBDeRhamPlus R p x := rfl`.
-/
theorem residueFieldBDeRhamPlusEquiv_residue {ξ : 𝕎R♭}
    (hξ : RingHom.ker (fontaineTheta R p) = span {ξ})
    (hF : Function.Surjective (frobenius (ModP R p) p)) (hK : IsField (Localization.Away (p : R)))
    (x : BDeRhamPlus R p) :
    haveI := isLocalRing_bDeRhamPlus hξ hF hK
    residueFieldBDeRhamPlusEquiv hξ hF hK (residue (BDeRhamPlus R p) x) = thetaBDeRhamPlus R p x :=
  rfl

end DVR

namespace IsPerfectoidField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p]

local notation "𝒪" => normInteger K
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger K) p)
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔹" => BDeRhamPlus (normInteger K) p

/- English proof (translation)
Rewrite using `[IsLocalization.Away, isLocalization_iff]`. Establish `hp0 : (p : K) ≠ 0` using `Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero`. Establish `hpn : ‖(p : K)‖ < 1` using `IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p)`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨_, n, rfl⟩`.

Simplify using `only [map_pow, map_natCast]`. Conclude with `(isUnit_iff_ne_zero.mpr hp0).pow n`. Introduce `z`. Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one (show (0 : ℝ) < (‖z‖ + 1)⁻¹ by positivity) hpn`. Use `⟨⟨⟨z * (p : K) ^ n, ?_⟩, ⟨(p : 𝒪) ^ n, n, rfl⟩⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[mem_normInteger, norm_mul, norm_pow]`. Establish `h1 : ‖z‖ * ‖(p : K)‖ ^ n ≤ ‖z‖ * (‖z‖ + 1)⁻¹` using `mul_le_mul_of_nonneg_left hn.le (norm_nonneg z)`. Establish `h2 : ‖z‖ * (‖z‖ + 1)⁻¹ ≤ 1`. Rewrite using `[← div_eq_mul_inv, div_le_one (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear equalities and inequalities to obtain the conclusion. Both sides reduce to the same expression. Introduce `x y h`. Conclude with `⟨1, by simpa using Subtype.ext h⟩`.
-/
theorem isLocalization_away [CharZero K] : IsLocalization.Away (p : 𝒪) K := by
  rw [IsLocalization.Away, isLocalization_iff]
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpn : ‖(p : K)‖ < 1 := IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p)
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    simp only [map_pow, map_natCast]
    exact (isUnit_iff_ne_zero.mpr hp0).pow n
  · intro z
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < (‖z‖ + 1)⁻¹ by positivity) hpn
    refine ⟨⟨⟨z * (p : K) ^ n, ?_⟩, ⟨(p : 𝒪) ^ n, n, rfl⟩⟩, ?_⟩
    · rw [mem_normInteger, norm_mul, norm_pow]
      have h1 : ‖z‖ * ‖(p : K)‖ ^ n ≤ ‖z‖ * (‖z‖ + 1)⁻¹ :=
        mul_le_mul_of_nonneg_left hn.le (norm_nonneg z)
      have h2 : ‖z‖ * (‖z‖ + 1)⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one (by positivity)]
        linarith
      linarith
    · rfl
  · intro x y h
    exact ⟨1, by simpa using Subtype.ext h⟩

def awayEquiv [CharZero K] : Localization.Away (p : 𝒪) ≃ₐ[𝒪] K :=
  haveI := isLocalization_away (K := K) p
  IsLocalization.algEquiv (Submonoid.powers (p : 𝒪)) _ K

/- English proof (translation)
The claim follows from `MulEquiv.isField (Field.toIsField K) (awayEquiv (K := K) p).toMulEquiv`.
-/
theorem isField_away [CharZero K] : IsField (Localization.Away (p : 𝒪)) :=
  MulEquiv.isField (Field.toIsField K) (awayEquiv (K := K) p).toMulEquiv

def thetaBDeRhamPlusField [CharZero K] : 𝔹 →+* K :=
  (awayEquiv (K := K) p).toRingEquiv.toRingHom.comp (thetaBDeRhamPlus 𝒪 p)

/- English proof (translation)
Simplify using `only [thetaBDeRhamPlusField, RingHom.comp_apply, thetaBDeRhamPlus_wittToBDeRhamPlus]`. Conclude with `(awayEquiv (K := K) p).commutes (θ x)`.
-/
theorem thetaBDeRhamPlusField_wittToBDeRhamPlus [CharZero K] (x : 𝕎𝒪♭) :
    thetaBDeRhamPlusField p (wittToBDeRhamPlus 𝒪 p x) = (θ x : K) := by
  simp only [thetaBDeRhamPlusField, RingHom.comp_apply, thetaBDeRhamPlus_wittToBDeRhamPlus]
  exact (awayEquiv (K := K) p).commutes (θ x)

/- English proof (translation)
The claim follows from `(awayEquiv (K := K) p).surjective.comp (surjective_thetaBDeRhamPlus 𝒪 p (surjective_frobenius p))`.
-/
theorem surjective_thetaBDeRhamPlusField [CharZero K] :
    Function.Surjective (thetaBDeRhamPlusField (K := K) p) :=
  (awayEquiv (K := K) p).surjective.comp (surjective_thetaBDeRhamPlus 𝒪 p (surjective_frobenius p))

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [RingHom.mem_ker, thetaBDeRhamPlusField, RingHom.comp_apply]`. Conclude with `map_eq_zero_iff _ (awayEquiv (K := K) p).injective`.
-/
theorem ker_thetaBDeRhamPlusField [CharZero K] :
    RingHom.ker (thetaBDeRhamPlusField (K := K) p) = RingHom.ker (thetaBDeRhamPlus 𝒪 p) := by
  ext x
  simp only [RingHom.mem_ker, thetaBDeRhamPlusField, RingHom.comp_apply]
  exact map_eq_zero_iff _ (awayEquiv (K := K) p).injective

variable {p}

/- English proof (translation)
Use `isDomain_preTilt (K := K) p` as an intermediate fact. Use `isDomain_wittVector_preTilt K p` as an intermediate fact. Use `mem_nonZeroDivisors_of_ne_zero fun h0 => ?_` and prove the remaining obligations. Take `⟨ξ₀, h₀, h1⟩` from `exists_mem_ker_fontaineTheta_isUnit_coeff_one K p`. Rewrite `h₀` using `[hξ, h0, mem_span_singleton, zero_dvd_iff]`.

Rewrite `h1` using `[h₀, zero_coeff]`. Conclude with `not_isUnit_zero h1`.
-/
theorem mem_nonZeroDivisors_of_ker_eq_span {ξ : 𝕎𝒪♭} (hξ : RingHom.ker θ = span {ξ}) :
    ξ ∈ nonZeroDivisors 𝕎𝒪♭ := by
  have := isDomain_preTilt (K := K) p
  have := isDomain_wittVector_preTilt K p
  refine mem_nonZeroDivisors_of_ne_zero fun h0 => ?_
  obtain ⟨ξ₀, h₀, h1⟩ := exists_mem_ker_fontaineTheta_isUnit_coeff_one K p
  rw [hξ, h0, mem_span_singleton, zero_dvd_iff] at h₀
  rw [h₀, zero_coeff] at h1
  exact not_isUnit_zero h1

variable (K p) in

def kerThetaGenerator : 𝕎𝒪♭ :=
  haveI := isPrincipal_ker_fontaineTheta K p
  Submodule.IsPrincipal.generator (RingHom.ker θ)

variable (K p) in

/- English proof (translation)
The claim follows from `haveI := isPrincipal_ker_fontaineTheta K p (Submodule.IsPrincipal.span_singleton_generator (RingHom.ker θ)).symm`.
-/
theorem ker_fontaineTheta_eq_span_kerThetaGenerator : RingHom.ker θ = span {kerThetaGenerator K p} :=
  haveI := isPrincipal_ker_fontaineTheta K p
  (Submodule.IsPrincipal.span_singleton_generator (RingHom.ker θ)).symm

variable [CharZero K]

instance isDomain_bDeRhamPlus : IsDomain 𝔹 :=
  GroundTheory.PAdicHodge.isDomain_bDeRhamPlus (ker_fontaineTheta_eq_span_kerThetaGenerator K p)
    (mem_nonZeroDivisors_of_ker_eq_span (ker_fontaineTheta_eq_span_kerThetaGenerator K p))
    (surjective_frobenius p) (isField_away p)

instance isDiscreteValuationRing_bDeRhamPlus : IsDiscreteValuationRing 𝔹 :=
  GroundTheory.PAdicHodge.isDiscreteValuationRing_bDeRhamPlus (ker_fontaineTheta_eq_span_kerThetaGenerator K p)
    (mem_nonZeroDivisors_of_ker_eq_span (ker_fontaineTheta_eq_span_kerThetaGenerator K p))
    (surjective_frobenius p) (isField_away p)

/- English proof (translation)
Rewrite using `[ker_thetaBDeRhamPlusField]`. Conclude with `GroundTheory.PAdicHodge.maximalIdeal_bDeRhamPlus (ker_fontaineTheta_eq_span_kerThetaGenerator K p) (surjective_frobenius p) (isField_away p)`.
-/
theorem maximalIdeal_bDeRhamPlus :
    maximalIdeal 𝔹 = RingHom.ker (thetaBDeRhamPlusField (K := K) p) := by
  rw [ker_thetaBDeRhamPlusField]
  exact GroundTheory.PAdicHodge.maximalIdeal_bDeRhamPlus (ker_fontaineTheta_eq_span_kerThetaGenerator K p)
    (surjective_frobenius p) (isField_away p)

/- English proof (translation)
The claim follows from `GroundTheory.PAdicHodge.maximalIdeal_bDeRhamPlus_eq_span hξ (surjective_frobenius p) (isField_away p)`.
-/
theorem maximalIdeal_bDeRhamPlus_eq_span {ξ : 𝕎𝒪♭} (hξ : RingHom.ker θ = span {ξ}) :
    maximalIdeal 𝔹 = span {wittToBDeRhamPlus 𝒪 p ξ} :=
  GroundTheory.PAdicHodge.maximalIdeal_bDeRhamPlus_eq_span hξ (surjective_frobenius p) (isField_away p)

/- English proof (translation)
The claim follows from `GroundTheory.PAdicHodge.irreducible_wittToBDeRhamPlus hξ (mem_nonZeroDivisors_of_ker_eq_span hξ) (surjective_frobenius p) (isField_away p)`.
-/
theorem irreducible_wittToBDeRhamPlus {ξ : 𝕎𝒪♭} (hξ : RingHom.ker θ = span {ξ}) :
    Irreducible (wittToBDeRhamPlus 𝒪 p ξ) :=
  GroundTheory.PAdicHodge.irreducible_wittToBDeRhamPlus hξ (mem_nonZeroDivisors_of_ker_eq_span hξ)
    (surjective_frobenius p) (isField_away p)

/- English proof (translation)
Rewrite using `[maximalIdeal_bDeRhamPlus_eq_span (ker_fontaineTheta_eq_span_kerThetaGenerator K p)]`. Conclude with `isAdicComplete_bDeRhamPlus (ker_fontaineTheta_eq_span_kerThetaGenerator K p)`.
-/
theorem isAdicComplete_maximalIdeal_bDeRhamPlus : IsAdicComplete (maximalIdeal 𝔹) 𝔹 := by
  rw [maximalIdeal_bDeRhamPlus_eq_span (ker_fontaineTheta_eq_span_kerThetaGenerator K p)]
  exact isAdicComplete_bDeRhamPlus (ker_fontaineTheta_eq_span_kerThetaGenerator K p)

def residueFieldBDeRhamPlusEquiv : ResidueField 𝔹 ≃+* K :=
  (Ideal.quotEquivOfEq (maximalIdeal_bDeRhamPlus (K := K) (p := p))).trans
    (RingHom.quotientKerEquivOfSurjective (surjective_thetaBDeRhamPlusField (K := K) p))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem residueFieldBDeRhamPlusEquiv_residue (x : 𝔹) :
    residueFieldBDeRhamPlusEquiv (residue 𝔹 x) = thetaBDeRhamPlusField p x :=
  rfl

end IsPerfectoidField

end GroundTheory.PAdicHodge
