import Mathlib
open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory

open Polynomial

/- English proof (translation)
Take `⟨n, y, hy⟩` from `IsArtinian.exists_pow_succ_smul_dvd a (1 : A)`. Simplify using `only [smul_eq_mul, mul_one] at hy`. Establish `hy' : a ^ (n + 1) * y = a ^ n` using `hy`. Use `⟨y, ?_⟩` and prove the remaining obligations. Establish `hc : IsNilpotent (a - a * a * y)` using `⟨n + 1, by`.

Combine the equalities or inequalities in the displayed calculation. Use `_ = a ^ (n + 1) * (1 - a * y) ^ (n + 1) := mul_pow _ _ _`. Use `_ = (a ^ (n + 1) - a * (a ^ (n + 1) * y)) * (1 - a * y) ^ n := by rw [pow_succ (1 - a * y)]; ring`. Use `_ = 0 := by rw [hy', ← pow_succ', sub_self, zero_mul]⟩`. Conclude with `(sub_eq_zero.mp hc.eq_zero).symm`.
-/
theorem exists_mul_mul_eq_self_of_isArtinian_isReduced {A : Type} [CommRing A] [IsArtinianRing A]
    [IsReduced A] (a : A) : ∃ y : A, a * a * y = a := by
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd a (1 : A)
  simp only [smul_eq_mul, mul_one] at hy
  have hy' : a ^ (n + 1) * y = a ^ n := hy
  refine ⟨y, ?_⟩
  have hc : IsNilpotent (a - a * a * y) := ⟨n + 1, by
    calc (a - a * a * y) ^ (n + 1) = (a * (1 - a * y)) ^ (n + 1) := by ring
    _ = a ^ (n + 1) * (1 - a * y) ^ (n + 1) := mul_pow _ _ _
    _ = (a ^ (n + 1) - a * (a ^ (n + 1) * y)) * (1 - a * y) ^ n := by rw [pow_succ (1 - a * y)]; ring
    _ = 0 := by rw [hy', ← pow_succ', sub_self, zero_mul]⟩
  exact (sub_eq_zero.mp hc.eq_zero).symm

/- English proof (translation)
Simplify using `only [aeval_eq_sum_range, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, mul_smul_comm, mul_pow, ← mul_assoc, ← pow_succ', hf.pow_succ_eq]`.
-/
theorem idempotent_mul_aeval_mul {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {f : A}
    (hf : IsIdempotentElem f) (x : A) (p : R[X]) : f * aeval (f * x) p = f * aeval x p := by
  simp only [aeval_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, mul_smul_comm, mul_pow, ← mul_assoc, ← pow_succ', hf.pow_succ_eq]

/- English proof (translation)
Assemble the required witnesses or components as `⟨X * (X - C 1), monic_X.mul (monic_X_sub_C 1), by simp only [eval₂_mul, eval₂_X, eval₂_sub, eval₂_C, eval₂_one, map_one, mul_sub, mul_one, he.eq, sub_self]⟩`.
-/
theorem isIntegral_of_isIdempotentElem {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {e : A}
    (he : IsIdempotentElem e) : IsIntegral R e :=
  ⟨X * (X - C 1), monic_X.mul (monic_X_sub_C 1), by
    simp only [eval₂_mul, eval₂_X, eval₂_sub, eval₂_C, eval₂_one, map_one, mul_sub, mul_one,
      he.eq, sub_self]⟩

/- English proof (translation)
Establish `hidem : ∀ e : A, IsIdempotentElem e → e ∈ integralClosure R A` using `fun e he => (show IsIntegral R e from isIntegral_of_isIdempotentElem he)`. Establish `hcompl : ∀ e : integralClosure R A, e ∈ Q → (1 - e) ∈ Q.primeCompl`. Introduce `e he h1`. Conclude with `(Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).mpr (by`. Simplify using `using Q.add_mem he h1))`.

Set `T : Submonoid A` to `Algebra.algebraMapSubmonoid A Q.primeCompl`. Set `J : Ideal A` to `RingHom.ker (algebraMap A (Localization T))`. Establish `memJ : ∀ a : A, a ∈ J ↔ ∃ s ∈ Q.primeCompl, (s : A) * a = 0`. Introduce `a`. Rewrite using `[RingHom.mem_ker, IsLocalization.map_eq_zero_iff T]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨m, hm⟩, hma⟩`. Take `⟨s, hs, rfl⟩` from `Submonoid.mem_map.mp hm`. Conclude with `⟨s, hs, hma⟩`. Introduce and unpack `⟨s, hs, hsa⟩`.

Conclude with `⟨⟨(s : A), Submonoid.mem_map.mpr ⟨s, hs, rfl⟩⟩, hsa⟩`. Establish `hS : ∀ s ∈ Q.primeCompl, (s : A) ∉ J`. Introduce `s hs h`. Take `⟨t, ht, hts⟩` from `(memJ _).mp h`. Establish `h0 : t * s = 0` using `Subtype.ext (by simpa using hts)`.

Conclude with `(Q.primeCompl.mul_mem ht hs) (h0 ▸ Q.zero_mem)`. Establish `hJprime : J.IsPrime`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `htop`. Conclude with `hS 1 Q.primeCompl.one_mem (by simp [htop])`.

Introduce `a c hac`. Take `⟨y, hy⟩` from `exists_mul_mul_eq_self_of_isArtinian_isReduced a`. Establish `hei : IsIdempotentElem (a * y)`. Unfold `IsIdempotentElem`. Combine the equalities or inequalities in the displayed calculation.

Use `_ = a * y := by rw [hy]`. Set `e : integralClosure R A` to `⟨a * y, hidem _ hei⟩`. Distinguish the cases in `he : e ∈ Q`. Use `left`. Use `(memJ a).mpr ⟨1 - e, hcompl e he, ?_⟩` and prove the remaining obligations.

Simplify using `only [e, Subalgebra.coe_sub, OneMemClass.coe_one]`. Take the linear combination `-hy`. Use `right`. Take `⟨s, hs, hsac⟩` from `(memJ _).mp hac`. Use `(memJ c).mpr ⟨s * e, Q.primeCompl.mul_mem hs he, ?_⟩` and prove the remaining obligations.

Simplify using `only [e, MulMemClass.coe_mul]`. Take the linear combination `y * hsac`. Use `haveI : J.IsPrime := hJprime`. Use `haveI hJm : J.IsMaximal := IsArtinianRing.isMaximal_of_isPrime J`. Use `letI : Field (A ⧸ J) := Ideal.Quotient.field J`.

Set `g : integralClosure R A →+* A ⧸ J` to `algebraMap (integralClosure R A) (A ⧸ J)`. Establish `g_eq : ∀ b, g b = Ideal.Quotient.mk J (b : A)` using `fun b => rfl`. Establish `hunit : ∀ s : Q.primeCompl, IsUnit (g s)`. Introduce `s`. Rewrite using `[isUnit_iff_ne_zero, g_eq, Ne, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `hS s.1 s.2`. Establish `hB0 : ∀ b : integralClosure R A, algebraMap (integralClosure R A) (Localization.AtPrime Q) b = 0 ↔ g b = 0`. Introduce `b`. Rewrite using `[IsLocalization.map_eq_zero_iff Q.primeCompl, g_eq, Ideal.Quotient.eq_zero_iff_mem, memJ]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨s, hs⟩, hsb⟩`. Conclude with `⟨s, hs, by simpa using congrArg Subtype.val hsb⟩`. Introduce and unpack `⟨s, hs, hsb⟩`. Conclude with `⟨⟨s, hs⟩, Subtype.ext (by simpa using hsb)⟩`. Set `ψ : Localization.AtPrime Q →+* A ⧸ J` to `IsLocalization.lift (M := Q.primeCompl) hunit`.

Establish `hinj : Function.Injective ψ`. Rewrite using `[IsLocalization.lift_injective_iff]`. Introduce `x y`. Rewrite using `[← sub_eq_zero, ← map_sub, hB0, map_sub, sub_eq_zero]`. Use `haveI hdom : IsDomain (Localization.AtPrime Q) := Function.Injective.isDomain ψ hinj`.

Use `⟨hdom, ?_⟩` and prove the remaining obligations. Use `letI : Algebra (Localization.AtPrime Q) (A ⧸ J) := ψ.toAlgebra`. Use `haveI : IsScalarTower (integralClosure R A) (Localization.AtPrime Q) (A ⧸ J) := IsScalarTower.of_algebraMap_eq fun b => (IsLocalization.lift_eq hunit b).symm`. Establish `hclosed : ∀ z : A ⧸ J, IsIntegral (Localization.AtPrime Q) z → ∃ w, ψ w = z`. Introduce `z hz`.

Take `⟨⟨s, hs⟩, hint⟩` from `IsIntegral.exists_multiple_integral_of_isLocalization Q.primeCompl z hz`. Establish `hint' : IsIntegral R ((⟨s, hs⟩ : Q.primeCompl) • z)` using `isIntegral_trans _ hint`. Take `⟨p, hpm, hp⟩` from `hint'`. Take `⟨a, ha⟩` from `Ideal.Quotient.mk_surjective ((⟨s, hs⟩ : Q.primeCompl) • z)`. Establish `hpa : aeval a p ∈ J`.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk R, ← aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk, ha]`. Conclude with `hp`. Take `⟨t, ht, htp⟩` from `(memJ _).mp hpa`. Take `⟨w, hw⟩` from `exists_mul_mul_eq_self_of_isArtinian_isReduced (t : A)`. Establish `hfi : IsIdempotentElem ((t : A) * w)`.

Unfold `IsIdempotentElem`. Combine the equalities or inequalities in the displayed calculation. Use `_ = (t : A) * w := by rw [hw]`. Set `f : integralClosure R A` to `⟨(t : A) * w, hidem _ hfi⟩`. Establish `hf : f ∈ Q.primeCompl`.

Introduce `hfQ`. Apply `hS t ht` to reduce the goal to its premises. Use `(memJ _).mpr ⟨1 - f, hcompl f hfQ, ?_⟩` and prove the remaining obligations. Simplify using `only [f, Subalgebra.coe_sub, OneMemClass.coe_one]`. Take the linear combination `-hw`.

Establish `hfp : (t : A) * w * aeval a p = 0` using `by linear_combination w * htp`. Establish `hfa : IsIntegral R ((t : A) * w * a)`. Use `⟨X * p, monic_X.mul hpm, ?_⟩` and prove the remaining obligations. Rewrite using `[← aeval_def, map_mul, aeval_X]`. Combine the equalities or inequalities in the displayed calculation.

Use `_ = 0 := by rw [idempotent_mul_aeval_mul hfi, hfp, mul_zero]`. Set `c : integralClosure R A` to `⟨(t : A) * w * a, (show IsIntegral R ((t : A) * w * a) from hfa)⟩`. Use `⟨IsLocalization.mk' (Localization.AtPrime Q) c (⟨s, hs⟩ : Q.primeCompl), ?_⟩` and prove the remaining obligations. Rewrite using `[IsLocalization.lift_mk'_spec]`. Establish `hf1 : g f = 1`.

Establish `hne : g f ≠ 0`. Rewrite using `[g_eq, Ne, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hS f hf`. Establish `hid : g f * g f = g f`. Rewrite using `[← map_mul]`.

Conclude with `congrArg g (Subtype.ext hfi.eq)`. Establish `: g f * (g f - 1) = 0` using `by rw [mul_sub, hid, mul_one, sub_self]`. Conclude with `sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hne)`. Establish `hsz : (⟨s, hs⟩ : Q.primeCompl) • z = g s * z`. Rewrite using `[Submonoid.smul_def, Algebra.smul_def]`.

Establish `hgc : g c = g f * Ideal.Quotient.mk J a`. Rewrite using `[g_eq, g_eq, ← map_mul]`. Rewrite using `[hgc, hf1, one_mul, ha, hsz]`. Rewrite using `[isIntegrallyClosed_iff (FractionRing (Localization.AtPrime Q))]`. Introduce `x hx`.

Establish `hinj' : Function.Injective (algebraMap (Localization.AtPrime Q) (A ⧸ J))` using `hinj`. Set `ι` to `IsFractionRing.liftAlgHom (R := Localization.AtPrime Q) (A := Localization.AtPrime Q) (K := FractionRing (Localization.AtPrime Q)) (L := A ⧸ J) (g := Algebra.ofId (Localization.AtPrime Q) (A ⧸ J)) hinj'`. Take `⟨w, hw⟩` from `hclosed (ι x) (hx.map ι)`. Use `⟨w, ι.toRingHom.injective ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ι (algebraMap _ _ w) = ι x`.

Rewrite using `[AlgHom.commutes]`. Conclude with `hw`.
-/
theorem localization_integralClosure_isDomain_isIntegrallyClosed
    (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [IsArtinianRing A] [IsReduced A]
    (Q : Ideal (integralClosure R A)) [Q.IsPrime] :
    IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  classical
  have hidem : ∀ e : A, IsIdempotentElem e → e ∈ integralClosure R A := fun e he =>
    (show IsIntegral R e from isIntegral_of_isIdempotentElem he)
  have hcompl : ∀ e : integralClosure R A, e ∈ Q → (1 - e) ∈ Q.primeCompl := by
    intro e he h1
    exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).mpr (by
      simpa using Q.add_mem he h1))
  let T : Submonoid A := Algebra.algebraMapSubmonoid A Q.primeCompl
  let J : Ideal A := RingHom.ker (algebraMap A (Localization T))
  have memJ : ∀ a : A, a ∈ J ↔ ∃ s ∈ Q.primeCompl, (s : A) * a = 0 := by
    intro a
    rw [RingHom.mem_ker, IsLocalization.map_eq_zero_iff T]
    constructor
    · rintro ⟨⟨m, hm⟩, hma⟩
      obtain ⟨s, hs, rfl⟩ := Submonoid.mem_map.mp hm
      exact ⟨s, hs, hma⟩
    · rintro ⟨s, hs, hsa⟩
      exact ⟨⟨(s : A), Submonoid.mem_map.mpr ⟨s, hs, rfl⟩⟩, hsa⟩
  have hS : ∀ s ∈ Q.primeCompl, (s : A) ∉ J := by
    intro s hs h
    obtain ⟨t, ht, hts⟩ := (memJ _).mp h
    have h0 : t * s = 0 := Subtype.ext (by simpa using hts)
    exact (Q.primeCompl.mul_mem ht hs) (h0 ▸ Q.zero_mem)
  have hJprime : J.IsPrime := by
    refine ⟨?_, ?_⟩
    · intro htop
      exact hS 1 Q.primeCompl.one_mem (by simp [htop])
    · intro a c hac
      obtain ⟨y, hy⟩ := exists_mul_mul_eq_self_of_isArtinian_isReduced a
      have hei : IsIdempotentElem (a * y) := by
        unfold IsIdempotentElem
        calc a * y * (a * y) = (a * a * y) * y := by ring
        _ = a * y := by rw [hy]
      let e : integralClosure R A := ⟨a * y, hidem _ hei⟩
      by_cases he : e ∈ Q
      · left
        refine (memJ a).mpr ⟨1 - e, hcompl e he, ?_⟩
        simp only [e, Subalgebra.coe_sub, OneMemClass.coe_one]
        linear_combination -hy
      · right
        obtain ⟨s, hs, hsac⟩ := (memJ _).mp hac
        refine (memJ c).mpr ⟨s * e, Q.primeCompl.mul_mem hs he, ?_⟩
        simp only [e, MulMemClass.coe_mul]
        linear_combination y * hsac
  haveI : J.IsPrime := hJprime
  haveI hJm : J.IsMaximal := IsArtinianRing.isMaximal_of_isPrime J
  letI : Field (A ⧸ J) := Ideal.Quotient.field J
  let g : integralClosure R A →+* A ⧸ J := algebraMap (integralClosure R A) (A ⧸ J)
  have g_eq : ∀ b, g b = Ideal.Quotient.mk J (b : A) := fun b => rfl
  have hunit : ∀ s : Q.primeCompl, IsUnit (g s) := by
    intro s
    rw [isUnit_iff_ne_zero, g_eq, Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hS s.1 s.2
  have hB0 : ∀ b : integralClosure R A,
      algebraMap (integralClosure R A) (Localization.AtPrime Q) b = 0 ↔ g b = 0 := by
    intro b
    rw [IsLocalization.map_eq_zero_iff Q.primeCompl, g_eq, Ideal.Quotient.eq_zero_iff_mem, memJ]
    constructor
    · rintro ⟨⟨s, hs⟩, hsb⟩
      exact ⟨s, hs, by simpa using congrArg Subtype.val hsb⟩
    · rintro ⟨s, hs, hsb⟩
      exact ⟨⟨s, hs⟩, Subtype.ext (by simpa using hsb)⟩
  let ψ : Localization.AtPrime Q →+* A ⧸ J := IsLocalization.lift (M := Q.primeCompl) hunit
  have hinj : Function.Injective ψ := by
    rw [IsLocalization.lift_injective_iff]
    intro x y
    rw [← sub_eq_zero, ← map_sub, hB0, map_sub, sub_eq_zero]
  haveI hdom : IsDomain (Localization.AtPrime Q) := Function.Injective.isDomain ψ hinj
  refine ⟨hdom, ?_⟩
  letI : Algebra (Localization.AtPrime Q) (A ⧸ J) := ψ.toAlgebra
  haveI : IsScalarTower (integralClosure R A) (Localization.AtPrime Q) (A ⧸ J) :=
    IsScalarTower.of_algebraMap_eq fun b => (IsLocalization.lift_eq hunit b).symm
  have hclosed : ∀ z : A ⧸ J, IsIntegral (Localization.AtPrime Q) z → ∃ w, ψ w = z := by
    intro z hz
    obtain ⟨⟨s, hs⟩, hint⟩ :=
      IsIntegral.exists_multiple_integral_of_isLocalization Q.primeCompl z hz
    have hint' : IsIntegral R ((⟨s, hs⟩ : Q.primeCompl) • z) := isIntegral_trans _ hint
    obtain ⟨p, hpm, hp⟩ := hint'
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((⟨s, hs⟩ : Q.primeCompl) • z)
    have hpa : aeval a p ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk R, ← aeval_algHom_apply,
        Ideal.Quotient.mkₐ_eq_mk, ha]
      exact hp
    obtain ⟨t, ht, htp⟩ := (memJ _).mp hpa
    obtain ⟨w, hw⟩ := exists_mul_mul_eq_self_of_isArtinian_isReduced (t : A)
    have hfi : IsIdempotentElem ((t : A) * w) := by
      unfold IsIdempotentElem
      calc (t : A) * w * ((t : A) * w) = ((t : A) * t * w) * w := by ring
      _ = (t : A) * w := by rw [hw]
    let f : integralClosure R A := ⟨(t : A) * w, hidem _ hfi⟩
    have hf : f ∈ Q.primeCompl := by
      intro hfQ
      apply hS t ht
      refine (memJ _).mpr ⟨1 - f, hcompl f hfQ, ?_⟩
      simp only [f, Subalgebra.coe_sub, OneMemClass.coe_one]
      linear_combination -hw
    have hfp : (t : A) * w * aeval a p = 0 := by linear_combination w * htp
    have hfa : IsIntegral R ((t : A) * w * a) := by
      refine ⟨X * p, monic_X.mul hpm, ?_⟩
      rw [← aeval_def, map_mul, aeval_X]
      calc (t : A) * w * a * aeval ((t : A) * w * a) p
          = a * ((t : A) * w * aeval ((t : A) * w * a) p) := by ring
      _ = 0 := by rw [idempotent_mul_aeval_mul hfi, hfp, mul_zero]
    let c : integralClosure R A := ⟨(t : A) * w * a, (show IsIntegral R ((t : A) * w * a) from hfa)⟩
    refine ⟨IsLocalization.mk' (Localization.AtPrime Q) c (⟨s, hs⟩ : Q.primeCompl), ?_⟩
    rw [IsLocalization.lift_mk'_spec]
    have hf1 : g f = 1 := by
      have hne : g f ≠ 0 := by
        rw [g_eq, Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hS f hf
      have hid : g f * g f = g f := by
        rw [← map_mul]; exact congrArg g (Subtype.ext hfi.eq)
      have : g f * (g f - 1) = 0 := by rw [mul_sub, hid, mul_one, sub_self]
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hne)
    have hsz : (⟨s, hs⟩ : Q.primeCompl) • z = g s * z := by
      rw [Submonoid.smul_def, Algebra.smul_def]
    have hgc : g c = g f * Ideal.Quotient.mk J a := by
      rw [g_eq, g_eq, ← map_mul]
    rw [hgc, hf1, one_mul, ha, hsz]
  rw [isIntegrallyClosed_iff (FractionRing (Localization.AtPrime Q))]
  intro x hx
  have hinj' : Function.Injective (algebraMap (Localization.AtPrime Q) (A ⧸ J)) := hinj
  let ι := IsFractionRing.liftAlgHom (R := Localization.AtPrime Q) (A := Localization.AtPrime Q)
    (K := FractionRing (Localization.AtPrime Q)) (L := A ⧸ J)
    (g := Algebra.ofId (Localization.AtPrime Q) (A ⧸ J)) hinj'
  obtain ⟨w, hw⟩ := hclosed (ι x) (hx.map ι)
  refine ⟨w, ι.toRingHom.injective ?_⟩
  change ι (algebraMap _ _ w) = ι x
  rw [AlgHom.commutes]
  exact hw

end GlobalTheory
