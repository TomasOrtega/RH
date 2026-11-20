import Mathlib

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace CrystallineSemistableComparison.Pb.EtaleIntegralityFacts

/- English proof (translation)
Use `⟨Polynomial.X * (Polynomial.X - Polynomial.C 1), Polynomial.monic_X.mul (Polynomial.monic_X_sub_C 1), ?_⟩` and prove the remaining obligations. Simplify using `[Polynomial.eval₂_mul, Polynomial.eval₂_sub, mul_sub, he]`.
-/
theorem isIntegral_of_mul_self_eq {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {e : S}
    (he : e * e = e) : IsIntegral R e := by
  refine ⟨Polynomial.X * (Polynomial.X - Polynomial.C 1),
    Polynomial.monic_X.mul (Polynomial.monic_X_sub_C 1), ?_⟩
  simp [Polynomial.eval₂_mul, Polynomial.eval₂_sub, mul_sub, he]

/- English proof (translation)
Take `⟨u, hu⟩` from `(TensorProduct.toIntegralClosure_bijective_of_smooth (R := P) (S := A) (B := FractionRing P)).2 ⟨t, ht⟩`. Establish `key : ∀ u : A ⊗[P] integralClosure P (FractionRing P), ∃ a : A, a ⊗ₜ[P] (1 : FractionRing P) = ((TensorProduct.toIntegralClosure P A (FractionRing P) u : _) : A ⊗[P] FractionRing P)`. Introduce `u`. Proceed by induction on `u with`. Consider the case `zero => exact ⟨0, by simp⟩`.

Consider the case `tmul a y`. Take `⟨p, hp⟩` from `IsIntegrallyClosed.isIntegral_iff.mp y.2`. Use `⟨p • a, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = a ⊗ₜ[P] (y : FractionRing P)`. Rewrite using `[TensorProduct.smul_tmul, ← hp, Algebra.algebraMap_eq_smul_one]`.

Consider the case `add x y hx hy`. Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`. Conclude with `⟨a + b, by rw [TensorProduct.add_tmul, ha, hb, map_add, Subalgebra.coe_add]⟩`. Take `⟨a, ha⟩` from `key u`.

Conclude with `⟨a, by rw [ha, hu]⟩`.
-/
theorem exists_tmul_one_eq_of_isIntegral {P A : Type} [CommRing P] [IsDomain P] [IsIntegrallyClosed P]
    [CommRing A] [Algebra P A] [Algebra.Smooth P A] (t : A ⊗[P] FractionRing P)
    (ht : IsIntegral A t) : ∃ a : A, a ⊗ₜ[P] (1 : FractionRing P) = t := by
  obtain ⟨u, hu⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth (R := P) (S := A)
    (B := FractionRing P)).2 ⟨t, ht⟩
  have key : ∀ u : A ⊗[P] integralClosure P (FractionRing P), ∃ a : A,
      a ⊗ₜ[P] (1 : FractionRing P) =
        ((TensorProduct.toIntegralClosure P A (FractionRing P) u : _) : A ⊗[P] FractionRing P) := by
    intro u
    induction u with
    | zero => exact ⟨0, by simp⟩
    | tmul a y =>
      obtain ⟨p, hp⟩ := IsIntegrallyClosed.isIntegral_iff.mp y.2
      refine ⟨p • a, ?_⟩
      change _ = a ⊗ₜ[P] (y : FractionRing P)
      rw [TensorProduct.smul_tmul, ← hp, Algebra.algebraMap_eq_smul_one]
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [TensorProduct.add_tmul, ha, hb, map_add, Subalgebra.coe_add]⟩
  obtain ⟨a, ha⟩ := key u
  exact ⟨a, by rw [ha, hu]⟩

/- English proof (translation)
Establish `hι : Function.Injective (fun a : A => a ⊗ₜ[P] (1 : FractionRing P))`. Establish `hinj : Function.Injective (Algebra.linearMap P (FractionRing P))` using `IsFractionRing.injective P (FractionRing P)`. Establish `h2` using `Module.Flat.lTensor_preserves_injective_linearMap (M := A) (Algebra.linearMap P (FractionRing P)) hinj`. Introduce `a b hab`. Apply `(TensorProduct.rid P A).symm.injective` to reduce the goal to its premises.

Apply `h2` to reduce the goal to its premises. Simplify using `using hab`. Take `⟨I, hI, Ai, hAi, hAlg, e, -⟩` from `(Algebra.FormallyEtale.iff_exists_algEquiv_prod (FractionRing P) (FractionRing P ⊗[P] A)).mp inferInstance`. Use `Fintype.ofFinite I` as an intermediate fact. Set `φ : A ⊗[P] FractionRing P ≃+* (Π i, Ai i)` to `(Algebra.TensorProduct.comm P A (FractionRing P)).toRingEquiv.trans e.toRingEquiv`.

Establish `hε : ∀ i, ∃ a : A, a ⊗ₜ[P] (1 : FractionRing P) = φ.symm (Pi.single i 1)`. Introduce `i`. Use `exists_tmul_one_eq_of_isIntegral _ (isIntegral_of_mul_self_eq ?_)` and prove the remaining obligations. Rewrite using `[← map_mul, ← Pi.single_mul, one_mul]`. Use `choose a ha using hε`.

Take `⟨i₀, hi₀⟩ : ∃ i, a i ∉ q` from `by by_contra! h`. Establish `hsum : (∑ i, a i) ∈ q` using `Ideal.sum_mem q fun i _ => h i`. Establish `h1 : (∑ i, a i) = 1`. Apply `hι` to reduce the goal to its premises. Simplify using `only`.

Rewrite using `[TensorProduct.sum_tmul, Finset.sum_congr rfl (fun i _ => ha i), ← map_sum, Finset.univ_sum_single]`. Conclude with `map_one φ.symm`. Conclude with `(Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one q).2 (h1 ▸ hsum))`. Use `⟨a i₀, hi₀, ?_⟩` and prove the remaining obligations. Set `F : A →+* Ai i₀` to `(Pi.evalRingHom Ai i₀).comp (φ.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom))`.

Establish `hF : ∀ x : A, F x = φ (x ⊗ₜ[P] (1 : FractionRing P)) i₀` using `fun x => rfl`. Establish `hFg : IsUnit (F (a i₀))`. Rewrite using `[hF, ha, RingEquiv.apply_symm_apply, Pi.single_eq_same]`. Conclude with `isUnit_one`. Set `ψ : Localization.Away (a i₀) →+* Ai i₀` to `IsLocalization.Away.lift (a i₀) hFg`.

Establish `hψ : Function.Injective ψ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨⟨y, s⟩, rfl⟩` from `IsLocalization.mk'_surjective (Submonoid.powers (a i₀)) x`. Establish `hspec` using `IsLocalization.mk'_spec (Localization.Away (a i₀)) y s`.

Establish `hFy : F y = 0`. Establish `h3` using `congrArg ψ hspec`. Rewrite `h3` using `[map_mul, hx, zero_mul]`. Establish `h4 : ψ (algebraMap A (Localization.Away (a i₀)) y) = F y` using `IsLocalization.lift_eq _ _`. Rewrite using `[← h4, ← h3]`.

Establish `hyg : y * a i₀ = 0`. Apply `hι` to reduce the goal to its premises. Simplify using `only`. Establish `hmul : (y * a i₀) ⊗ₜ[P] (1 : FractionRing P) = (y ⊗ₜ[P] (1 : FractionRing P)) * (a i₀ ⊗ₜ[P] (1 : FractionRing P))`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one]`.

Rewrite using `[hmul, zero_tmul]`. Apply `φ.injective` to reduce the goal to its premises. Rewrite using `[map_mul, ha, RingEquiv.apply_symm_apply, map_zero]`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = i₀`.

Substitute `hk` using the available equality. Simplify using `only [Pi.mul_apply, Pi.single_eq_same, mul_one, Pi.zero_apply]`. Conclude with `hFy`. Simplify using `[Pi.mul_apply, Pi.single_eq_of_ne hk]`. Establish `hy0 : algebraMap A (Localization.Away (a i₀)) y = 0`.

Establish `h5` using `congrArg (algebraMap A (Localization.Away (a i₀))) hyg`. Rewrite `h5` using `[map_mul, map_zero]`. Conclude with `(IsUnit.mul_left_eq_zero (IsLocalization.Away.algebraMap_isUnit (a i₀))).1 h5`. Rewrite `hy0` using `[← hspec]`. Conclude with `(IsUnit.mul_left_eq_zero (IsLocalization.map_units _ s)).1 hy0`.

Conclude with `hψ.isDomain ψ`.
-/
theorem exists_away_isDomain_of_etale {P A : Type} [CommRing P] [IsDomain P] [IsIntegrallyClosed P]
    [CommRing A] [Algebra P A] [Algebra.Etale P A] (q : Ideal A) [q.IsPrime] :
    ∃ g ∉ q, IsDomain (Localization.Away g) := by
  classical

  have hι : Function.Injective (fun a : A => a ⊗ₜ[P] (1 : FractionRing P)) := by
    have hinj : Function.Injective (Algebra.linearMap P (FractionRing P)) :=
      IsFractionRing.injective P (FractionRing P)
    have h2 := Module.Flat.lTensor_preserves_injective_linearMap (M := A)
      (Algebra.linearMap P (FractionRing P)) hinj
    intro a b hab
    apply (TensorProduct.rid P A).symm.injective
    apply h2
    simpa using hab

  obtain ⟨I, hI, Ai, hAi, hAlg, e, -⟩ :=
    (Algebra.FormallyEtale.iff_exists_algEquiv_prod (FractionRing P) (FractionRing P ⊗[P] A)).mp
      inferInstance
  have := Fintype.ofFinite I
  let φ : A ⊗[P] FractionRing P ≃+* (Π i, Ai i) :=
    (Algebra.TensorProduct.comm P A (FractionRing P)).toRingEquiv.trans e.toRingEquiv

  have hε : ∀ i, ∃ a : A, a ⊗ₜ[P] (1 : FractionRing P) = φ.symm (Pi.single i 1) := by
    intro i
    refine exists_tmul_one_eq_of_isIntegral _ (isIntegral_of_mul_self_eq ?_)
    rw [← map_mul, ← Pi.single_mul, one_mul]
  choose a ha using hε

  obtain ⟨i₀, hi₀⟩ : ∃ i, a i ∉ q := by
    by_contra! h
    have hsum : (∑ i, a i) ∈ q := Ideal.sum_mem q fun i _ => h i
    have h1 : (∑ i, a i) = 1 := by
      apply hι
      simp only
      rw [TensorProduct.sum_tmul, Finset.sum_congr rfl (fun i _ => ha i), ← map_sum,
        Finset.univ_sum_single]
      exact map_one φ.symm
    exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one q).2 (h1 ▸ hsum))
  refine ⟨a i₀, hi₀, ?_⟩

  let F : A →+* Ai i₀ := (Pi.evalRingHom Ai i₀).comp
    (φ.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom))
  have hF : ∀ x : A, F x = φ (x ⊗ₜ[P] (1 : FractionRing P)) i₀ := fun x => rfl
  have hFg : IsUnit (F (a i₀)) := by
    rw [hF, ha, RingEquiv.apply_symm_apply, Pi.single_eq_same]
    exact isUnit_one
  let ψ : Localization.Away (a i₀) →+* Ai i₀ := IsLocalization.Away.lift (a i₀) hFg
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (a i₀)) x
    have hspec := IsLocalization.mk'_spec (Localization.Away (a i₀)) y s
    have hFy : F y = 0 := by
      have h3 := congrArg ψ hspec
      rw [map_mul, hx, zero_mul] at h3
      have h4 : ψ (algebraMap A (Localization.Away (a i₀)) y) = F y := IsLocalization.lift_eq _ _
      rw [← h4, ← h3]
    have hyg : y * a i₀ = 0 := by
      apply hι
      simp only
      have hmul : (y * a i₀) ⊗ₜ[P] (1 : FractionRing P) =
          (y ⊗ₜ[P] (1 : FractionRing P)) * (a i₀ ⊗ₜ[P] (1 : FractionRing P)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      rw [hmul, zero_tmul]
      apply φ.injective
      rw [map_mul, ha, RingEquiv.apply_symm_apply, map_zero]
      funext k
      by_cases hk : k = i₀
      · subst hk
        simp only [Pi.mul_apply, Pi.single_eq_same, mul_one, Pi.zero_apply]
        exact hFy
      · simp [Pi.mul_apply, Pi.single_eq_of_ne hk]
    have hy0 : algebraMap A (Localization.Away (a i₀)) y = 0 := by
      have h5 := congrArg (algebraMap A (Localization.Away (a i₀))) hyg
      rw [map_mul, map_zero] at h5
      exact (IsUnit.mul_left_eq_zero (IsLocalization.Away.algebraMap_isUnit (a i₀))).1 h5
    rw [← hspec] at hy0
    exact (IsUnit.mul_left_eq_zero (IsLocalization.map_units _ s)).1 hy0
  exact hψ.isDomain ψ

end CrystallineSemistableComparison.Pb.EtaleIntegralityFacts
