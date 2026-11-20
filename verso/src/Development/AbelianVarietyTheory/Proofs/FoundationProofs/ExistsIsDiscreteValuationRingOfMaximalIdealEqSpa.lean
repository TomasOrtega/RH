import Mathlib

namespace GlobalTheory

open Polynomial IsLocalRing
open scoped TensorProduct

section Lift

variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]

/- English proof (translation)
Take `⟨c, hc⟩` from `hb.exists_right_inv`. Take `⟨a, rfl⟩` from `hπ c`. Establish `h : b * a - 1 ∈ RingHom.ker π` using `by simp [RingHom.mem_ker, hc]`. Use `Ideal.mem_jacobson_bot.mp (hj h) 1` as an intermediate fact. Rewrite `this` using `[mul_one, sub_add_cancel]`.

Conclude with `isUnit_of_mul_isUnit_left this`.
-/
theorem isUnit_of_isUnit_map_of_ker_le_jacobson (π : B →+* C) (hπ : Function.Surjective π)
    (hj : RingHom.ker π ≤ Ideal.jacobson ⊥) {b : B} (hb : IsUnit (π b)) : IsUnit b := by
  obtain ⟨c, hc⟩ := hb.exists_right_inv
  obtain ⟨a, rfl⟩ := hπ c
  have h : b * a - 1 ∈ RingHom.ker π := by simp [RingHom.mem_ker, hc]
  have := Ideal.mem_jacobson_bot.mp (hj h) 1
  rw [mul_one, sub_add_cancel] at this
  exact isUnit_of_mul_isUnit_left this

/- English proof (translation)
The claim follows from `isUnit_of_isUnit_map_of_ker_le_jacobson π hπ (fun x hx => HenselianRing.jac (I := I) ((hI x).mpr hx)) hb`.
-/
theorem isUnit_of_isUnit_map_of_henselian (I : Ideal B) [HenselianRing B I] (π : B →+* C)
    (hπ : Function.Surjective π) (hI : ∀ b, b ∈ I ↔ π b = 0) {b : B} (hb : IsUnit (π b)) :
    IsUnit b :=
  isUnit_of_isUnit_map_of_ker_le_jacobson π hπ
    (fun x hx => HenselianRing.jac (I := I) ((hI x).mpr hx)) hb

/- English proof (translation)
Establish `: Nontrivial C`. Assume the negation of the conclusion as `hC`. Rewrite `hC` using `[not_nontrivial_iff_subsingleton]`. Conclude with `not_isUnit_zero (isUnit_of_isUnit_map_of_henselian I π hπ hI (b := 0) (isUnit_of_subsingleton _))`. Conclude with `IsLocalRing.of_surjective' π hπ`.
-/
theorem isLocalRing_of_surjective_of_henselian [IsLocalRing B] (I : Ideal B) [HenselianRing B I]
    (π : B →+* C) (hπ : Function.Surjective π) (hI : ∀ b, b ∈ I ↔ π b = 0) : IsLocalRing C := by
  have : Nontrivial C := by
    by_contra hC
    rw [not_nontrivial_iff_subsingleton] at hC
    exact not_isUnit_zero (isUnit_of_isUnit_map_of_henselian I π hπ hI (b := 0)
      (isUnit_of_subsingleton _))
  exact IsLocalRing.of_surjective' π hπ

/- English proof (translation)
Take `⟨P⟩ : Nonempty (StandardEtalePresentation R A)` from `inferInstance`. Establish `h₀ : P.P.HasMap (φ P.x)` using `P.hasMap.map φ`. Take `⟨t₀, ht₀⟩` from `hπ (φ P.x)`. Establish `hu : ∀ b, IsUnit (π b) → IsUnit b` using `fun b hb => isUnit_of_isUnit_map_of_henselian I (π : B →+* C) hπ hI hb`. Take `⟨t, ht, htt⟩` from `HenselianRing.is_henselian (I := I) (P.f.map (algebraMap R B)) (P.monic_f.map _) t₀ (by rw [hI, eval_map_algebraMap, ← aeval_algHom_apply, ht₀]; exact h₀.1) (by`.

Use `IsUnit.map _ (hu _ ?_)` and prove the remaining obligations. Rewrite using `[derivative_map, eval_map_algebraMap, ← aeval_algHom_apply, ht₀]`. Conclude with `h₀.isUnit_derivative_f)`. Establish `hπt : π t = φ P.x`. Rewrite `htt` using `[hI, map_sub, sub_eq_zero]`.

Rewrite using `[htt, ht₀]`. Establish `h₁ : P.P.HasMap t` using `⟨by rwa [IsRoot.def, eval_map_algebraMap] at ht, hu _ (by rw [← aeval_algHom_apply, hπt]; exact h₀.2)⟩`. Conclude with `⟨(P.P.lift t h₁).comp P.equivRing.toAlgHom, P.hom_ext (by simp [hπt])⟩`.
-/
theorem exists_algHom_lift_of_isStandardEtale [Algebra.IsStandardEtale R A] (I : Ideal B)
    [HenselianRing B I] (π : B →ₐ[R] C) (hπ : Function.Surjective π) (hI : ∀ b, b ∈ I ↔ π b = 0)
    (φ : A →ₐ[R] C) : ∃ ψ : A →ₐ[R] B, π.comp ψ = φ := by
  obtain ⟨P⟩ : Nonempty (StandardEtalePresentation R A) := inferInstance
  have h₀ : P.P.HasMap (φ P.x) := P.hasMap.map φ
  obtain ⟨t₀, ht₀⟩ := hπ (φ P.x)
  have hu : ∀ b, IsUnit (π b) → IsUnit b := fun b hb =>
    isUnit_of_isUnit_map_of_henselian I (π : B →+* C) hπ hI hb
  obtain ⟨t, ht, htt⟩ := HenselianRing.is_henselian (I := I)
    (P.f.map (algebraMap R B)) (P.monic_f.map _) t₀
    (by rw [hI, eval_map_algebraMap, ← aeval_algHom_apply, ht₀]; exact h₀.1)
    (by
      refine IsUnit.map _ (hu _ ?_)
      rw [derivative_map, eval_map_algebraMap, ← aeval_algHom_apply, ht₀]
      exact h₀.isUnit_derivative_f)
  have hπt : π t = φ P.x := by
    rw [hI, map_sub, sub_eq_zero] at htt
    rw [htt, ht₀]
  have h₁ : P.P.HasMap t :=
    ⟨by rwa [IsRoot.def, eval_map_algebraMap] at ht,
      hu _ (by rw [← aeval_algHom_apply, hπt]; exact h₀.2)⟩
  exact ⟨(P.P.lift t h₁).comp P.equivRing.toAlgHom, P.hom_ext (by simp [hπt])⟩

/- English proof (translation)
Establish `: IsLocalRing C` using `isLocalRing_of_surjective_of_henselian I (π : B →+* C) hπ hI`. Take `⟨f, hf, n, _, _, _⟩` from `Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := (maximalIdeal C).comap φ)`. Establish `hφf : IsUnit (φ f)` using `by simpa using hf`. Set `φ' : Localization.Away f →ₐ[R] C` to `IsLocalization.Away.liftAlgHom f hφf`. Use `choose b hb using fun i : Fin n => hπ (φ' (algebraMap _ _ (MvPolynomial.X (R := R) i)))`.

Set `χ : MvPolynomial (Fin n) R →ₐ[R] C` to `φ'.comp (IsScalarTower.toAlgHom R _ _)`. Establish `hχ : π.comp (MvPolynomial.aeval b) = χ` using `by ext i; simp [χ, hb]`. Use `letI := (MvPolynomial.aeval (R := R) b).toAlgebra`. Use `letI := χ.toAlgebra`. Establish `: IsScalarTower R (MvPolynomial (Fin n) R) B` using `.of_algebraMap_eq fun r => ((MvPolynomial.aeval (R := R) b).commutes r).symm`.

Set `π' : B →ₐ[MvPolynomial (Fin n) R] C` to `⟨π, fun r => congr($hχ r)⟩`. Set `φ'' : Localization.Away f →ₐ[MvPolynomial (Fin n) R] C` to `⟨φ', fun r => rfl⟩`. Take `⟨ψ, hψ⟩` from `exists_algHom_lift_of_isStandardEtale I π' hπ hI φ''`. Use `⟨(ψ.restrictScalars R).comp (IsScalarTower.toAlgHom R A _), AlgHom.ext fun a => ?_⟩` and prove the remaining obligations. Conclude with `congr($hψ (algebraMap A _ a)).trans (show φ' (algebraMap A _ a) = φ a by simp [φ'])`.
-/
theorem exists_algHom_lift_of_smooth [Algebra.Smooth R A] [IsLocalRing B] (I : Ideal B)
    [HenselianRing B I] (π : B →ₐ[R] C) (hπ : Function.Surjective π) (hI : ∀ b, b ∈ I ↔ π b = 0)
    (φ : A →ₐ[R] C) : ∃ ψ : A →ₐ[R] B, π.comp ψ = φ := by
  have : IsLocalRing C := isLocalRing_of_surjective_of_henselian I (π : B →+* C) hπ hI
  obtain ⟨f, hf, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R)
    (p := (maximalIdeal C).comap φ)
  have hφf : IsUnit (φ f) := by simpa using hf
  let φ' : Localization.Away f →ₐ[R] C := IsLocalization.Away.liftAlgHom f hφf
  choose b hb using fun i : Fin n => hπ (φ' (algebraMap _ _ (MvPolynomial.X (R := R) i)))
  let χ : MvPolynomial (Fin n) R →ₐ[R] C := φ'.comp (IsScalarTower.toAlgHom R _ _)
  have hχ : π.comp (MvPolynomial.aeval b) = χ := by ext i; simp [χ, hb]
  letI := (MvPolynomial.aeval (R := R) b).toAlgebra
  letI := χ.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin n) R) B :=
    .of_algebraMap_eq fun r => ((MvPolynomial.aeval (R := R) b).commutes r).symm
  let π' : B →ₐ[MvPolynomial (Fin n) R] C := ⟨π, fun r => congr($hχ r)⟩
  let φ'' : Localization.Away f →ₐ[MvPolynomial (Fin n) R] C := ⟨φ', fun r => rfl⟩
  obtain ⟨ψ, hψ⟩ := exists_algHom_lift_of_isStandardEtale I π' hπ hI φ''
  refine ⟨(ψ.restrictScalars R).comp (IsScalarTower.toAlgHom R A _), AlgHom.ext fun a => ?_⟩
  exact congr($hψ (algebraMap A _ a)).trans (show φ' (algebraMap A _ a) = φ a by simp [φ'])

/- English proof (translation)
Establish `key : ∀ n : ℕ, ∃ a, a - a₀ ∈ maximalIdeal B ∧ f.eval a₀ ^ 2 ^ n ∣ f.eval a ∧ IsUnit (f.derivative.eval a)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => exact ⟨a₀, by simp, by simp, h₁⟩`. Consider the case `succ n ih`.

Take `⟨a, ha, hd, u, hu⟩` from `ih`. Establish `hm : f.eval a ∈ maximalIdeal B` using `Ideal.mem_of_dvd _ hd (Ideal.pow_mem_of_mem _ h₀ _ (by positivity))`. Establish `hy : -(↑u⁻¹ * f.eval a) ∈ maximalIdeal B` using `neg_mem (Ideal.mul_mem_left _ _ hm)`. Use `⟨a + -(↑u⁻¹ * f.eval a), ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[add_sub_right_comm]`.

Conclude with `add_mem ha hy`. Take `⟨c, hc⟩` from `f.binomExpansion a (-(↑u⁻¹ * f.eval a))`. Rewrite using `[hc, ← hu, mul_neg, Units.mul_inv_cancel_left, add_neg_cancel, zero_add, pow_succ, pow_mul, neg_sq, mul_pow]`. Conclude with `((pow_dvd_pow_of_dvd hd 2).mul_left _).mul_left _`. Take `⟨c, hc⟩` from `f.derivative.evalSubFactor (a + -(↑u⁻¹ * f.eval a)) a`.

Assume the negation of the conclusion as `hn`. Establish `h₂` using `sub_mem ((mem_maximalIdeal _).mpr hn) (Ideal.mul_mem_left (maximalIdeal B) c hy)`. Rewrite `hc` using `[add_sub_cancel_left]`. Rewrite `h₂` using `[← hc, sub_sub_cancel, ← hu]`. Conclude with `(mem_maximalIdeal _).mp h₂ u.isUnit`.

Take `⟨n, hn⟩` from `hI h₀`. Take `⟨a, ha, hd, hu⟩` from `key n`. Take `⟨b, hb, hba⟩` from `HenselianRing.is_henselian (I := I) f hf a (Ideal.mem_of_dvd _ hd (Ideal.pow_mem_of_pow_mem _ hn Nat.lt_two_pow_self.le)) (hu.map _)`. Use `⟨b, hb, ?_⟩` and prove the remaining obligations. Establish `hle : I ≤ maximalIdeal B` using `(HenselianRing.jac (I := I)).trans (jacobson_eq_maximalIdeal ⊥ bot_ne_top).le`.

Simplify using `using add_mem (hle hba) ha`.
-/
theorem henselianLocalRing_of_le_radical [IsLocalRing B] (I : Ideal B) [HenselianRing B I]
    (hI : maximalIdeal B ≤ I.radical) : HenselianLocalRing B where
  is_henselian f hf a₀ h₀ h₁ := by
    have key : ∀ n : ℕ, ∃ a, a - a₀ ∈ maximalIdeal B ∧ f.eval a₀ ^ 2 ^ n ∣ f.eval a ∧
        IsUnit (f.derivative.eval a) := by
      intro n
      induction n with
      | zero => exact ⟨a₀, by simp, by simp, h₁⟩
      | succ n ih =>
        obtain ⟨a, ha, hd, u, hu⟩ := ih
        have hm : f.eval a ∈ maximalIdeal B :=
          Ideal.mem_of_dvd _ hd (Ideal.pow_mem_of_mem _ h₀ _ (by positivity))
        have hy : -(↑u⁻¹ * f.eval a) ∈ maximalIdeal B := neg_mem (Ideal.mul_mem_left _ _ hm)
        refine ⟨a + -(↑u⁻¹ * f.eval a), ?_, ?_, ?_⟩
        · rw [add_sub_right_comm]
          exact add_mem ha hy
        · obtain ⟨c, hc⟩ := f.binomExpansion a (-(↑u⁻¹ * f.eval a))
          rw [hc, ← hu, mul_neg, Units.mul_inv_cancel_left, add_neg_cancel, zero_add, pow_succ,
            pow_mul, neg_sq, mul_pow]
          exact ((pow_dvd_pow_of_dvd hd 2).mul_left _).mul_left _
        · obtain ⟨c, hc⟩ := f.derivative.evalSubFactor (a + -(↑u⁻¹ * f.eval a)) a
          by_contra hn
          have h₂ := sub_mem ((mem_maximalIdeal _).mpr hn)
            (Ideal.mul_mem_left (maximalIdeal B) c hy)
          rw [add_sub_cancel_left] at hc
          rw [← hc, sub_sub_cancel, ← hu] at h₂
          exact (mem_maximalIdeal _).mp h₂ u.isUnit
    obtain ⟨n, hn⟩ := hI h₀
    obtain ⟨a, ha, hd, hu⟩ := key n
    obtain ⟨b, hb, hba⟩ := HenselianRing.is_henselian (I := I) f hf a
      (Ideal.mem_of_dvd _ hd (Ideal.pow_mem_of_pow_mem _ hn Nat.lt_two_pow_self.le)) (hu.map _)
    refine ⟨b, hb, ?_⟩
    have hle : I ≤ maximalIdeal B :=
      (HenselianRing.jac (I := I)).trans (jacobson_eq_maximalIdeal ⊥ bot_ne_top).le
    simpa using add_mem (hle hba) ha

end Lift

section SeparablePoints

variable {R A B K : Type*} [CommRing R] [CommRing A] [CommRing B] [Field K]
  [Algebra R A] [Algebra R B] [Algebra R K]

/- English proof (translation)
Set `p` to `RingHom.ker (algebraMap R K)`. Establish `: p.IsPrime` using `RingHom.ker_isPrime _`. Establish `: q.LiesOver p` using `⟨hq.symm⟩`. Use `letI := Localization.AtPrime.algebraOfLiesOver p q`. Set `ι : p.ResidueField →ₐ[R] K` to `Ideal.ResidueField.liftₐ p (Algebra.ofId R K) le_rfl (by`.

Simplify using `[SetLike.le_def, IsUnit.mem_submonoid_iff, p])`. Use `letI := ι.toAlgebra`. Establish `: IsScalarTower R p.ResidueField K` using `.of_algebraMap_eq fun r => (ι.commutes r).symm`. Set `j : q.ResidueField →ₐ[p.ResidueField] K` to `IsSepClosed.lift`. Conclude with `⟨(j.restrictScalars R).comp (IsScalarTower.toAlgHom R A _)⟩`.
-/
theorem nonempty_algHom_of_etale_of_isSepClosed [IsSepClosed K] [Algebra.Etale R A] (q : Ideal A)
    [q.IsPrime] (hq : q.comap (algebraMap R A) = RingHom.ker (algebraMap R K)) :
    Nonempty (A →ₐ[R] K) := by
  let p := RingHom.ker (algebraMap R K)
  have : p.IsPrime := RingHom.ker_isPrime _
  have : q.LiesOver p := ⟨hq.symm⟩
  letI := Localization.AtPrime.algebraOfLiesOver p q
  let ι : p.ResidueField →ₐ[R] K := Ideal.ResidueField.liftₐ p (Algebra.ofId R K) le_rfl (by
    simp [SetLike.le_def, IsUnit.mem_submonoid_iff, p])
  letI := ι.toAlgebra
  have : IsScalarTower R p.ResidueField K := .of_algebraMap_eq fun r => (ι.commutes r).symm
  let j : q.ResidueField →ₐ[p.ResidueField] K := IsSepClosed.lift
  exact ⟨(j.restrictScalars R).comp (IsScalarTower.toAlgHom R A _)⟩

/- English proof (translation)
Establish `: Infinite K`. Assume the negation of the conclusion as `hK`. Rewrite `hK` using `[not_infinite_iff_finite]`. Use `IsSepClosed.isAlgClosed_of_perfectField K` as an intermediate fact. Conclude with `not_finite K`.

Take `⟨f, hf, n, _, _, _⟩` from `Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := p)`. Set `S` to `Localization.Away f`. Set `P` to `MvPolynomial (Fin n) R`. Establish `hdisj` using `(Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hf`. Set `p' : PrimeSpectrum S` to `⟨p.map (algebraMap A S), IsLocalization.isPrime_of_isPrime_disjoint (.powers f) _ _ ‹_› hdisj⟩`.

Establish `hp' : p'.asIdeal.comap (algebraMap R S) = RingHom.ker (algebraMap R K)`. Rewrite using `[IsScalarTower.algebraMap_eq R A S, ← Ideal.comap_comap, ← hp]`. Conclude with `congrArg _ (IsLocalization.comap_map_of_isPrime_disjoint (.powers f) _ ‹_› hdisj)`. Establish `hopen` using `(PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation (R := P) (S := S)).isOpen_range`. Take `⟨_, ⟨_, ⟨h, rfl⟩, rfl⟩, hh, hsub⟩` from `PrimeSpectrum.isBasis_basic_opens |>.exists_subset_of_mem_open (Set.mem_range_self p') hopen`.

Choose the witnesses or unpack the hypotheses as in `⟨b, hb⟩ : ∃ b : Fin n → K, MvPolynomial.aeval b h ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Establish `h₀ : h.map (algebraMap R K) = 0` using `MvPolynomial.funext fun b => by rw [MvPolynomial.eval_map, ← MvPolynomial.aeval_def, hc, map_zero]`. Apply `hh` to reduce the goal to its premises.

Rewrite using `[h.as_sum]`. Use `Ideal.sum_mem _ fun m _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.monomial_eq]`. Use `Ideal.mul_mem_right _ _ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap P S (algebraMap R P _) ∈ p'.asIdeal`.

Rewrite using `[← IsScalarTower.algebraMap_apply, ← Ideal.mem_comap, hp', RingHom.mem_ker, ← MvPolynomial.coeff_map, h₀, MvPolynomial.coeff_zero]`. Use `letI := (MvPolynomial.aeval (R := R) b).toAlgebra`. Establish `: IsScalarTower R P K` using `.of_algebraMap_eq fun r => ((MvPolynomial.aeval (R := R) b).commutes r).symm`. Take `⟨q, hq⟩` from `hsub (a := ⟨RingHom.ker (algebraMap P K), RingHom.ker_isPrime _⟩) hb`. Take `⟨ψ⟩` from `nonempty_algHom_of_etale_of_isSepClosed (R := P) (K := K) q.asIdeal congr($(hq).asIdeal)`.

Conclude with `⟨(ψ.restrictScalars R).comp (IsScalarTower.toAlgHom R A _)⟩`.
-/
theorem nonempty_algHom_of_smooth_of_isSepClosed [IsSepClosed K] [Algebra.Smooth R A] (p : Ideal A)
    [p.IsPrime] (hp : p.comap (algebraMap R A) = RingHom.ker (algebraMap R K)) :
    Nonempty (A →ₐ[R] K) := by
  have : Infinite K := by
    by_contra hK
    rw [not_infinite_iff_finite] at hK
    have := IsSepClosed.isAlgClosed_of_perfectField K
    exact not_finite K
  obtain ⟨f, hf, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R)
    (p := p)
  let S := Localization.Away f
  let P := MvPolynomial (Fin n) R
  have hdisj := (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hf
  let p' : PrimeSpectrum S := ⟨p.map (algebraMap A S),
    IsLocalization.isPrime_of_isPrime_disjoint (.powers f) _ _ ‹_› hdisj⟩
  have hp' : p'.asIdeal.comap (algebraMap R S) = RingHom.ker (algebraMap R K) := by
    rw [IsScalarTower.algebraMap_eq R A S, ← Ideal.comap_comap, ← hp]
    exact congrArg _ (IsLocalization.comap_map_of_isPrime_disjoint (.powers f) _ ‹_› hdisj)
  have hopen := (PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
    (R := P) (S := S)).isOpen_range
  obtain ⟨_, ⟨_, ⟨h, rfl⟩, rfl⟩, hh, hsub⟩ := PrimeSpectrum.isBasis_basic_opens
    |>.exists_subset_of_mem_open (Set.mem_range_self p') hopen
  obtain ⟨b, hb⟩ : ∃ b : Fin n → K, MvPolynomial.aeval b h ≠ 0 := by
    by_contra hc
    push Not at hc
    have h₀ : h.map (algebraMap R K) = 0 :=
      MvPolynomial.funext fun b => by rw [MvPolynomial.eval_map, ← MvPolynomial.aeval_def, hc, map_zero]
    apply hh
    rw [h.as_sum]
    refine Ideal.sum_mem _ fun m _ => ?_
    rw [MvPolynomial.monomial_eq]
    refine Ideal.mul_mem_right _ _ ?_
    change algebraMap P S (algebraMap R P _) ∈ p'.asIdeal
    rw [← IsScalarTower.algebraMap_apply, ← Ideal.mem_comap, hp', RingHom.mem_ker,
      ← MvPolynomial.coeff_map, h₀, MvPolynomial.coeff_zero]
  letI := (MvPolynomial.aeval (R := R) b).toAlgebra
  have : IsScalarTower R P K :=
    .of_algebraMap_eq fun r => ((MvPolynomial.aeval (R := R) b).commutes r).symm
  obtain ⟨q, hq⟩ := hsub (a := ⟨RingHom.ker (algebraMap P K), RingHom.ker_isPrime _⟩) hb
  obtain ⟨ψ⟩ := nonempty_algHom_of_etale_of_isSepClosed (R := P) (K := K) q.asIdeal
    congr($(hq).asIdeal)
  exact ⟨(ψ.restrictScalars R).comp (IsScalarTower.toAlgHom R A _)⟩

/- English proof (translation)
Set `k` to `ResidueField B`. Set `L` to `IntermediateField.adjoin k (Set.range b)`. Establish `: FiniteDimensional k L` using `IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x`. Take `⟨θ, hθ⟩` from `Field.exists_primitive_element k L`. Establish `hi : IsIntegral k θ` using `Algebra.IsIntegral.isIntegral θ`.

Take `⟨μ, hμ, -, hμm⟩` from `lifts_and_natDegree_eq_and_monic (f := algebraMap B k) (p := minpoly k θ) (map_surjective _ residue_surjective _) (minpoly.monic hi)`. Set `P : StandardEtalePair B` to `⟨μ, hμm, derivative μ, 1, 0, 1, by simp⟩`. Establish `key : ∀ g : B[X], aeval (θ : K) g = (aeval θ (g.map (algebraMap B k)) : L)` using `fun g => by`. Rewrite using `[← aeval_map_algebraMap k]`. Conclude with `aeval_algHom_apply L.val θ _`.

Establish `hP : P.HasMap (θ : K)`. Use `⟨by rw [key, hμ, minpoly.aeval]; rfl, Ne.isUnit ?_⟩` and prove the remaining obligations. Rewrite using `[key, ← derivative_map, hμ]`. Conclude with `fun h => (Algebra.IsSeparable.isSeparable k θ).aeval_derivative_ne_zero (minpoly.aeval k θ) (Subtype.ext h)`. Use `⟨P, P.lift _ hP, fun i => ?_⟩` and prove the remaining obligations.

Establish `h₁ : (⟨b i, IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩ : L) ∈ Algebra.adjoin k {θ}`. Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hi.isAlgebraic, hθ]`. Discharge the goal by the elementary cases of `trivial`. Rewrite `h₁` using `[Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨g, hg⟩` from `h₁`.

Take `⟨g, rfl⟩` from `map_surjective (algebraMap B k) residue_surjective g`. Use `⟨aeval P.X g, ?_⟩` and prove the remaining obligations. Rewrite using `[← aeval_algHom_apply, StandardEtalePair.lift_X, key]`. Conclude with `congrArg Subtype.val hg`.
-/
theorem exists_etale_subset_range [IsLocalRing B] [Algebra B K] [Algebra (ResidueField B) K]
    [IsScalarTower B (ResidueField B) K] [Algebra.IsSeparable (ResidueField B) K]
    {ι : Type*} [Finite ι] (b : ι → K) :
    ∃ (P : StandardEtalePair B) (ε : P.Ring →ₐ[B] K), ∀ i, b i ∈ Set.range ε := by
  let k := ResidueField B
  let L := IntermediateField.adjoin k (Set.range b)
  have : FiniteDimensional k L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element k L
  have hi : IsIntegral k θ := Algebra.IsIntegral.isIntegral θ
  obtain ⟨μ, hμ, -, hμm⟩ := lifts_and_natDegree_eq_and_monic (f := algebraMap B k)
    (p := minpoly k θ) (map_surjective _ residue_surjective _) (minpoly.monic hi)
  let P : StandardEtalePair B := ⟨μ, hμm, derivative μ, 1, 0, 1, by simp⟩
  have key : ∀ g : B[X], aeval (θ : K) g = (aeval θ (g.map (algebraMap B k)) : L) := fun g => by
    rw [← aeval_map_algebraMap k]
    exact aeval_algHom_apply L.val θ _
  have hP : P.HasMap (θ : K) := by
    refine ⟨by rw [key, hμ, minpoly.aeval]; rfl, Ne.isUnit ?_⟩
    rw [key, ← derivative_map, hμ]
    exact fun h => (Algebra.IsSeparable.isSeparable k θ).aeval_derivative_ne_zero
      (minpoly.aeval k θ) (Subtype.ext h)
  refine ⟨P, P.lift _ hP, fun i => ?_⟩
  have h₁ : (⟨b i, IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩ : L) ∈ Algebra.adjoin k {θ} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hi.isAlgebraic, hθ]
    trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at h₁
  obtain ⟨g, hg⟩ := h₁
  obtain ⟨g, rfl⟩ := map_surjective (algebraMap B k) residue_surjective g
  refine ⟨aeval P.X g, ?_⟩
  rw [← aeval_algHom_apply, StandardEtalePair.lift_X, key]
  exact congrArg Subtype.val hg

end SeparablePoints

section QuasiSection

universe u

variable {R : Type*} {A B : Type u} {K : Type*} [CommRing R] [CommRing A] [CommRing B] [Field K]
  [Algebra R A] [Algebra R B] [Algebra R K] [IsLocalRing B] [Algebra B K] [IsScalarTower R B K]
  [Algebra (ResidueField B) K] [IsScalarTower B (ResidueField B) K]
  [Algebra.IsSeparable (ResidueField B) K]

/- English proof (translation)
Establish `: (RingHom.ker φ).IsPrime` using `RingHom.ker_isPrime _`. Take `⟨f, hf, n, _, _, _⟩` from `Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := RingHom.ker φ)`. Set `S` to `Localization.Away f`. Set `P` to `MvPolynomial (Fin n) R`. Set `φ' : S →ₐ[R] K` to `IsLocalization.Away.liftAlgHom f (Ne.isUnit hf)`.

Take `⟨Q, ε, hε⟩` from `exists_etale_subset_range (B := B) fun i : Fin n => φ' (algebraMap P S (MvPolynomial.X i))`. Use `choose c hc using hε`. Set `E` to `Q.Ring`. Use `letI : Algebra R E := ((algebraMap B E).comp (algebraMap R B)).toAlgebra`. Establish `: IsScalarTower R B E` using `.of_algebraMap_eq' rfl`.

Set `χ : P →ₐ[R] K` to `φ'.comp (IsScalarTower.toAlgHom R _ _)`. Establish `hχ : (ε.restrictScalars R).comp (MvPolynomial.aeval c) = χ`. Use extensionality with `i`. Conclude with `(congrArg ε (MvPolynomial.aeval_X c i)).trans (hc i)`. Use `letI := (MvPolynomial.aeval (R := R) c).toAlgebra`.

Use `letI := χ.toAlgebra`. Use `letI := ε.toAlgebra`. Establish `: IsScalarTower B E K` using `.of_algebraMap_eq fun r => (ε.commutes r).symm`. Establish `: IsScalarTower P E K` using `.of_algebraMap_eq fun r => congr($hχ r).symm`. Set `φ'' : S →ₐ[P] K` to `⟨φ', fun r => rfl⟩`.

Set `W` to `E ⊗[P] S`. Set `ε' : W →ₐ[E] K` to `Algebra.TensorProduct.lift (Algebra.ofId E K) φ'' fun _ _ => .all _ _`. Use `⟨W, inferInstance, inferInstance, Algebra.Etale.comp B E W, (Algebra.TensorProduct.includeRight (R := P) (A := E) (B := S)).toRingHom.comp (algebraMap A S), ε'.restrictScalars B, RingHom.ext fun r => ?_, fun a => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(1 : E) ⊗ₜ[P] algebraMap A S (algebraMap R A r) = (algebraMap R E r) ⊗ₜ[P] (1 : S)`. Rewrite using `[← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R P S, ← (MvPolynomial.aeval (R := R) c).commutes r]`.

Conclude with `(Algebra.TensorProduct.tmul_one_eq_one_tmul _).symm`. Express the relevant statement in the definitionally equal form `ε' ((1 : E) ⊗ₜ[P] algebraMap A S a) = φ a`. Rewrite using `[Algebra.TensorProduct.lift_tmul, map_one, one_mul]`. Conclude with `(show φ' (algebraMap A _ a) = φ a by simp [φ'])`.
-/
theorem exists_etale_algHom_lift_of_smooth [Algebra.Smooth R A] (φ : A →ₐ[R] K) :
    ∃ (W : Type u) (_ : CommRing W) (_ : Algebra B W) (_ : Algebra.Etale B W) (ψ : A →+* W)
      (ε : W →ₐ[B] K), ψ.comp (algebraMap R A) = (algebraMap B W).comp (algebraMap R B) ∧
        ∀ a, ε (ψ a) = φ a := by
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime _
  obtain ⟨f, hf, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R)
    (p := RingHom.ker φ)
  let S := Localization.Away f
  let P := MvPolynomial (Fin n) R
  let φ' : S →ₐ[R] K := IsLocalization.Away.liftAlgHom f (Ne.isUnit hf)
  obtain ⟨Q, ε, hε⟩ := exists_etale_subset_range (B := B)
    fun i : Fin n => φ' (algebraMap P S (MvPolynomial.X i))
  choose c hc using hε
  let E := Q.Ring
  letI : Algebra R E := ((algebraMap B E).comp (algebraMap R B)).toAlgebra
  have : IsScalarTower R B E := .of_algebraMap_eq' rfl
  let χ : P →ₐ[R] K := φ'.comp (IsScalarTower.toAlgHom R _ _)
  have hχ : (ε.restrictScalars R).comp (MvPolynomial.aeval c) = χ := by
    ext i
    exact (congrArg ε (MvPolynomial.aeval_X c i)).trans (hc i)
  letI := (MvPolynomial.aeval (R := R) c).toAlgebra
  letI := χ.toAlgebra
  letI := ε.toAlgebra
  have : IsScalarTower B E K := .of_algebraMap_eq fun r => (ε.commutes r).symm
  have : IsScalarTower P E K := .of_algebraMap_eq fun r => congr($hχ r).symm
  let φ'' : S →ₐ[P] K := ⟨φ', fun r => rfl⟩
  let W := E ⊗[P] S
  let ε' : W →ₐ[E] K := Algebra.TensorProduct.lift (Algebra.ofId E K) φ'' fun _ _ => .all _ _
  refine ⟨W, inferInstance, inferInstance, Algebra.Etale.comp B E W,
    (Algebra.TensorProduct.includeRight (R := P) (A := E) (B := S)).toRingHom.comp
      (algebraMap A S), ε'.restrictScalars B, RingHom.ext fun r => ?_, fun a => ?_⟩
  · change (1 : E) ⊗ₜ[P] algebraMap A S (algebraMap R A r) = (algebraMap R E r) ⊗ₜ[P] (1 : S)
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R P S,
      ← (MvPolynomial.aeval (R := R) c).commutes r]
    exact (Algebra.TensorProduct.tmul_one_eq_one_tmul _).symm
  · change ε' ((1 : E) ⊗ₜ[P] algebraMap A S a) = φ a
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    exact (show φ' (algebraMap A _ a) = φ a by simp [φ'])

end QuasiSection

section LocalForms

universe u

variable {B W : Type u} {K : Type*} [CommRing B] [CommRing W] [Field K] [IsLocalRing B]
  [Algebra B W] [Algebra B K] [Algebra (ResidueField B) K] [IsScalarTower B (ResidueField B) K]

omit [Algebra B W] [CommRing W] in
/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_apply B (ResidueField B) K, map_eq_zero]`. Conclude with `residue_eq_zero_iff b`.
-/
theorem algebraMap_eq_zero_iff_mem_maximalIdeal (b : B) :
    algebraMap B K b = 0 ↔ b ∈ maximalIdeal B := by
  rw [IsScalarTower.algebraMap_apply B (ResidueField B) K, map_eq_zero]
  exact residue_eq_zero_iff b

omit [Algebra B W] [CommRing W] in

/- English proof (translation)
Establish `: Module.Finite B (AdjoinRoot μ)` using `hμm.finite_adjoinRoot`. Assume the negation of the conclusion as `hn`. Take `⟨M, hM, hgM⟩` from `exists_max_ideal_of_mem_nonunits hn`. Establish `hM' : M.comap (algebraMap B (AdjoinRoot μ)) = maximalIdeal B` using `eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M)`. Establish `hco : IsCoprime (minpoly (ResidueField B) θ) (g.map (residue B))`.

Rewrite using `[(minpoly.irreducible hθ).coprime_iff_not_dvd, minpoly.dvd_iff]`. Rewrite `hg` using `[← aeval_map_algebraMap (ResidueField B)]`. Then use the resulting hypothesis. Take `⟨a, b, hab⟩` from `hco`. Take `⟨a, rfl⟩` from `map_surjective (residue B) residue_surjective a`. Take `⟨b, rfl⟩` from `map_surjective (residue B) residue_surjective b`.

Establish `h₀ : (a * μ + b * g - 1).map (residue B) = 0`. Rewrite using `[Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, hμ, hab, Polynomial.map_one, sub_self]`. Establish `h₁ : AdjoinRoot.mk μ (a * μ + b * g - 1) ∈ M`. Rewrite using `[(a * μ + b * g - 1).as_sum_support_C_mul_X_pow, map_sum]`. Use `Ideal.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul]`. Use `Ideal.mul_mem_right _ _ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap B (AdjoinRoot μ) _ ∈ M`. Rewrite using `[← Ideal.mem_comap, hM', ← residue_eq_zero_iff, ← coeff_map, h₀, coeff_zero]`. Rewrite `h₁` using `[map_sub, map_add, map_mul, map_mul, AdjoinRoot.mk_self, mul_zero, zero_add, map_one]`.

Establish `h₂` using `sub_mem (M.mul_mem_left (AdjoinRoot.mk μ b) hgM) h₁`. Rewrite `h₂` using `[sub_sub_cancel]`. Conclude with `hM.ne_top ((Ideal.eq_top_iff_one _).mpr h₂)`.
-/
theorem isUnit_adjoinRoot_mk_of_aeval_ne_zero {θ : K} (hθ : IsIntegral (ResidueField B) θ)
    {μ : B[X]} (hμm : μ.Monic) (hμ : μ.map (residue B) = minpoly (ResidueField B) θ) {g : B[X]}
    (hg : aeval θ g ≠ 0) : IsUnit (AdjoinRoot.mk μ g) := by
  have : Module.Finite B (AdjoinRoot μ) := hμm.finite_adjoinRoot
  by_contra hn
  obtain ⟨M, hM, hgM⟩ := exists_max_ideal_of_mem_nonunits hn
  have hM' : M.comap (algebraMap B (AdjoinRoot μ)) = maximalIdeal B :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M)
  have hco : IsCoprime (minpoly (ResidueField B) θ) (g.map (residue B)) := by
    rw [(minpoly.irreducible hθ).coprime_iff_not_dvd, minpoly.dvd_iff]
    rwa [← aeval_map_algebraMap (ResidueField B)] at hg
  obtain ⟨a, b, hab⟩ := hco
  obtain ⟨a, rfl⟩ := map_surjective (residue B) residue_surjective a
  obtain ⟨b, rfl⟩ := map_surjective (residue B) residue_surjective b
  have h₀ : (a * μ + b * g - 1).map (residue B) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, hμ, hab,
      Polynomial.map_one, sub_self]
  have h₁ : AdjoinRoot.mk μ (a * μ + b * g - 1) ∈ M := by
    rw [(a * μ + b * g - 1).as_sum_support_C_mul_X_pow, map_sum]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [map_mul]
    refine Ideal.mul_mem_right _ _ ?_
    change algebraMap B (AdjoinRoot μ) _ ∈ M
    rw [← Ideal.mem_comap, hM', ← residue_eq_zero_iff, ← coeff_map, h₀, coeff_zero]
  rw [map_sub, map_add, map_mul, map_mul, AdjoinRoot.mk_self, mul_zero, zero_add, map_one] at h₁
  have h₂ := sub_mem (M.mul_mem_left (AdjoinRoot.mk μ b) hgM) h₁
  rw [sub_sub_cancel] at h₂
  exact hM.ne_top ((Ideal.eq_top_iff_one _).mpr h₂)

end LocalForms

section LocalHenselian

universe u

variable {B W : Type u} {K : Type*} [CommRing B] [CommRing W] [Field K] [HenselianLocalRing B]
  [Algebra B W] [Algebra B K] [Algebra (ResidueField B) K] [IsScalarTower B (ResidueField B) K]
  [Algebra.IsSeparable (ResidueField B) K]

end LocalHenselian

section DiscreteValuation

/- English proof (translation)
Establish `key : ∀ x : B, x ≠ 0 → ∃ (n : ℕ) (u : Bˣ), t ^ n * u = x`. Introduce `x hx`. Establish `h : ∃ n : ℕ, ¬ t ^ n ∣ x`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`.

Apply `hx` to reduce the goal to its premises. Rewrite using `[← Ideal.mem_bot, ← hs, Ideal.mem_iInf]`. Introduce `n`. Rewrite using `[hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Conclude with `hc n`.

Establish `h₀ : Nat.find h ≠ 0` using `fun h₀ => Nat.find_spec h (by simp [h₀])`. Take `⟨n, hn⟩` from `Nat.exists_eq_succ_of_ne_zero h₀`. Take `⟨u, rfl⟩` from `not_not.mp (Nat.find_min h (hn ▸ n.lt_succ_self))`. Establish `hu : IsUnit u`. Assume the negation of the conclusion as `hu`.

Establish `h₁ : u ∈ maximalIdeal B` using `hu`. Rewrite `h₁` using `[hm, Ideal.mem_span_singleton]`. Conclude with `Nat.find_spec h (by rw [hn, pow_succ]; exact mul_dvd_mul_left _ h₁)`. Conclude with `⟨n, hu.unit, rfl⟩`. Establish `hreg : ∀ x : B, x ≠ 0 → x ∈ nonZeroDivisors B` using `fun x hx => by`.

Take `⟨n, u, rfl⟩` from `key x hx`. Conclude with `mul_mem (pow_mem ht n) u.isUnit.mem_nonZeroDivisors`. Establish `: NoZeroDivisors B` using `⟨fun {a b} hab => by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`.

Conclude with `hc.1 (mem_nonZeroDivisors_iff_right.mp (hreg b hc.2) a hab)⟩`. Establish `: IsDomain B` using `NoZeroDivisors.to_isDomain B`. Establish `hp : Prime t`. Rewrite using `[← Ideal.span_singleton_prime (nonZeroDivisors.ne_zero ht), ← hm]`. Use `infer_instance`.

Conclude with `⟨this, IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨t, hp.irreducible, fun {x} hx => by`. Take `⟨n, u, h⟩` from `key x hx`. Conclude with `⟨n, u, h⟩⟩⟩`.
-/
theorem exists_isDiscreteValuationRing_of_maximalIdeal_eq_span {B : Type*} [CommRing B]
    [IsLocalRing B] {t : B} (ht : t ∈ nonZeroDivisors B) (hm : maximalIdeal B = Ideal.span {t})
    (hs : ⨅ n : ℕ, maximalIdeal B ^ n = ⊥) :
    ∃ _ : IsDomain B, IsDiscreteValuationRing B := by
  classical
  have key : ∀ x : B, x ≠ 0 → ∃ (n : ℕ) (u : Bˣ), t ^ n * u = x := by
    intro x hx
    have h : ∃ n : ℕ, ¬ t ^ n ∣ x := by
      by_contra hc
      push Not at hc
      apply hx
      rw [← Ideal.mem_bot, ← hs, Ideal.mem_iInf]
      intro n
      rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact hc n
    have h₀ : Nat.find h ≠ 0 := fun h₀ => Nat.find_spec h (by simp [h₀])
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero h₀
    obtain ⟨u, rfl⟩ := not_not.mp (Nat.find_min h (hn ▸ n.lt_succ_self))
    have hu : IsUnit u := by
      by_contra hu
      have h₁ : u ∈ maximalIdeal B := hu
      rw [hm, Ideal.mem_span_singleton] at h₁
      exact Nat.find_spec h (by rw [hn, pow_succ]; exact mul_dvd_mul_left _ h₁)
    exact ⟨n, hu.unit, rfl⟩
  have hreg : ∀ x : B, x ≠ 0 → x ∈ nonZeroDivisors B := fun x hx => by
    obtain ⟨n, u, rfl⟩ := key x hx
    exact mul_mem (pow_mem ht n) u.isUnit.mem_nonZeroDivisors
  have : NoZeroDivisors B := ⟨fun {a b} hab => by
    by_contra hc
    push Not at hc
    exact hc.1 (mem_nonZeroDivisors_iff_right.mp (hreg b hc.2) a hab)⟩
  have : IsDomain B := NoZeroDivisors.to_isDomain B
  have hp : Prime t := by
    rw [← Ideal.span_singleton_prime (nonZeroDivisors.ne_zero ht), ← hm]
    infer_instance
  exact ⟨this, IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨t, hp.irreducible, fun {x} hx => by
      obtain ⟨n, u, h⟩ := key x hx
      exact ⟨n, u, h⟩⟩⟩

variable (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

/- English proof (translation)
Take `⟨t, ht⟩` from `IsDiscreteValuationRing.exists_irreducible V`. Use `exists_isDiscreteValuationRing_of_maximalIdeal_eq_span (t := algebraMap V B t) ?_ ?_ hs` and prove the remaining obligations. Rewrite using `[mem_nonZeroDivisors_iff_left]`. Introduce `x hx`. Use `Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B) (mem_nonZeroDivisors_of_ne_zero ht.ne_zero)` as an intermediate fact.

Conclude with `this (show t • x = t • (0 : B) by rw [smul_zero, Algebra.smul_def, hx])`. Rewrite using `[← hm, ht.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]`.
-/
theorem exists_isDiscreteValuationRing_of_flat (B : Type*) [CommRing B] [IsLocalRing B]
    [Algebra V B] [Module.Flat V B]
    (hm : (maximalIdeal V).map (algebraMap V B) = maximalIdeal B)
    (hs : ⨅ n : ℕ, maximalIdeal B ^ n = ⊥) : ∃ _ : IsDomain B, IsDiscreteValuationRing B := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible V
  refine exists_isDiscreteValuationRing_of_maximalIdeal_eq_span (t := algebraMap V B t) ?_ ?_ hs
  · rw [mem_nonZeroDivisors_iff_left]
    intro x hx
    have := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B)
      (mem_nonZeroDivisors_of_ne_zero ht.ne_zero)
    exact this (show t • x = t • (0 : B) by rw [smul_zero, Algebra.smul_def, hx])
  · rw [← hm, ht.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]

/- English proof (translation)
Establish `: IsNoetherianRing B` using `Algebra.EssFiniteType.isNoetherianRing V B`. Conclude with `exists_isDiscreteValuationRing_of_flat V B Algebra.FormallyUnramified.map_maximalIdeal (Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal B).ne_top)`.
-/
theorem exists_isDiscreteValuationRing_of_unramified (B : Type*) [CommRing B] [IsLocalRing B]
    [Algebra V B] [IsLocalHom (algebraMap V B)] [Module.Flat V B] [Algebra.EssFiniteType V B]
    [Algebra.FormallyUnramified V B] : ∃ _ : IsDomain B, IsDiscreteValuationRing B := by
  have : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing V B
  exact exists_isDiscreteValuationRing_of_flat V B Algebra.FormallyUnramified.map_maximalIdeal
    (Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal B).ne_top)

/- English proof (translation)
Establish `: Algebra.EssFiniteType B L` using `.of_isLocalization L (nonZeroDivisors B)`. Establish `: Algebra.FormallyUnramified B L` using `.of_isLocalization (nonZeroDivisors B)`. Establish `: Algebra.EssFiniteType R L` using `.comp R B L`. Establish `: Algebra.FormallyUnramified R L` using `.comp R B L`. Establish `: Algebra.EssFiniteType K L` using `.of_comp R K L`.

Establish `: Algebra.FormallyUnramified K L` using `.of_restrictScalars R K L`. Conclude with `⟨Algebra.FormallyUnramified.finite_of_free K L, Algebra.FormallyUnramified.isSeparable K L⟩`.
-/
theorem finite_and_isSeparable_fractionRing_of_unramified (R B K L : Type*) [CommRing R]
    [CommRing B] [Algebra R B] [Algebra.EssFiniteType R B] [Algebra.FormallyUnramified R B]
    [Field K] [Field L] [Algebra R K] [Algebra B L] [IsFractionRing B L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [IsScalarTower R B L] :
    Module.Finite K L ∧ Algebra.IsSeparable K L := by
  have : Algebra.EssFiniteType B L := .of_isLocalization L (nonZeroDivisors B)
  have : Algebra.FormallyUnramified B L := .of_isLocalization (nonZeroDivisors B)
  have : Algebra.EssFiniteType R L := .comp R B L
  have : Algebra.FormallyUnramified R L := .comp R B L
  have : Algebra.EssFiniteType K L := .of_comp R K L
  have : Algebra.FormallyUnramified K L := .of_restrictScalars R K L
  exact ⟨Algebra.FormallyUnramified.finite_of_free K L, Algebra.FormallyUnramified.isSeparable K L⟩

end DiscreteValuation

end GlobalTheory
