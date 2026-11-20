import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CotInd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaFlatReg

open IsLocalRing UpperTheory.V.AlgebraTools

/- English proof (translation)
Establish `hJn : RingHom.ker (Ideal.Quotient.mk J) ≤ n`. Rewrite using `[Ideal.mk_ker]` and apply the resulting hypothesis. Establish `hm : (n.map (Ideal.Quotient.mk J)).IsPrime` using `Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hJn`. Establish `hle : J ≤ (J.map (algebraMap R A)).comap (algebraMap R A)` using `Ideal.le_comap_map`. Use `letI : Algebra (R ⧸ J) (A ⧸ J.map (algebraMap R A)) := (Ideal.quotientMap _ _ hle).toAlgebra`.

Establish `hl` using `IsLocalization.of_surjective n.primeCompl A (S' := A ⧸ J.map (algebraMap R A)) (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective rfl (by rw [Ideal.mk_ker, Ideal.mk_ker])`. Establish `e : n.primeCompl.map (Ideal.Quotient.mk J) = (n.map (Ideal.Quotient.mk J)).primeCompl`. Establish `hc : (n.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) = n`. Rewrite using `[Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_eq_left.2 hJn]`. Use extensionality with `y`.

Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x', hx', e⟩ hx`. Conclude with `hx' (hc.le (show Ideal.Quotient.mk J x' ∈ _ from e ▸ hx))`. Conclude with `fun hx => ⟨x, fun h => hx (Ideal.mem_map_of_mem _ h), rfl⟩`.

Rewrite `hl` using `[e]`. Use `IsRegularRing.isRegularLocalRing_localization (n.map (Ideal.Quotient.mk J))` as an intermediate fact. Conclude with `IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv (n.map (Ideal.Quotient.mk J)).primeCompl (Localization.AtPrime (n.map (Ideal.Quotient.mk J))) _).toRingEquiv`.
-/
private theorem fibre_reg (R : Type) [CommRing R] (J n : Ideal R) [n.IsPrime] (hn : J ≤ n)
    [IsRegularRing (R ⧸ J)] (A : Type) [CommRing A] [Algebra R A] [IsLocalization.AtPrime A n] :
    IsRegularLocalRing (A ⧸ J.map (algebraMap R A)) := by
  have hJn : RingHom.ker (Ideal.Quotient.mk J) ≤ n := by
    rwa [Ideal.mk_ker]
  have hm : (n.map (Ideal.Quotient.mk J)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hJn
  have hle : J ≤ (J.map (algebraMap R A)).comap (algebraMap R A) := Ideal.le_comap_map
  letI : Algebra (R ⧸ J) (A ⧸ J.map (algebraMap R A)) := (Ideal.quotientMap _ _ hle).toAlgebra
  have hl := IsLocalization.of_surjective n.primeCompl A (S' := A ⧸ J.map (algebraMap R A))
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective rfl
    (by rw [Ideal.mk_ker, Ideal.mk_ker])
  have e : n.primeCompl.map (Ideal.Quotient.mk J) = (n.map (Ideal.Quotient.mk J)).primeCompl := by
    have hc : (n.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) = n := by
      rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_eq_left.2 hJn]
    ext y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    constructor
    · rintro ⟨x', hx', e⟩ hx
      exact hx' (hc.le (show Ideal.Quotient.mk J x' ∈ _ from e ▸ hx))
    · exact fun hx => ⟨x, fun h => hx (Ideal.mem_map_of_mem _ h), rfl⟩
  rw [e] at hl
  have := IsRegularRing.isRegularLocalRing_localization (n.map (Ideal.Quotient.mk J))
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv (n.map (Ideal.Quotient.mk J)).primeCompl
    (Localization.AtPrime (n.map (Ideal.Quotient.mk J))) _).toRingEquiv

/- English proof (translation)
Introduce `A _ _ σ _ Q _ hQ`. Establish `hcomp : algebraMap A (Localization.AtPrime Q) = (algebraMap (MvPolynomial σ A) (Localization.AtPrime Q)).comp MvPolynomial.C` using `IsScalarTower.algebraMap_eq A (MvPolynomial σ A) (Localization.AtPrime Q)`. Use `haveI : IsRegularRing (MvPolynomial σ A ⧸ (maximalIdeal A).map (MvPolynomial.C : A →+* MvPolynomial σ A)) := by`. Use `letI := Ideal.Quotient.field (maximalIdeal A)`. Use `haveI : IsRegularRing (MvPolynomial σ (A ⧸ maximalIdeal A)) := inferInstance`.

Conclude with `IsRegularRing.of_ringEquiv (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) (maximalIdeal A)).toRingEquiv`. Establish `hf` using `fibre_reg _ _ Q hQ (Localization.AtPrime Q)`. Rewrite `hf` using `[Ideal.map_map, ← hcomp]`. Use `haveI : IsNoetherianRing (Localization.AtPrime Q) := IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance`. Use `haveI : Module.Flat (MvPolynomial σ A) (Localization.AtPrime Q) := IsLocalization.flat _ Q.primeCompl`.

Use `haveI : Module.Flat A (Localization.AtPrime Q) := Module.Flat.trans A (MvPolynomial σ A) (Localization.AtPrime Q)`. Use `haveI : IsLocalHom (algebraMap A (Localization.AtPrime Q)) := by`. Use `⟨fun a ha => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hna`. Establish `h1 : MvPolynomial.C a ∈ Q` using `hQ (Ideal.mem_map_of_mem _ ((mem_maximalIdeal a).2 hna))`.

Rewrite `ha` using `[hcomp]`. Conclude with `(IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime Q) Q _).1 ha h1`. Establish `H` using `regular_of_flat_fibre A (Localization.AtPrime Q)`. Rewrite `H` using `[hcomp]`. Conclude with `H`.
-/
theorem UpperTheory.V.AlgebraTools.regular_polynomial_localization :
    ∀ (A : Type) [CommRing A] [IsRegularLocalRing A] (σ : Type) [Finite σ] (Q : Ideal (MvPolynomial σ A)) [Q.IsPrime],
      (maximalIdeal A).map (MvPolynomial.C : A →+* MvPolynomial σ A) ≤ Q →
      IsRegularLocalRing (Localization.AtPrime Q) ∧ ∀ (κ : Type) [Fintype κ] (x : κ → A), CotInd A x →
        CotInd (Localization.AtPrime Q) (fun k => algebraMap (MvPolynomial σ A) _ (MvPolynomial.C (x k))) := by
  intro A _ _ σ _ Q _ hQ
  have hcomp : algebraMap A (Localization.AtPrime Q) =
      (algebraMap (MvPolynomial σ A) (Localization.AtPrime Q)).comp MvPolynomial.C :=
    IsScalarTower.algebraMap_eq A (MvPolynomial σ A) (Localization.AtPrime Q)
  haveI : IsRegularRing (MvPolynomial σ A ⧸
      (maximalIdeal A).map (MvPolynomial.C : A →+* MvPolynomial σ A)) := by
    letI := Ideal.Quotient.field (maximalIdeal A)
    haveI : IsRegularRing (MvPolynomial σ (A ⧸ maximalIdeal A)) := inferInstance
    exact IsRegularRing.of_ringEquiv
      (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) (maximalIdeal A)).toRingEquiv
  have hf := fibre_reg _ _ Q hQ (Localization.AtPrime Q)
  rw [Ideal.map_map, ← hcomp] at hf
  haveI : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  haveI : Module.Flat (MvPolynomial σ A) (Localization.AtPrime Q) :=
    IsLocalization.flat _ Q.primeCompl
  haveI : Module.Flat A (Localization.AtPrime Q) :=
    Module.Flat.trans A (MvPolynomial σ A) (Localization.AtPrime Q)
  haveI : IsLocalHom (algebraMap A (Localization.AtPrime Q)) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 : MvPolynomial.C a ∈ Q := hQ (Ideal.mem_map_of_mem _ ((mem_maximalIdeal a).2 hna))
    rw [hcomp] at ha
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime Q) Q _).1 ha h1
  have H := regular_of_flat_fibre A (Localization.AtPrime Q)
  rw [hcomp] at H
  exact H
