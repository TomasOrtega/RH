import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeNormOfKummer
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.Fld

/- English proof (translation)
Use `Fintype.ofFinite R` as an intermediate fact. Establish `hd : (Polynomial.X ^ q - Polynomial.X : Polynomial R).natDegree = q`. Rewrite using `[Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by simpa using hq), Polynomial.natDegree_X_pow]`. Establish `hne : (Polynomial.X ^ q - Polynomial.X : Polynomial R) ≠ 0`. Introduce `h0`.

Rewrite `hd` using `[h0, Polynomial.natDegree_zero]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Nat.card_eq_fintype_card, ← Finset.card_univ]`. Use `le_trans (Polynomial.card_le_degree_of_subset_roots ?_) hd.le` and prove the remaining obligations. Introduce `x _`.

Rewrite using `[Polynomial.mem_roots hne]`. Simplify using `[h x]`.
-/
theorem card_le_of_pow_eq_self {R : Type} [CommRing R] [IsDomain R] [Finite R] {q : ℕ} (hq : 1 < q)
    (h : ∀ x : R, x ^ q = x) : Nat.card R ≤ q := by
  classical
  have := Fintype.ofFinite R
  have hd : (Polynomial.X ^ q - Polynomial.X : Polynomial R).natDegree = q := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by simpa using hq), Polynomial.natDegree_X_pow]
  have hne : (Polynomial.X ^ q - Polynomial.X : Polynomial R) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hd
    omega
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  refine le_trans (Polynomial.card_le_degree_of_subset_roots ?_) hd.le
  intro x _
  rw [Polynomial.mem_roots hne]
  simp [h x]

/- English proof (translation)
Set `e : 𝓞 F ≃ₐ[𝓞 K] 𝓞 F` to `RingOfIntegers.mapAlgEquiv σ`. Choose the witnesses or unpack the hypotheses as in `⟨θ, hθ⟩ : ∃ θ : 𝓞 F, e θ - θ ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Apply `hσ` to reduce the goal to its premises.

Use extensionality with `x`. Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 F) x`. Establish `h : ∀ a : 𝓞 F, σ (algebraMap (𝓞 F) F a) = algebraMap (𝓞 F) F a` using `fun a => congrArg (algebraMap (𝓞 F) F) (sub_eq_zero.1 (hc a))`. Simplify using `only [map_div₀, h, AlgEquiv.one_apply]`. Establish `hfin : {P : HeightOneSpectrum (𝓞 F) | P.asIdeal ∣ Ideal.span {e θ - θ}}.Finite` using `Ideal.finite_factors (by simpa using hθ)`.

Use `⟨{v | ∃ P : HeightOneSpectrum (𝓞 F), P.asIdeal ∣ Ideal.span {e θ - θ} ∧ P.asIdeal.under (𝓞 K) = v.asIdeal}, ?_, ?_⟩` and prove the remaining obligations. Use `Set.Finite.of_finite_image (f := fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal) ((hfin.image (fun P => P.asIdeal.under (𝓞 K))).subset ?_) (fun a _ b _ h => HeightOneSpectrum.ext h)` and prove the remaining obligations. Introduce and unpack `_ ⟨v, ⟨P, hP, hv⟩, rfl⟩`. Conclude with `⟨P, hP, hv⟩`. Introduce and unpack `v hv ⟨P, hP, hPo, hx⟩`.

Establish `hvp` using `v.isPrime`. Establish `hne : P ≠ ⊥` using `Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P`. Establish `hfP : Finite (𝓞 F ⧸ P)` using `Ideal.finiteQuotientOfFreeOfNeBot _ hne`. Establish `hfv : Finite (𝓞 K ⧸ v.asIdeal)` using `Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot`. Establish `hq : 1 < Ideal.absNorm v.asIdeal`.

Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Conclude with `Finite.one_lt_card`. Establish `hle : Nat.card (𝓞 F ⧸ P) ≤ Nat.card (𝓞 K ⧸ v.asIdeal)`. Establish `h0 : Ideal.absNorm v.asIdeal = Nat.card (𝓞 K ⧸ v.asIdeal)`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`.

Rewrite using `[← h0]`. Use `card_le_of_pow_eq_self hq fun x => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Use `hx x` as an intermediate fact. Rewrite `this` using `[one_smul]`.

Rewrite using `[← map_pow]`. Conclude with `(Ideal.Quotient.eq.2 this).symm`. Establish `hinj : Function.Injective (algebraMap (𝓞 K ⧸ v.asIdeal) (𝓞 F ⧸ P))` using `FaithfulSMul.algebraMap_injective _ _`. Establish `hbij : Function.Bijective (algebraMap (𝓞 K ⧸ v.asIdeal) (𝓞 F ⧸ P))` using `hinj.bijective_of_nat_card_le hle`. Establish `hN : Ideal.absNorm P = Ideal.absNorm v.asIdeal`.

Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Conclude with `(Nat.card_eq_of_bijective _ hbij).symm`. Establish `hQo : (P.comap e).LiesOver v.asIdeal` using `inferInstance`. Establish `hQ : (P.comap e).IsPrime` using `Ideal.comap_isPrime _ _`. Establish `hQne : P.comap e ≠ ⊥` using `Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot _`.

Use `⟨⟨P, hP, hne⟩, ⟨P.comap e, hQ, hQne⟩, ?_, hPo, hQo, hN, ?_⟩` and prove the remaining obligations. Introduce `h`. Establish `h' : P = P.comap e` using `congrArg HeightOneSpectrum.asIdeal h`. Apply `hv` to reduce the goal to its premises. Use `⟨⟨P, hP, hne⟩, ?_, hPo.over.symm⟩` and prove the remaining obligations.

Rewrite using `[Ideal.dvd_span_singleton]`. Take `⟨a, ha⟩` from `hbij.2 (Ideal.Quotient.mk P θ)`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Establish `h1 : algebraMap (𝓞 K) (𝓞 F) a - θ ∈ P` using `Ideal.Quotient.eq.1 ha`. Establish `h2 : e (algebraMap (𝓞 K) (𝓞 F) a - θ) ∈ P`.

Use `h' ▸ h1` as an intermediate fact. Conclude with `this`. Rewrite `h2` using `[map_sub, AlgEquiv.commutes]`. Use `P.sub_mem h1 h2` as an intermediate fact. Use `show e θ - θ ∈ P`.

Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Use `show Ideal.absNorm (P.comap e) = _`. Rewrite using `[← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Use `Nat.card_congr (Ideal.quotientEquiv (P.comap e) P e.toRingEquiv ?_).toEquiv` and prove the remaining obligations.

Conclude with `(Ideal.map_comap_of_surjective (e.toRingEquiv : 𝓞 F →+* 𝓞 F) e.surjective P).symm`.
-/
theorem exists_two_primes_of_isFrob_one (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F]
    [Algebra K F] (σ : F ≃ₐ[K] F) (hσ : σ ≠ 1) :
    ∃ T : Set (HeightOneSpectrum (𝓞 K)), T.Finite ∧ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → IsFrob F v 1 →
      ∃ P Q : HeightOneSpectrum (𝓞 F), P ≠ Q ∧ P.asIdeal.LiesOver v.asIdeal ∧ Q.asIdeal.LiesOver v.asIdeal ∧
        Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧ Ideal.absNorm Q.asIdeal = Ideal.absNorm v.asIdeal := by
  let e : 𝓞 F ≃ₐ[𝓞 K] 𝓞 F := RingOfIntegers.mapAlgEquiv σ
  obtain ⟨θ, hθ⟩ : ∃ θ : 𝓞 F, e θ - θ ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hσ
    ext x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
    have h : ∀ a : 𝓞 F, σ (algebraMap (𝓞 F) F a) = algebraMap (𝓞 F) F a := fun a =>
      congrArg (algebraMap (𝓞 F) F) (sub_eq_zero.1 (hc a))
    simp only [map_div₀, h, AlgEquiv.one_apply]
  have hfin : {P : HeightOneSpectrum (𝓞 F) | P.asIdeal ∣ Ideal.span {e θ - θ}}.Finite :=
    Ideal.finite_factors (by simpa using hθ)
  refine ⟨{v | ∃ P : HeightOneSpectrum (𝓞 F), P.asIdeal ∣ Ideal.span {e θ - θ} ∧
    P.asIdeal.under (𝓞 K) = v.asIdeal}, ?_, ?_⟩
  · refine Set.Finite.of_finite_image (f := fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal)
      ((hfin.image (fun P => P.asIdeal.under (𝓞 K))).subset ?_) (fun a _ b _ h => HeightOneSpectrum.ext h)
    rintro _ ⟨v, ⟨P, hP, hv⟩, rfl⟩
    exact ⟨P, hP, hv⟩
  rintro v hv ⟨P, hP, hPo, hx⟩
  have hvp := v.isPrime
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
  have hfP : Finite (𝓞 F ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  have hfv : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  have hq : 1 < Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact Finite.one_lt_card
  have hle : Nat.card (𝓞 F ⧸ P) ≤ Nat.card (𝓞 K ⧸ v.asIdeal) := by
    have h0 : Ideal.absNorm v.asIdeal = Nat.card (𝓞 K ⧸ v.asIdeal) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [← h0]
    refine card_le_of_pow_eq_self hq fun x => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have := hx x
    rw [one_smul] at this
    rw [← map_pow]
    exact (Ideal.Quotient.eq.2 this).symm
  have hinj : Function.Injective (algebraMap (𝓞 K ⧸ v.asIdeal) (𝓞 F ⧸ P)) := FaithfulSMul.algebraMap_injective _ _
  have hbij : Function.Bijective (algebraMap (𝓞 K ⧸ v.asIdeal) (𝓞 F ⧸ P)) :=
    hinj.bijective_of_nat_card_le hle
  have hN : Ideal.absNorm P = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact (Nat.card_eq_of_bijective _ hbij).symm
  have hQo : (P.comap e).LiesOver v.asIdeal := inferInstance
  have hQ : (P.comap e).IsPrime := Ideal.comap_isPrime _ _
  have hQne : P.comap e ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot _
  refine ⟨⟨P, hP, hne⟩, ⟨P.comap e, hQ, hQne⟩, ?_, hPo, hQo, hN, ?_⟩
  · intro h
    have h' : P = P.comap e := congrArg HeightOneSpectrum.asIdeal h
    apply hv
    refine ⟨⟨P, hP, hne⟩, ?_, hPo.over.symm⟩
    rw [Ideal.dvd_span_singleton]
    obtain ⟨a, ha⟩ := hbij.2 (Ideal.Quotient.mk P θ)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have h1 : algebraMap (𝓞 K) (𝓞 F) a - θ ∈ P := Ideal.Quotient.eq.1 ha
    have h2 : e (algebraMap (𝓞 K) (𝓞 F) a - θ) ∈ P := by
      have := h' ▸ h1
      exact this
    rw [map_sub, AlgEquiv.commutes] at h2
    have := P.sub_mem h1 h2
    show e θ - θ ∈ P
    convert this using 1
    ring
  · show Ideal.absNorm (P.comap e) = _
    rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    refine Nat.card_congr (Ideal.quotientEquiv (P.comap e) P e.toRingEquiv ?_).toEquiv
    exact (Ideal.map_comap_of_surjective (e.toRingEquiv : 𝓞 F →+* 𝓞 F) e.surjective P).symm

end GlobalTheory.Mem.Fld
