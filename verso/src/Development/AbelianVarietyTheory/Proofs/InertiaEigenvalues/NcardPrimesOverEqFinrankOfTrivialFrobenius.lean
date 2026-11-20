import Mathlib
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

/- English proof (translation)
Use `haveI := Fintype.ofFinite F`. Establish `hne : (X ^ q - X : F[X]) ≠ 0`. Introduce `h0`. Establish `h1` using `congrArg Polynomial.natDegree (sub_eq_zero.1 h0)`. Rewrite `h1` using `[natDegree_X_pow, natDegree_X]`.

Use linear arithmetic over natural numbers and integers. Establish `hdeg : (X ^ q - X : F[X]).natDegree ≤ q`. Use `(natDegree_sub_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[natDegree_X_pow, natDegree_X]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[Nat.card_eq_fintype_card, ← Finset.card_univ]`. Use `le_trans ?_ hdeg` and prove the remaining obligations. Use `Polynomial.card_le_degree_of_subset_roots ?_` and prove the remaining obligations. Introduce `x _`. Rewrite using `[mem_roots hne]`.

Simplify using `[h x]`.
-/
theorem natCard_le_of_forall_pow_eq_self (F : Type*) [CommRing F] [IsDomain F] [Finite F]
    (q : ℕ) (hq : 1 < q) (h : ∀ x : F, x ^ q = x) : Nat.card F ≤ q := by
  classical
  haveI := Fintype.ofFinite F
  have hne : (X ^ q - X : F[X]) ≠ 0 := by
    intro h0
    have h1 := congrArg Polynomial.natDegree (sub_eq_zero.1 h0)
    rw [natDegree_X_pow, natDegree_X] at h1
    omega
  have hdeg : (X ^ q - X : F[X]).natDegree ≤ q := by
    refine (natDegree_sub_le _ _).trans ?_
    rw [natDegree_X_pow, natDegree_X]
    omega
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  refine le_trans ?_ hdeg
  refine Polynomial.card_le_degree_of_subset_roots ?_
  intro x _
  rw [mem_roots hne]
  simp [h x]

/- English proof (translation)
Introduce `K M _ _ _ _ _ _`. Establish `hD : differentIdeal (𝓞 K) (𝓞 M) ≠ ⊥` using `differentIdeal_ne_bot`. Use `⟨(fun P : HeightOneSpectrum (𝓞 M) => P.under (𝓞 K)) '' {P | P.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 M)}, (Ideal.finite_factors hD).image _, ?_⟩` and prove the remaining obligations. Introduce `v hv hx`. Use `haveI := v.isPrime`.

Establish `hq : 1 < Ideal.absNorm v.asIdeal`. Establish `h0 : Ideal.absNorm v.asIdeal ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `v.ne_bot`. Establish `h1 : Ideal.absNorm v.asIdeal ≠ 1`.

Rewrite using `[Ne, Ideal.absNorm_eq_one_iff]`. Conclude with `v.isPrime.ne_top`. Use linear arithmetic over natural numbers and integers. Establish `hf : ∀ P ∈ v.asIdeal.primesOver (𝓞 M), P.inertiaDeg (𝓞 K) = 1`. Introduce `P hP`.

Use `haveI := hP.1`. Use `haveI := hP.2`. Establish `hP0 : P ≠ ⊥` using `Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P`. Use `haveI : Finite (𝓞 M ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0`. Establish `hle : Nat.card (𝓞 M ⧸ P) ≤ Ideal.absNorm v.asIdeal`.

Use `natCard_le_of_forall_pow_eq_self _ _ hq fun y => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Rewrite using `[← map_pow, Ideal.Quotient.eq]`. Conclude with `hx P hP x`. Establish `hN : Ideal.absNorm P = Nat.card (𝓞 M ⧸ P)`.

Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Establish `h` using `Ideal.absNorm_pow_inertiaDeg v.asIdeal P`. Rewrite `hle` using `[← hN, ← h]`. Establish `hpos : 0 < P.inertiaDeg (𝓞 K)` using `P.inertiaDeg_pos (𝓞 K)`. Establish `h2 : P.inertiaDeg (𝓞 K) ≤ 1`.

Rewrite using `[← Nat.pow_le_pow_iff_right hq, pow_one]`. Conclude with `hle`. Use linear arithmetic over natural numbers and integers. Establish `he : ∀ P ∈ v.asIdeal.primesOver (𝓞 M), P.ramificationIdx (𝓞 K) = 1`. Introduce `P hP`.

Use `haveI := hP.1`. Use `haveI := hP.2`. Establish `hP0 : P ≠ ⊥` using `Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P`. Establish `hn : ¬ P ∣ differentIdeal (𝓞 K) (𝓞 M)`. Introduce `hd`.

Use `hv ⟨⟨P, hP.1, hP0⟩, hd, ?_⟩` and prove the remaining obligations. Use `ext1`. Conclude with `(Ideal.over_def P v.asIdeal).symm`. Use `haveI : Algebra.IsUnramifiedAt (𝓞 K) P := not_dvd_differentIdeal_iff.1 hn`. Conclude with `Ideal.ramificationIdx_eq_one P (𝓞 K)`.

Use `⟨?_, fun P hP => ?_⟩` and prove the remaining obligations. Take `⟨P⟩` from `(inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 M))) haveI := P.2.1 haveI := P.2.2`. Establish `h` using `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.asIdeal (𝓞 M) Gal(M/K)`. Rewrite `h` using `[Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal P.1 Gal(M/K), Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal P.1 Gal(M/K), he P.1 P.2, hf P.1 P.2, IsGalois.card_aut_eq_finrank]`. Simplify using `using h`.

Use `haveI := hP.1 haveI := hP.2`. Rewrite using `[← Ideal.absNorm_pow_inertiaDeg v.asIdeal P, hf P hP, pow_one]`.
-/
theorem exists_finite_ncard_primesOver_eq_finrank_of_pow_absNorm_sub_mem :
    ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
      [IsGalois K M], ∃ T : Set (HeightOneSpectrum (𝓞 K)), T.Finite ∧
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T →
        (∀ P ∈ v.asIdeal.primesOver (𝓞 M), ∀ x : 𝓞 M, x ^ Ideal.absNorm v.asIdeal - x ∈ P) →
        (v.asIdeal.primesOver (𝓞 M)).ncard = Module.finrank K M ∧
          ∀ P ∈ v.asIdeal.primesOver (𝓞 M), Ideal.absNorm P = Ideal.absNorm v.asIdeal := by
  intro K M _ _ _ _ _ _
  have hD : differentIdeal (𝓞 K) (𝓞 M) ≠ ⊥ := differentIdeal_ne_bot
  refine ⟨(fun P : HeightOneSpectrum (𝓞 M) => P.under (𝓞 K)) ''
    {P | P.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 M)}, (Ideal.finite_factors hD).image _, ?_⟩
  intro v hv hx
  haveI := v.isPrime
  have hq : 1 < Ideal.absNorm v.asIdeal := by
    have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
    omega
  have hf : ∀ P ∈ v.asIdeal.primesOver (𝓞 M), P.inertiaDeg (𝓞 K) = 1 := by
    intro P hP
    haveI := hP.1
    haveI := hP.2
    have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
    haveI : Finite (𝓞 M ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0
    have hle : Nat.card (𝓞 M ⧸ P) ≤ Ideal.absNorm v.asIdeal := by
      refine natCard_le_of_forall_pow_eq_self _ _ hq fun y => ?_
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [← map_pow, Ideal.Quotient.eq]
      exact hx P hP x
    have hN : Ideal.absNorm P = Nat.card (𝓞 M ⧸ P) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have h := Ideal.absNorm_pow_inertiaDeg v.asIdeal P
    rw [← hN, ← h] at hle
    have hpos : 0 < P.inertiaDeg (𝓞 K) := P.inertiaDeg_pos (𝓞 K)
    have h2 : P.inertiaDeg (𝓞 K) ≤ 1 := by
      rw [← Nat.pow_le_pow_iff_right hq, pow_one]; exact hle
    omega
  have he : ∀ P ∈ v.asIdeal.primesOver (𝓞 M), P.ramificationIdx (𝓞 K) = 1 := by
    intro P hP
    haveI := hP.1
    haveI := hP.2
    have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
    have hn : ¬ P ∣ differentIdeal (𝓞 K) (𝓞 M) := by
      intro hd
      refine hv ⟨⟨P, hP.1, hP0⟩, hd, ?_⟩
      ext1
      exact (Ideal.over_def P v.asIdeal).symm
    haveI : Algebra.IsUnramifiedAt (𝓞 K) P := not_dvd_differentIdeal_iff.1 hn
    exact Ideal.ramificationIdx_eq_one P (𝓞 K)
  refine ⟨?_, fun P hP => ?_⟩
  · obtain ⟨P⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 M)))
    haveI := P.2.1
    haveI := P.2.2
    have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.asIdeal (𝓞 M)
      Gal(M/K)
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal P.1 Gal(M/K),
      Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal P.1 Gal(M/K), he P.1 P.2, hf P.1 P.2,
      IsGalois.card_aut_eq_finrank] at h
    simpa using h
  · haveI := hP.1
    haveI := hP.2
    rw [← Ideal.absNorm_pow_inertiaDeg v.asIdeal P, hf P hP, pow_one]

end GlobalTheory
