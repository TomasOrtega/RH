import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormPrimeIffInertiaDegEqOneAndFiniteRamified

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual

namespace GlobalTheory.FrobDense

/- English proof (translation)
Introduce `h`. Establish `h1` using `congrArg Complex.im h`. Establish `: 0 < Real.sqrt H.d` using `Real.sqrt_pos.2 (by exact_mod_cast H.hyp.2.1.pos)`. Simplify using `at h1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem conj_ne {R : Ranks} (H : Host R) :
    starRingEnd ℂ (Complex.I * (Real.sqrt H.d : ℂ)) ≠ Complex.I * (Real.sqrt H.d : ℂ) := by
  intro h
  have h1 := congrArg Complex.im h
  have : 0 < Real.sqrt H.d := Real.sqrt_pos.2 (by exact_mod_cast H.hyp.2.1.pos)
  simp at h1
  linarith

/- English proof (translation)
Establish `h0 : (Complex.I * (Real.sqrt H.d : ℂ)) ^ 2 = -(H.d : ℂ)`. Rewrite using `[mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]`. Simplify using the standard rewrite rules. Establish `h3 : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ)` using `H.φ₀_mem`. Apply `H.φ₀.injective` to reduce the goal to its premises.

Rewrite using `[map_pow, h3, h0]`. Simplify using the standard rewrite rules.
-/
theorem sqrt_sq {R : Ranks} (H : Host R) : H.sqrtMinusD ^ 2 = -(H.d : H.E) := by
  have h0 : (Complex.I * (Real.sqrt H.d : ℂ)) ^ 2 = -(H.d : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have h3 : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem
  apply H.φ₀.injective
  rw [map_pow, h3, h0]
  simp

/- English proof (translation)
Establish `hint : IsIntegral ℤ H.sqrtMinusD`. Apply `IsIntegral.of_pow (n := 2) (by norm_num)` to reduce the goal to its premises. Rewrite using `[sqrt_sq]`. Use `(isIntegral_algebraMap (R := ℤ) (A := H.E) (x := (H.d : ℤ))).neg` as an intermediate fact. Simplify using `using this`.

Set `c : 𝓞 H.E →+* 𝓞 H.E` to `RingOfIntegers.mapRingHom (H.conj : H.E →+* H.E)`. Set `b : 𝓞 H.E` to `⟨_, hint⟩`. Establish `hb : c b - b ≠ 0`. Introduce `h`. Establish `h1 : H.conj H.sqrtMinusD = H.sqrtMinusD` using `congrArg (fun y : 𝓞 H.E => (y : H.E)) (sub_eq_zero.1 h)`.

Establish `h2` using `H.conjE_apply H.φ₀ H.sqrtMinusD`. Establish `h3 : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ)` using `H.φ₀_mem`. Establish `h4 : H.φ₀ (H.conj H.sqrtMinusD) = starRingEnd ℂ (H.φ₀ H.sqrtMinusD)` using `h2`. Rewrite `h4` using `[h1, h3]`. Conclude with `conj_ne H h4.symm`.

Use `⟨{v | v.asIdeal ∣ Ideal.span {c b - b}}, Ideal.finite_factors (by simpa [Ideal.span_singleton_eq_bot] using hb), fun v hv hd => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hs`. Apply `hv` to reduce the goal to its premises. Establish `hp` using `((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified H.E).1 v).2 hd`. Establish `hst : ∀ x ∈ v.asIdeal, c x ∈ v.asIdeal`.

Introduce `x hx`. Assume the negation of the conclusion as `hx'`. Use `hs ⟨x, hx, fun y hy => ?_⟩` and prove the remaining obligations. Establish `: y = c x` using `RingOfIntegers.ext hy`. Rewrite using `[this]` and apply the resulting hypothesis.

Establish `: Fact (Ideal.absNorm v.asIdeal).Prime` using `⟨hp⟩`. Establish `hcard : Nat.card (𝓞 H.E ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal` using `rfl`. Use `v.isPrime` as an intermediate fact. Establish `htop : AddSubgroup.zmultiples (1 : 𝓞 H.E ⧸ v.asIdeal) = ⊤` using `zmultiples_eq_top_of_prime_card hcard one_ne_zero`. Establish `hmem : Ideal.Quotient.mk v.asIdeal b ∈ AddSubgroup.zmultiples (1 : 𝓞 H.E ⧸ v.asIdeal)`.

Rewrite using `[htop]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨n, hn⟩` from `AddSubgroup.mem_zmultiples_iff.1 hmem`. Establish `h1 : b - (n : 𝓞 H.E) ∈ v.asIdeal`. Rewrite using `[← Ideal.Quotient.eq, ← hn]`.

Simplify using the standard rewrite rules. Establish `h2` using `hst _ h1`. Rewrite `h2` using `[map_sub, map_intCast]`. Use `show v.asIdeal ∣ _`. Rewrite using `[Ideal.dvd_span_singleton]`.

Use `v.asIdeal.sub_mem h2 h1` as an intermediate fact. Simplify using `using this`.
-/
theorem exists_finite_split {R : Ranks} (H : Host R) :
    ∃ A : Set (HeightOneSpectrum (𝓞 H.E)), A.Finite ∧
    ∀ v, v ∉ A → v.asIdeal.inertiaDeg ℤ = 1 → IsSplitPl H v := by
  have hint : IsIntegral ℤ H.sqrtMinusD := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [sqrt_sq]
    have := (isIntegral_algebraMap (R := ℤ) (A := H.E) (x := (H.d : ℤ))).neg
    simpa using this
  let c : 𝓞 H.E →+* 𝓞 H.E := RingOfIntegers.mapRingHom (H.conj : H.E →+* H.E)
  let b : 𝓞 H.E := ⟨_, hint⟩
  have hb : c b - b ≠ 0 := by
    intro h
    have h1 : H.conj H.sqrtMinusD = H.sqrtMinusD := congrArg (fun y : 𝓞 H.E => (y : H.E)) (sub_eq_zero.1 h)
    have h2 := H.conjE_apply H.φ₀ H.sqrtMinusD
    have h3 : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem
    have h4 : H.φ₀ (H.conj H.sqrtMinusD) = starRingEnd ℂ (H.φ₀ H.sqrtMinusD) := h2
    rw [h1, h3] at h4
    exact conj_ne H h4.symm
  refine ⟨{v | v.asIdeal ∣ Ideal.span {c b - b}},
    Ideal.finite_factors (by simpa [Ideal.span_singleton_eq_bot] using hb), fun v hv hd => ?_⟩
  by_contra hs
  apply hv
  have hp := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified H.E).1 v).2 hd
  have hst : ∀ x ∈ v.asIdeal, c x ∈ v.asIdeal := by
    intro x hx
    by_contra hx'
    refine hs ⟨x, hx, fun y hy => ?_⟩
    have : y = c x := RingOfIntegers.ext hy
    rwa [this]
  have : Fact (Ideal.absNorm v.asIdeal).Prime := ⟨hp⟩
  have hcard : Nat.card (𝓞 H.E ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := rfl
  have := v.isPrime
  have htop : AddSubgroup.zmultiples (1 : 𝓞 H.E ⧸ v.asIdeal) = ⊤ :=
    zmultiples_eq_top_of_prime_card hcard one_ne_zero
  have hmem : Ideal.Quotient.mk v.asIdeal b ∈ AddSubgroup.zmultiples (1 : 𝓞 H.E ⧸ v.asIdeal) := by
    rw [htop]; trivial
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 hmem
  have h1 : b - (n : 𝓞 H.E) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq, ← hn]; simp
  have h2 := hst _ h1
  rw [map_sub, map_intCast] at h2
  show v.asIdeal ∣ _
  rw [Ideal.dvd_span_singleton]
  have := v.asIdeal.sub_mem h2 h1
  simpa using this

/- English proof (translation)
Rewrite using `[dense_iff_inter_open]`. Introduce and unpack `W hW ⟨g, hg⟩`. Establish `hV : IsOpen {s : G H.E N.Om | s * g ∈ W}` using `hW.preimage (continuous_mul_const g)`. Establish `: IsGalois H.E N.Om` using `{}`. Take `⟨U, hU⟩` from `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hV (by simpa using hg)`.

Take `⟨A, hA, hsp⟩` from `exists_finite_split H`. Establish `hl : (placesOver H.E (N.l i)).Finite`. Establish `h0 : ((N.l i : ℕ) : 𝓞 H.E) ≠ 0` using `Nat.cast_ne_zero.2 (N.lPrime i).out.ne_zero`. Use `(Ideal.finite_factors (I := Ideal.span {((N.l i : ℕ) : 𝓞 H.E)}) (by simpa [Ideal.span_singleton_eq_bot] using h0)).subset fun v hv => ?_` and prove the remaining obligations. Conclude with `Ideal.dvd_span_singleton.2 hv`.

Take `⟨v, hv, hd, -, B, hB, -, σ, hσ, hU'⟩` from `hC H.E N.Om U.toSubgroup U.isOpen U.isNormal' g (hA.toFinset ∪ hl.toFinset ∪ N.S i ∪ N.Q i)`. Simplify using `only [Finset.mem_union, Set.Finite.mem_toFinset, not_or] at hv`. Use `hU hU'` as an intermediate fact. Simplify using `only [Set.mem_ofPred_eq, inv_mul_cancel_right] at this`. Conclude with `⟨σ, this, v, ⟨hsp v hv.1.1.1 hd, hv.1.1.2, hv.1.2, hv.2⟩, B, hB, hσ⟩`.
-/
theorem dense_frob (hC : GlobalTheory.TwSys.Cheb) {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (i : N.Loc) : Dense {σ : GE N | ∃ w, SplitOut N i w ∧ ∃ B : ValuationSubring N.Om,
      Formalism.ConjugateSelfDual.IsPlaceOver (F := H.E) B w ∧ Formalism.ConjugateSelfDual.IsFrob (F := H.E) B (Formalism.ConjugateSelfDual.normV w) σ} := by
  classical
  rw [dense_iff_inter_open]
  rintro W hW ⟨g, hg⟩
  have hV : IsOpen {s : G H.E N.Om | s * g ∈ W} := hW.preimage (continuous_mul_const g)
  have : IsGalois H.E N.Om := {}
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hV (by simpa using hg)
  obtain ⟨A, hA, hsp⟩ := exists_finite_split H
  have hl : (placesOver H.E (N.l i)).Finite := by
    have h0 : ((N.l i : ℕ) : 𝓞 H.E) ≠ 0 := Nat.cast_ne_zero.2 (N.lPrime i).out.ne_zero
    refine (Ideal.finite_factors (I := Ideal.span {((N.l i : ℕ) : 𝓞 H.E)})
      (by simpa [Ideal.span_singleton_eq_bot] using h0)).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  obtain ⟨v, hv, hd, -, B, hB, -, σ, hσ, hU'⟩ := hC H.E N.Om U.toSubgroup U.isOpen U.isNormal' g
    (hA.toFinset ∪ hl.toFinset ∪ N.S i ∪ N.Q i)
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, not_or] at hv
  have := hU hU'
  simp only [Set.mem_ofPred_eq, inv_mul_cancel_right] at this
  exact ⟨σ, this, v, ⟨hsp v hv.1.1.1 hd, hv.1.1.2, hv.1.2, hv.2⟩, B, hB, hσ⟩

end GlobalTheory.FrobDense
