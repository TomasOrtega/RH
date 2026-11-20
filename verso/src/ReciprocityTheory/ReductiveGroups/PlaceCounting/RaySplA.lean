import Mathlib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.N2

open NumberField IsDedekindDomain

/- English proof (translation)
Use `haveI := Fact.mk hp`. Use `set P : Ideal ℤ := Ideal.span {(p : ℤ)} with hPdef`. Use `haveI hPmax : P.IsMaximal := Int.ideal_span_isMaximal_of_prime p`. Establish `hP0 : P ≠ ⊥`. Rewrite using `[hPdef, Ne, Ideal.span_singleton_eq_bot]`.

Conclude with `hp.ne_zero` after adjusting the coercions. Use `haveI : Fintype (P.primesOver (𝓞 E)) := by`. Rewrite using `[← IsDedekindDomain.coe_primesOverFinset hP0 (𝓞 E)]`. Use `infer_instance`. Establish `hsum : ∑ q : P.primesOver (𝓞 E), (q : Ideal (𝓞 E)).ramificationIdx ℤ * (q : Ideal (𝓞 E)).inertiaDeg ℤ = Module.finrank ℚ E`.

Rewrite using `[Ideal.sum_ramification_inertia_eq_finrank P (𝓞 E), NumberField.RingOfIntegers.rank]`. Establish `hiff : ∀ w : HeightOneSpectrum (𝓞 E), ((p : ℕ) : 𝓞 E) ∈ w.asIdeal ↔ w.asIdeal ∣ Ideal.map (algebraMap ℤ (𝓞 E)) P`. Introduce `w`. Rewrite using `[Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, hPdef, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]`. Simplify using the standard rewrite rules.

Set `eqv` to `(Equiv.subtypeEquivRight hiff).trans (IsDedekindDomain.HeightOneSpectrum.equivPrimesOver (𝓞 E) hP0)`. Establish `hS : {w : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ w.asIdeal}.ncard = Fintype.card (P.primesOver (𝓞 E))`. Rewrite using `[← Nat.card_coe_set_eq, ← Nat.card_eq_fintype_card]`. Conclude with `Nat.card_congr eqv`. Establish `hpos : ∀ q : P.primesOver (𝓞 E), 1 ≤ (q : Ideal (𝓞 E)).ramificationIdx ℤ * (q : Ideal (𝓞 E)).inertiaDeg ℤ`.

Introduce `q`. Use `haveI := Ideal.primesOver.isPrime P q`. Conclude with `Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Ideal.ramificationIdx_pos _ ℤ).ne' (Ideal.inertiaDeg_pos _ ℤ).ne')`. Establish `hcard : Fintype.card (P.primesOver (𝓞 E)) = ∑ _q : P.primesOver (𝓞 E), 1` using `by simp`. Establish `heqv : ∀ W : HeightOneSpectrum (𝓞 E), ∀ hW : ((p : ℕ) : 𝓞 E) ∈ W.asIdeal, ((eqv ⟨W, hW⟩ : P.primesOver (𝓞 E)) : Ideal (𝓞 E)) = W.asIdeal`.

Introduce `W hW`. Simplify using `[eqv, IsDedekindDomain.HeightOneSpectrum.equivPrimesOver_apply]`. Rewrite using `[hS, ← hsum, hcard]`. Prove the components needed by the constructor for the conclusion. Introduce `h W hW`.

Establish `hall` using `(Finset.sum_eq_sum_iff_of_le (fun q _ => hpos q)).1 h`. Establish `h1` using `hall (eqv ⟨W, hW⟩) (Finset.mem_univ _)`. Rewrite `h1` using `[heqv W hW]`. Conclude with `mul_eq_one.1 h1.symm`. Introduce `h`.

Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Take `⟨⟨W, hW⟩, rfl⟩` from `eqv.surjective q`. Rewrite using `[heqv W hW]`. Take `⟨h1, h2⟩` from `h W hW`. Rewrite using `[h1, h2]`.
-/
theorem ncard_places_eq_finrank_iff (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime) :
    {w : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ w.asIdeal}.ncard = Module.finrank ℚ E ↔
      ∀ W : HeightOneSpectrum (𝓞 E), ((p : ℕ) : 𝓞 E) ∈ W.asIdeal →
        W.asIdeal.ramificationIdx ℤ = 1 ∧ W.asIdeal.inertiaDeg ℤ = 1 := by
  classical
  haveI := Fact.mk hp
  set P : Ideal ℤ := Ideal.span {(p : ℤ)} with hPdef
  haveI hPmax : P.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hP0 : P ≠ ⊥ := by
    rw [hPdef, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  haveI : Fintype (P.primesOver (𝓞 E)) := by
    rw [← IsDedekindDomain.coe_primesOverFinset hP0 (𝓞 E)]
    infer_instance
  have hsum : ∑ q : P.primesOver (𝓞 E), (q : Ideal (𝓞 E)).ramificationIdx ℤ * (q : Ideal (𝓞 E)).inertiaDeg ℤ =
      Module.finrank ℚ E := by
    rw [Ideal.sum_ramification_inertia_eq_finrank P (𝓞 E), NumberField.RingOfIntegers.rank]
  have hiff : ∀ w : HeightOneSpectrum (𝓞 E),
      ((p : ℕ) : 𝓞 E) ∈ w.asIdeal ↔ w.asIdeal ∣ Ideal.map (algebraMap ℤ (𝓞 E)) P := by
    intro w
    rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, hPdef, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    simp
  let eqv := (Equiv.subtypeEquivRight hiff).trans (IsDedekindDomain.HeightOneSpectrum.equivPrimesOver (𝓞 E) hP0)
  have hS : {w : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ w.asIdeal}.ncard = Fintype.card (P.primesOver (𝓞 E)) := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr eqv
  have hpos : ∀ q : P.primesOver (𝓞 E),
      1 ≤ (q : Ideal (𝓞 E)).ramificationIdx ℤ * (q : Ideal (𝓞 E)).inertiaDeg ℤ := by
    intro q
    haveI := Ideal.primesOver.isPrime P q
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Ideal.ramificationIdx_pos _ ℤ).ne' (Ideal.inertiaDeg_pos _ ℤ).ne')
  have hcard : Fintype.card (P.primesOver (𝓞 E)) = ∑ _q : P.primesOver (𝓞 E), 1 := by simp
  have heqv : ∀ W : HeightOneSpectrum (𝓞 E), ∀ hW : ((p : ℕ) : 𝓞 E) ∈ W.asIdeal,
      ((eqv ⟨W, hW⟩ : P.primesOver (𝓞 E)) : Ideal (𝓞 E)) = W.asIdeal := by
    intro W hW
    simp [eqv, IsDedekindDomain.HeightOneSpectrum.equivPrimesOver_apply]
  rw [hS, ← hsum, hcard]
  constructor
  · intro h W hW
    have hall := (Finset.sum_eq_sum_iff_of_le (fun q _ => hpos q)).1 h
    have h1 := hall (eqv ⟨W, hW⟩) (Finset.mem_univ _)
    rw [heqv W hW] at h1
    exact mul_eq_one.1 h1.symm
  · intro h
    refine Finset.sum_congr rfl fun q _ => ?_
    obtain ⟨⟨W, hW⟩, rfl⟩ := eqv.surjective q
    rw [heqv W hW]
    obtain ⟨h1, h2⟩ := h W hW
    rw [h1, h2]

end ReciprocityTheory.ChartRestriction.N2
