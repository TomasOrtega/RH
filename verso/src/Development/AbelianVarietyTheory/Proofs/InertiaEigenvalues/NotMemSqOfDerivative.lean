import Mathlib
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.UnramSimpleGen

/- English proof (translation)
Introduce `E E' _ _ _ _ _ p P β f _ hβ hadj hPp hder c hc`. Establish `hmem` using `aeval_derivative_mem_differentIdeal (𝓞 E) E E' β hadj`. Establish `hint : IsIntegral (𝓞 E) β` using `Algebra.IsIntegral.isIntegral β`. Establish `hdvd : minpoly (𝓞 E) β ∣ f.map (algebraMap ℤ (𝓞 E))` using `minpoly.isIntegrallyClosed_dvd hint (by rw [aeval_map_algebraMap]; exact hβ)`. Take `⟨k, hk⟩` from `hdvd`.

Establish `hfd : aeval β (derivative f) = aeval β (derivative (minpoly (𝓞 E) β)) * aeval β k`. Establish `h` using `congrArg (fun q => aeval β (derivative q)) hk`. Simplify using `only [derivative_mul, map_add, map_mul, minpoly.aeval, zero_mul, add_zero] at h`. Rewrite using `[← h, derivative_map, aeval_map_algebraMap]`. Establish `hnd : ¬ P.asIdeal ∣ differentIdeal (𝓞 E) (𝓞 E')`.

Introduce `h`. Apply `hder` to reduce the goal to its premises. Rewrite using `[hfd]`. Conclude with `Ideal.mul_mem_right _ _ ((Ideal.dvd_iff_le.1 h) hmem)`. Use `haveI := p.isMaximal`.

Establish `hnle : ¬ p.asIdeal.map (algebraMap (𝓞 E) (𝓞 E')) ≤ P.asIdeal ^ 2`. Introduce `hle`. Establish `h` using `pow_sub_one_dvd_differentIdeal (𝓞 E) (p := p.asIdeal) P.asIdeal 2 p.ne_bot (Ideal.dvd_iff_le.2 hle)`. Conclude with `hnd (by simpa using h)`. Distinguish the cases in `hcp : c ∈ p.asIdeal`.

Use `swap`. Introduce `h`. Conclude with `hcp ((hPp c).1 (Ideal.pow_le_self two_ne_zero h))`. Take `⟨J, hJ⟩ : p.asIdeal ∣ Ideal.span {c}` from `Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hcp)`. Establish `hJp : ¬ J ≤ p.asIdeal`.

Introduce `h`. Apply `hc` to reduce the goal to its premises. Establish `h1 : Ideal.span {c} ≤ p.asIdeal ^ 2`. Rewrite using `[hJ, pow_two]`. Conclude with `Ideal.mul_mono_right h`.

Conclude with `h1 (Ideal.mem_span_singleton_self c)`. Take `⟨s, hsJ, hsp⟩` from `Set.not_subset.1 hJp`. Establish `hps : p.asIdeal * Ideal.span {s} ≤ Ideal.span {c}`. Rewrite using `[hJ]`. Conclude with `Ideal.mul_mono_right ((Ideal.span_singleton_le_iff_mem _).2 hsJ)`.

Introduce `hcP`. Apply `hnle` to reduce the goal to its premises. Establish `hs' : algebraMap (𝓞 E) (𝓞 E') s ∉ P.asIdeal` using `fun h => hsp ((hPp s).1 h)`. Establish `hcop : IsCoprime P.asIdeal (Ideal.span {algebraMap (𝓞 E) (𝓞 E') s})`. Rewrite using `[Ideal.isCoprime_iff_sup_eq]`.

Use `P.isMaximal.1.2 _ (lt_of_le_of_ne le_sup_left fun h => hs' ?_)` and prove the remaining obligations. Rewrite using `[h]`. Conclude with `Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)`. Establish `hdiv : P.asIdeal ^ 2 ∣ p.asIdeal.map (algebraMap (𝓞 E) (𝓞 E')) * Ideal.span {algebraMap (𝓞 E) (𝓞 E') s}`. Rewrite using `[Ideal.dvd_iff_le]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Ideal.map_mul, Ideal.map_span, Set.image_singleton]`. Use `_ ≤ (Ideal.span {c}).map (algebraMap (𝓞 E) (𝓞 E')) := Ideal.map_mono hps`. Use `_ = Ideal.span {algebraMap (𝓞 E) (𝓞 E') c} := by rw [Ideal.map_span, Set.image_singleton]`. Use `_ ≤ P.asIdeal ^ 2 := (Ideal.span_singleton_le_iff_mem _).2 hcP`.

Conclude with `Ideal.dvd_iff_le.1 ((hcop.pow_left).dvd_of_dvd_mul_right hdiv)`.
-/
theorem not_mem_sq_of_derivative : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (p : HeightOneSpectrum (𝓞 E)) (P : HeightOneSpectrum (𝓞 E')) (β : 𝓞 E') (f : Polynomial ℤ),
    f.Monic → Polynomial.aeval β f = 0 → Algebra.adjoin E {(β : E')} = ⊤ →
    (∀ x : 𝓞 E, algebraMap (𝓞 E) (𝓞 E') x ∈ P.asIdeal ↔ x ∈ p.asIdeal) →
    Polynomial.aeval β (Polynomial.derivative f) ∉ P.asIdeal →
    ∀ c : 𝓞 E, c ∉ p.asIdeal ^ 2 → algebraMap (𝓞 E) (𝓞 E') c ∉ P.asIdeal ^ 2 := by
  intro E E' _ _ _ _ _ p P β f _ hβ hadj hPp hder c hc

  have hmem := aeval_derivative_mem_differentIdeal (𝓞 E) E E' β hadj
  have hint : IsIntegral (𝓞 E) β := Algebra.IsIntegral.isIntegral β
  have hdvd : minpoly (𝓞 E) β ∣ f.map (algebraMap ℤ (𝓞 E)) :=
    minpoly.isIntegrallyClosed_dvd hint (by rw [aeval_map_algebraMap]; exact hβ)
  obtain ⟨k, hk⟩ := hdvd
  have hfd : aeval β (derivative f) = aeval β (derivative (minpoly (𝓞 E) β)) * aeval β k := by
    have h := congrArg (fun q => aeval β (derivative q)) hk
    simp only [derivative_mul, map_add, map_mul, minpoly.aeval, zero_mul, add_zero] at h
    rw [← h, derivative_map, aeval_map_algebraMap]
  have hnd : ¬ P.asIdeal ∣ differentIdeal (𝓞 E) (𝓞 E') := by
    intro h
    apply hder
    rw [hfd]
    exact Ideal.mul_mem_right _ _ ((Ideal.dvd_iff_le.1 h) hmem)

  haveI := p.isMaximal
  have hnle : ¬ p.asIdeal.map (algebraMap (𝓞 E) (𝓞 E')) ≤ P.asIdeal ^ 2 := by
    intro hle
    have h := pow_sub_one_dvd_differentIdeal (𝓞 E) (p := p.asIdeal) P.asIdeal 2 p.ne_bot
      (Ideal.dvd_iff_le.2 hle)
    exact hnd (by simpa using h)

  by_cases hcp : c ∈ p.asIdeal
  swap
  · intro h
    exact hcp ((hPp c).1 (Ideal.pow_le_self two_ne_zero h))

  obtain ⟨J, hJ⟩ : p.asIdeal ∣ Ideal.span {c} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hcp)
  have hJp : ¬ J ≤ p.asIdeal := by
    intro h
    apply hc
    have h1 : Ideal.span {c} ≤ p.asIdeal ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right h
    exact h1 (Ideal.mem_span_singleton_self c)
  obtain ⟨s, hsJ, hsp⟩ := Set.not_subset.1 hJp
  have hps : p.asIdeal * Ideal.span {s} ≤ Ideal.span {c} := by
    rw [hJ]; exact Ideal.mul_mono_right ((Ideal.span_singleton_le_iff_mem _).2 hsJ)
  intro hcP
  apply hnle
  have hs' : algebraMap (𝓞 E) (𝓞 E') s ∉ P.asIdeal := fun h => hsp ((hPp s).1 h)
  have hcop : IsCoprime P.asIdeal (Ideal.span {algebraMap (𝓞 E) (𝓞 E') s}) := by
    rw [Ideal.isCoprime_iff_sup_eq]
    refine P.isMaximal.1.2 _ (lt_of_le_of_ne le_sup_left fun h => hs' ?_)
    rw [h]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hdiv : P.asIdeal ^ 2 ∣ p.asIdeal.map (algebraMap (𝓞 E) (𝓞 E')) *
      Ideal.span {algebraMap (𝓞 E) (𝓞 E') s} := by
    rw [Ideal.dvd_iff_le]
    calc p.asIdeal.map (algebraMap (𝓞 E) (𝓞 E')) * Ideal.span {algebraMap (𝓞 E) (𝓞 E') s}
        = (p.asIdeal * Ideal.span {s}).map (algebraMap (𝓞 E) (𝓞 E')) := by
          rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton]
      _ ≤ (Ideal.span {c}).map (algebraMap (𝓞 E) (𝓞 E')) := Ideal.map_mono hps
      _ = Ideal.span {algebraMap (𝓞 E) (𝓞 E') c} := by rw [Ideal.map_span, Set.image_singleton]
      _ ≤ P.asIdeal ^ 2 := (Ideal.span_singleton_le_iff_mem _).2 hcP
  exact Ideal.dvd_iff_le.1 ((hcop.pow_left).dvd_of_dvd_mul_right hdiv)

end GlobalTheory.UnramSimpleGen
