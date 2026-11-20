import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero

open NumberField

namespace GlobalTheory.ConjugateMultiplicity

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

/- English proof (translation)
Establish `hsq` using `H.sqrt_neg_disc_sq`. Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Establish `hre` using `congrArg Complex.re hsq`. Establish `him` using `congrArg Complex.im hsq`. Simplify using `only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him`.

Establish `h0 : H.rt0.re = 0`. Assume the negation of the conclusion as `hne`. Establish `hprod : H.rt0.re * H.rt0.im = 0` using `by linarith [mul_comm H.rt0.re H.rt0.im]`. Establish `him0 : H.rt0.im = 0` using `(mul_eq_zero.1 hprod).resolve_left hne`. Rewrite `hre` using `[him0]`.

Use polynomial arithmetic with `[sq_nonneg H.rt0.re]`. Apply the tactic sequence `apply Complex.ext <;> simp [h0]`.
-/
theorem rt0_conj_neg_ne_zero (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by

  have hsq := H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre := congrArg Complex.re hsq
  have him := congrArg Complex.im hsq
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
    Complex.natCast_im, neg_zero] at hre him
  have h0 : H.rt0.re = 0 := by
    by_contra hne
    have hprod : H.rt0.re * H.rt0.im = 0 := by linarith [mul_comm H.rt0.re H.rt0.im]
    have him0 : H.rt0.im = 0 := (mul_eq_zero.1 hprod).resolve_left hne
    rw [him0] at hre
    nlinarith [sq_nonneg H.rt0.re]
  apply Complex.ext <;> simp [h0]

/- English proof (translation)
Establish `h : (H.rt : E) ^ 2 = -(H.d : E)`. Establish `h'` using `congrArg ((↑) : 𝓞 E → E) H.rt_sq`. Move the coercions through the operations in `at h'`. Conclude with `h'`. Rewrite using `[← map_pow, h, map_neg, map_natCast, H.sqrt_neg_disc_sq]`.
-/
theorem emb_rt_sq (H : Host E) (τ : E →+* ℂ) : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
  have h : (H.rt : E) ^ 2 = -(H.d : E) := by
    have h' := congrArg ((↑) : 𝓞 E → E) H.rt_sq
    push_cast at h'
    exact h'
  rw [← map_pow, h, map_neg, map_natCast, H.sqrt_neg_disc_sq]

/- English proof (translation)
Establish `hne : H.rt0 ≠ -H.rt0`. Introduce `h`. Establish `h0 : H.rt0 = 0` using `by linear_combination h / 2`. Establish `hsq` using `H.sqrt_neg_disc_sq`. Rewrite `hsq` using `[h0]`.

Establish `hd : (H.d : ℂ) ≠ 0` using `by exact_mod_cast H.d_prime.ne_zero`. Conclude with `hd (by linear_combination hsq)`. Establish `hc : conjEmb τ (H.rt : E) = starRingEnd ℂ (τ (H.rt : E))` using `rfl`. Unfold `Datum.mult`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 (emb_rt_sq H τ) with h | h` into its components or cases.

Establish `h2 : ¬ conjEmb τ (H.rt : E) = H.rt0`. Rewrite using `[hc, h, rt0_conj_neg_ne_zero]`. Conclude with `fun e => hne e.symm`. Rewrite using `[if_pos h, if_neg h2]`. Establish `h2 : conjEmb τ (H.rt : E) = H.rt0`.

Rewrite using `[hc, h, map_neg, rt0_conj_neg_ne_zero, neg_neg]`. Establish `h3 : ¬ τ (H.rt : E) = H.rt0`. Rewrite using `[h]`. Conclude with `fun e => hne e.symm`. Rewrite using `[if_pos h2, if_neg h3]`.
-/
private theorem mult_conjEmb_eq_ite {H : Host E} (D : Datum H) (τ : E →+* ℂ) :
    Datum.mult D (conjEmb τ) = if τ (H.rt : E) = H.rt0 then Datum.q D else Datum.p D := by

  have hne : H.rt0 ≠ -H.rt0 := by
    intro h
    have h0 : H.rt0 = 0 := by linear_combination h / 2
    have hsq := H.sqrt_neg_disc_sq
    rw [h0] at hsq
    have hd : (H.d : ℂ) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
    exact hd (by linear_combination hsq)
  have hc : conjEmb τ (H.rt : E) = starRingEnd ℂ (τ (H.rt : E)) := rfl
  unfold Datum.mult

  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (emb_rt_sq H τ) with h | h
  · have h2 : ¬ conjEmb τ (H.rt : E) = H.rt0 := by
      rw [hc, h, rt0_conj_neg_ne_zero]
      exact fun e => hne e.symm
    rw [if_pos h, if_neg h2]
  · have h2 : conjEmb τ (H.rt : E) = H.rt0 := by
      rw [hc, h, map_neg, rt0_conj_neg_ne_zero, neg_neg]
    have h3 : ¬ τ (H.rt : E) = H.rt0 := by
      rw [h]
      exact fun e => hne e.symm
    rw [if_pos h2, if_neg h3]

/- English proof (translation)
Rewrite using `[mult_conjEmb_eq_ite]`. Unfold `Datum.mult`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem main {H : Host E} (D : Datum H) (τ : E →+* ℂ) :
    Datum.mult D (conjEmb τ) + Datum.mult D τ = Datum.p D + Datum.q D := by
  rw [mult_conjEmb_eq_ite]
  unfold Datum.mult
  split_ifs <;> omega

end GlobalTheory.ConjugateMultiplicity

/- English proof (translation)
Introduce `E _ _ _ H D τ`. Rewrite using `[GlobalTheory.ConjugateMultiplicity.mult_conjEmb_eq_ite]`. Unfold `ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem GlobalTheory.ConjugateMultiplicity.target : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (D : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (τ : E →+* ℂ), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult D (ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ) + ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult D τ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.p D + ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.q D := by
  intro E _ _ _ H D τ
  rw [GlobalTheory.ConjugateMultiplicity.mult_conjEmb_eq_ite]
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult
  split_ifs <;> omega
