import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Places

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V.Sd

/- English proof (translation)
Take `⟨hp, hspan, -, -⟩` from `UpperTheory.V.Af.Nf.places w`. Use `haveI : Fact (normV w).Prime := ⟨hp⟩`. Assume the negation of the conclusion as `h`. Establish `htop : w.asIdeal ⊔ 𝔪 = ⊤`. Assume the negation of the conclusion as `hne`.

Conclude with `h (le_sup_right.trans ((w.isMaximal.eq_of_le hne le_sup_left).symm.le))`. Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.mp (htop ▸ Submodule.mem_top : (1 : 𝓞 ℚ) ∈ w.asIdeal ⊔ 𝔪)`. Establish `hne : Ideal.absNorm 𝔪 ≠ 0` using `by rwa [Ne, Ideal.absNorm_eq_zero_iff]`. Rewrite `hd`, `hne` using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Use `haveI : Finite (𝓞 ℚ ⧸ 𝔪) := Nat.finite_of_card_ne_zero hne`.

Take `⟨y, hy⟩` from `exists_prime_addOrderOf_dvd_card' (G := 𝓞 ℚ ⧸ 𝔪) (normV w) hd`. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Establish `hpx : ((normV w : ℕ) : 𝓞 ℚ) * x ∈ 𝔪`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_natCast, ← nsmul_eq_mul, ← hy]`. Conclude with `addOrderOf_nsmul_eq_zero _`.

Establish `hx : x ∈ 𝔪`. Rewrite `ha` using `[hspan, Ideal.mem_span_singleton]`. Take `⟨c, rfl⟩` from `ha`. Establish `: x = c * (((normV w : ℕ) : 𝓞 ℚ) * x) + b * x`. Rewrite using `[← mul_assoc, mul_comm c, ← add_mul, hab, one_mul]`.

Rewrite using `[this]`. Conclude with `𝔪.add_mem (𝔪.mul_mem_left _ hpx) (𝔪.mul_mem_right _ hb)`. Establish `h0 : (Ideal.Quotient.mk 𝔪 x) = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr hx`. Rewrite `hy` using `[h0, addOrderOf_zero]`. Conclude with `hp.one_lt.ne hy`.
-/
private theorem le_asIdeal_of_normV_dvd_absNorm (w : Pl ℚ) (𝔪 : Ideal (𝓞 ℚ)) (h𝔪 : 𝔪 ≠ ⊥)
    (hd : normV w ∣ Ideal.absNorm 𝔪) : 𝔪 ≤ w.asIdeal := by
  obtain ⟨hp, hspan, -, -⟩ := UpperTheory.V.Af.Nf.places w
  haveI : Fact (normV w).Prime := ⟨hp⟩
  by_contra h
  have htop : w.asIdeal ⊔ 𝔪 = ⊤ := by
    by_contra hne
    exact h (le_sup_right.trans ((w.isMaximal.eq_of_le hne le_sup_left).symm.le))
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (htop ▸ Submodule.mem_top : (1 : 𝓞 ℚ) ∈ w.asIdeal ⊔ 𝔪)
  have hne : Ideal.absNorm 𝔪 ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hd hne
  haveI : Finite (𝓞 ℚ ⧸ 𝔪) := Nat.finite_of_card_ne_zero hne
  obtain ⟨y, hy⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 ℚ ⧸ 𝔪) (normV w) hd
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hpx : ((normV w : ℕ) : 𝓞 ℚ) * x ∈ 𝔪 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_natCast, ← nsmul_eq_mul, ← hy]
    exact addOrderOf_nsmul_eq_zero _
  have hx : x ∈ 𝔪 := by
    rw [hspan, Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    have : x = c * (((normV w : ℕ) : 𝓞 ℚ) * x) + b * x := by
      rw [← mul_assoc, mul_comm c, ← add_mul, hab, one_mul]
    rw [this]
    exact 𝔪.add_mem (𝔪.mul_mem_left _ hpx) (𝔪.mul_mem_right _ hb)
  have h0 : (Ideal.Quotient.mk 𝔪 x) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
  rw [h0, addOrderOf_zero] at hy
  exact hp.one_lt.ne hy

/- English proof (translation)
Take `⟨hp, -, hnorm, -⟩` from `UpperTheory.V.Af.Nf.places w`. Unfold `coefDiv`. Use `split_ifs with h1 h2 h2`. Establish `hc` using `h1.choose_spec`. Establish `habs : Ideal.absNorm 𝔪 = normV w * Ideal.absNorm h1.choose` using `by conv_lhs => rw [hc]`.

Rewrite using `[map_mul, hnorm]`. Simplify using `only [UpperTheory.V.Af.Nf.icoef]`. Rewrite using `[habs, Nat.mul_div_cancel_left _ hp.pos]`. It suffices to derive a contradiction. Apply `h2` to reduce the goal to its premises.

Take `⟨n, hn⟩` from `h1`. Rewrite using `[hn, map_mul, hnorm]`. Conclude with `dvd_mul_right _ _`. It suffices to derive a contradiction. Conclude with `h1 (Ideal.dvd_iff_le.mpr (le_asIdeal_of_normV_dvd_absNorm w 𝔪 h𝔪 h2))`.

Both sides reduce to the same expression.
-/
private theorem coefDiv_icoef_eq_ite_dvd (g : UpperHalfPlane → ℂ) (w : Pl ℚ) (𝔪 : Ideal (𝓞 ℚ)) (h𝔪 : 𝔪 ≠ ⊥) :
    coefDiv (UpperTheory.V.Af.Nf.icoef g) w.asIdeal 𝔪 =
      if normV w ∣ Ideal.absNorm 𝔪 then UpperTheory.V.Af.coef g (Ideal.absNorm 𝔪 / normV w) else 0 := by
  obtain ⟨hp, -, hnorm, -⟩ := UpperTheory.V.Af.Nf.places w
  unfold coefDiv
  split_ifs with h1 h2 h2
  · have hc := h1.choose_spec
    have habs : Ideal.absNorm 𝔪 = normV w * Ideal.absNorm h1.choose := by
      conv_lhs => rw [hc]
      rw [map_mul, hnorm]
    simp only [UpperTheory.V.Af.Nf.icoef]
    rw [habs, Nat.mul_div_cancel_left _ hp.pos]
  · exfalso
    apply h2
    obtain ⟨n, hn⟩ := h1
    rw [hn, map_mul, hnorm]
    exact dvd_mul_right _ _
  · exfalso
    exact h1 (Ideal.dvd_iff_le.mpr (le_asIdeal_of_normV_dvd_absNorm w 𝔪 h𝔪 h2))
  · rfl

/- English proof (translation)
Establish `hirr : ∀ v : Pl ℚ, Irreducible (Associates.mk v.asIdeal)` using `fun v => Associates.irreducible_mk.mpr v.irreducible`. Unfold `chiI`. Rewrite using `[finprod_eq_single _ w]`. Simplify using `only [hc, if_true]`. Unfold `ordI`.

Rewrite using `[Associates.count_self (hirr w), pow_one]`. Introduce `v hv`. Unfold `ordI`. Rewrite using `[Associates.count_eq_zero_of_ne (hirr v) (hirr w), pow_zero]`. Introduce `he`.

Apply `hv` to reduce the goal to its premises. Rewrite `he` using `[Associates.mk_eq_mk_iff_associated, associated_iff_eq]`. Conclude with `HeightOneSpectrum.ext he`.
-/
private theorem chiI_eq_of_conductor_eq_zero (ω : Formalism.L2.Host.HChar ℚ) (c : Pl ℚ → ℕ) (w : Pl ℚ) (hc : c w = 0) :
    chiI ω c w.asIdeal = ↑(ω.val w) := by
  classical
  have hirr : ∀ v : Pl ℚ, Irreducible (Associates.mk v.asIdeal) :=
    fun v => Associates.irreducible_mk.mpr v.irreducible
  unfold chiI
  rw [finprod_eq_single _ w]
  · simp only [hc, if_true]
    unfold ordI
    rw [Associates.count_self (hirr w), pow_one]
  · intro v hv
    unfold ordI
    rw [Associates.count_eq_zero_of_ne (hirr v) (hirr w), pow_zero]
    intro he
    apply hv
    rw [Associates.mk_eq_mk_iff_associated, associated_iff_eq] at he
    exact HeightOneSpectrum.ext he

/- English proof (translation)
Introduce `k f ω w hw hω 𝔪 h𝔪`. Take `⟨hp, -, hnorm, hlev⟩` from `UpperTheory.V.Af.Nf.places w`. Establish `hl : UpperTheory.V.Af.Nf.lev f.M w = 0` using `hlev f.M f.pos hw`. Establish `hn : 1 ≤ Ideal.absNorm 𝔪` using `Nat.one_le_iff_ne_zero.mpr (by rwa [Ne, Ideal.absNorm_eq_zero_iff])`. Establish `heig` using `f.eig (normV w) hp hw (Ideal.absNorm 𝔪) hn`.

Unfold `UpperTheory.V.Sd.hkCoef`. Rewrite using `[chiI_eq_of_conductor_eq_zero ω _ w hl, coefDiv_icoef_eq_ite_dvd _ w 𝔪 h𝔪, hω]`. Simplify using `only [UpperTheory.V.Af.Nf.icoef, map_mul, hnorm, UpperTheory.V.Af.Newform.a]`. Conclude with `heig`.
-/
theorem UpperTheory.V.Af.Nf.hkCoef :
    UpperTheory.V.Af.Nf.HkCoef := by
  intro k f ω w hw hω 𝔪 h𝔪
  obtain ⟨hp, -, hnorm, hlev⟩ := UpperTheory.V.Af.Nf.places w
  have hl : UpperTheory.V.Af.Nf.lev f.M w = 0 := hlev f.M f.pos hw
  have hn : 1 ≤ Ideal.absNorm 𝔪 := Nat.one_le_iff_ne_zero.mpr (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  have heig := f.eig (normV w) hp hw (Ideal.absNorm 𝔪) hn
  unfold UpperTheory.V.Sd.hkCoef
  rw [chiI_eq_of_conductor_eq_zero ω _ w hl, coefDiv_icoef_eq_ite_dvd _ w 𝔪 h𝔪, hω]
  simp only [UpperTheory.V.Af.Nf.icoef, map_mul, hnorm, UpperTheory.V.Af.Newform.a]
  exact heig
