import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.FrIntGOfDelta
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.ValOneOfNotMem

noncomputable section

namespace PI.CntNotIntW

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel

variable {D : Formalism.BasicNotions.D7}

/- English proof (translation)
Unfold `Loc.resChar`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`. Conclude with `ringChar.Nat.cast_ringChar`.
-/
theorem ell_mem (p : PlF D) : ((Loc.resChar p : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal := by
  unfold Loc.resChar
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

/- English proof (translation)
Rewrite using `[← (D.s.atP p).val x y]`. Conclude with `(Valuation.Compatible.vle_iff_le (v := valuation (D.s.atP p).Fp) _ _).symm`.
-/
theorem vle_iff (p : PlF D) (x y : D.host.F) :
    valuation (D.s.atP p).Fp ((D.s.atP p).ιF x) ≤ valuation (D.s.atP p).Fp ((D.s.atP p).ιF y) ↔
      p.valuation D.host.F x ≤ p.valuation D.host.F y := by
  rw [← (D.s.atP p).val x y]
  exact (Valuation.Compatible.vle_iff_le (v := valuation (D.s.atP p).Fp) _ _).symm

/- English proof (translation)
Establish `h1 : p.valuation D.host.F (algebraMap (𝓞 D.host.F) D.host.F d) = 1`. Rewrite using `[IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]`. Conclude with `hd`. Establish `h1' : p.valuation D.host.F 1 = 1` using `map_one _`. Apply `le_antisymm` to reduce the goal to its premises.

Establish `h2` using `(vle_iff p (algebraMap (𝓞 D.host.F) D.host.F d) 1).2 (by rw [h1, h1'])`. Simplify `h2` using `only [map_one]`. Establish `h2` using `(vle_iff p 1 (algebraMap (𝓞 D.host.F) D.host.F d)).2 (by rw [h1, h1'])`. Simplify `h2` using `only [map_one]`.
-/
theorem val_one_of_notMem (p : PlF D) (d : 𝓞 D.host.F) (hd : d ∉ p.asIdeal) :
    valuation (D.s.atP p).Fp ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F d)) = 1 := by
  have h1 : p.valuation D.host.F (algebraMap (𝓞 D.host.F) D.host.F d) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
    exact hd
  have h1' : p.valuation D.host.F 1 = 1 := map_one _
  apply le_antisymm
  · have h2 := (vle_iff p (algebraMap (𝓞 D.host.F) D.host.F d) 1).2 (by rw [h1, h1'])
    simpa only [map_one] using h2
  · have h2 := (vle_iff p 1 (algebraMap (𝓞 D.host.F) D.host.F d)).2 (by rw [h1, h1'])
    simpa only [map_one] using h2

/- English proof (translation)
Introduce `hmem`. Take `⟨π, hπ⟩` from `p.intValuation_exists_uniformizer`. Establish `hx1 : ¬ (p.valuation D.host.F 1 ≤ p.valuation D.host.F (algebraMap (𝓞 D.host.F) D.host.F π))`. Rewrite using `[map_one, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Evaluate the numerical expressions.

Establish `hxlt : valuation (D.s.atP p).Fp ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F π)) < 1`. Establish `h1` using `mt (vle_iff p 1 (algebraMap (𝓞 D.host.F) D.host.F π)).1 hx1`. Simplify using `only [map_one] at h1`. Conclude with `not_le.1 h1`. Establish `hvl : p.valuation D.host.F (algebraMap (𝓞 D.host.F) D.host.F ((Loc.resChar p : ℕ) : 𝓞 D.host.F)) ≤ p.valuation D.host.F (algebraMap (𝓞 D.host.F) D.host.F (π ^ 2))`.

Rewrite using `[IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, map_pow, hπ, ← WithZero.exp_nsmul]`. Establish `h2` using `(p.intValuation_le_pow_iff_mem _ 2).2 hmem`. Apply the tactic sequence `convert h2 using 2 <;> norm_num`. Establish `hq : valuation (D.s.atP p).Fp (sg.q : (D.s.atP p).Fp) ≤ valuation (D.s.atP p).Fp ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F π)) ^ 2`. Establish `h1` using `(vle_iff p _ _).2 hvl`.

Simplify using `only [map_natCast, map_pow] at h1`. Rewrite using `[sg.q_eq]`. Conclude with `h1`. Establish `hxmem : (D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F π) ∈ 𝒪[(D.s.atP p).Fp]` using `(Valuation.mem_integer_iff _ _).2 hxlt.le`. Establish `hI` using `Valuation.integer.integers (valuation (D.s.atP p).Fp)`.

Establish `hdvd : (⟨_, hxmem⟩ : 𝒪[(D.s.atP p).Fp]) ^ 2 ∣ sg.q`. Apply `hI.dvd_of_le` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `valuation _ (sg.q : (D.s.atP p).Fp) ≤ valuation _ (((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F π)) ^ 2)`. Rewrite using `[map_pow]`. Conclude with `hq`.

Take `⟨c, hc⟩` from `hdvd`. Establish `hsplit : sg.q = (⟨_, hxmem⟩ : 𝒪[(D.s.atP p).Fp]) * ((⟨_, hxmem⟩ : 𝒪[(D.s.atP p).Fp]) * c)`. Rewrite using `[hc]`. Expand and normalize the polynomial expressions, which then agree. Break down `sg.q_irr.isUnit_or_isUnit hsplit with hu | hu` into its components or cases.

Establish `h1` using `hI.isUnit_iff_valuation_eq_one.1 hu`. Conclude with `(ne_of_lt hxlt) h1`. Establish `h1` using `hI.isUnit_iff_valuation_eq_one.1 hu`. Establish `h2 : valuation (D.s.atP p).Fp ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F π) * (c : (D.s.atP p).Fp)) = 1` using `h1`. Rewrite `h2` using `[map_mul]`.

Establish `hc1 : valuation (D.s.atP p).Fp (c : (D.s.atP p).Fp) ≤ 1` using `(Valuation.mem_integer_iff _ _).1 c.2`. Establish `h5` using `mul_le_of_le_one_right' (a := valuation (D.s.atP p).Fp ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F π))) hc1`. Rewrite `h5` using `[h2]`. Conclude with `absurd hxlt (not_lt.2 h5)`.
-/
theorem ell_not_mem_sq (p : PlF D)
    (sg : Loc.SplitAt (D.s.atP p).Fp (D.s.atP p).Ep (D.s.atP p).cj (Loc.resChar p)) :
    ((Loc.resChar p : ℕ) : 𝓞 D.host.F) ∉ p.asIdeal ^ 2 := by
  intro hmem
  obtain ⟨π, hπ⟩ := p.intValuation_exists_uniformizer
  have hx1 : ¬ (p.valuation D.host.F 1 ≤ p.valuation D.host.F (algebraMap (𝓞 D.host.F) D.host.F π)) := by
    rw [map_one, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hπ, ← WithZero.exp_zero,
      WithZero.exp_le_exp]
    norm_num
  have hxlt : valuation (D.s.atP p).Fp ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F π)) < 1 := by
    have h1 := mt (vle_iff p 1 (algebraMap (𝓞 D.host.F) D.host.F π)).1 hx1
    simp only [map_one] at h1
    exact not_le.1 h1
  have hvl : p.valuation D.host.F (algebraMap (𝓞 D.host.F) D.host.F ((Loc.resChar p : ℕ) : 𝓞 D.host.F)) ≤
      p.valuation D.host.F (algebraMap (𝓞 D.host.F) D.host.F (π ^ 2)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, map_pow, hπ, ← WithZero.exp_nsmul]
    have h2 := (p.intValuation_le_pow_iff_mem _ 2).2 hmem
    convert h2 using 2 <;> norm_num
  have hq : valuation (D.s.atP p).Fp (sg.q : (D.s.atP p).Fp) ≤
      valuation (D.s.atP p).Fp ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F π)) ^ 2 := by
    have h1 := (vle_iff p _ _).2 hvl
    simp only [map_natCast, map_pow] at h1
    rw [sg.q_eq]
    exact h1
  have hxmem : (D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F π) ∈ 𝒪[(D.s.atP p).Fp] :=
    (Valuation.mem_integer_iff _ _).2 hxlt.le
  have hI := Valuation.integer.integers (valuation (D.s.atP p).Fp)
  have hdvd : (⟨_, hxmem⟩ : 𝒪[(D.s.atP p).Fp]) ^ 2 ∣ sg.q := by
    apply hI.dvd_of_le
    change valuation _ (sg.q : (D.s.atP p).Fp) ≤
      valuation _ (((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F π)) ^ 2)
    rw [map_pow]
    exact hq
  obtain ⟨c, hc⟩ := hdvd
  have hsplit : sg.q = (⟨_, hxmem⟩ : 𝒪[(D.s.atP p).Fp]) * ((⟨_, hxmem⟩ : 𝒪[(D.s.atP p).Fp]) * c) := by
    rw [hc]
    ring
  rcases sg.q_irr.isUnit_or_isUnit hsplit with hu | hu
  · have h1 := hI.isUnit_iff_valuation_eq_one.1 hu
    exact (ne_of_lt hxlt) h1
  · have h1 := hI.isUnit_iff_valuation_eq_one.1 hu
    have h2 : valuation (D.s.atP p).Fp
        ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F π) * (c : (D.s.atP p).Fp)) = 1 := h1
    rw [map_mul] at h2
    have hc1 : valuation (D.s.atP p).Fp (c : (D.s.atP p).Fp) ≤ 1 := (Valuation.mem_integer_iff _ _).1 c.2
    have h5 := mul_le_of_le_one_right'
      (a := valuation (D.s.atP p).Fp ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F π))) hc1
    rw [h2] at h5
    exact absurd hxlt (not_lt.2 h5)

/- English proof (translation)
Use `haveI hℓ : Fact (Loc.resChar p).Prime := (D.s.atP p).ellPrime`. Establish `hmem` using `ell_mem p`. Establish `hsq` using `ell_not_mem_sq p sg`. Establish `hle : Ideal.span {((Loc.resChar p : ℕ) : 𝓞 D.host.F)} ≤ p.asIdeal` using `(Ideal.span_singleton_le_iff_mem _).2 hmem`. Take `⟨Q, hQ⟩` from `Ideal.dvd_iff_le.2 hle`.

Use `haveI hPm : p.asIdeal.IsMaximal := p.isMaximal`. Establish `hcop : IsCoprime p.asIdeal Q`. Rewrite using `[Ideal.isCoprime_iff_sup_eq]`. Assume the negation of the conclusion as `hne`. Establish `h1 : p.asIdeal = p.asIdeal ⊔ Q` using `Ideal.IsMaximal.eq_of_le hPm hne le_sup_left`.

Establish `h2 : Q ≤ p.asIdeal`. Rewrite using `[h1]`. Conclude with `le_sup_right`. Apply `hsq` to reduce the goal to its premises. Establish `h3 : Ideal.span {((Loc.resChar p : ℕ) : 𝓞 D.host.F)} ≤ p.asIdeal ^ 2`.

Rewrite using `[hQ, sq]`. Conclude with `Ideal.mul_mono_right h2`. Conclude with `(Ideal.span_singleton_le_iff_mem _).1 h3`. Establish `hmap : p.asIdeal * Q = Ideal.map (algebraMap ℤ (𝓞 D.host.F)) (Ideal.span {((Loc.resChar p : ℕ) : ℤ)})`. Rewrite using `[Ideal.map_span, Set.image_singleton, map_natCast, ← hQ]`.

Use `haveI : (Ideal.span {((Loc.resChar p : ℕ) : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hℓ.out).irreducible`. Use `haveI : NeZero (Loc.resChar p) := ⟨hℓ.out.ne_zero⟩`. Use `haveI : Finite (ℤ ⧸ Ideal.span {((Loc.resChar p : ℕ) : ℤ)}) := Finite.of_equiv _ (Int.quotientSpanNatEquivZMod (Loc.resChar p)).symm.toEquiv`. Conclude with `not_dvd_differentIdeal_of_isCoprime ℤ (p := Ideal.span {((Loc.resChar p : ℕ) : ℤ)}) p.asIdeal Q hcop hmap`.
-/
theorem not_dvd_diff (p : PlF D)
    (sg : Loc.SplitAt (D.s.atP p).Fp (D.s.atP p).Ep (D.s.atP p).cj (Loc.resChar p)) :
    ¬ p.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F) := by
  haveI hℓ : Fact (Loc.resChar p).Prime := (D.s.atP p).ellPrime
  have hmem := ell_mem p
  have hsq := ell_not_mem_sq p sg
  have hle : Ideal.span {((Loc.resChar p : ℕ) : 𝓞 D.host.F)} ≤ p.asIdeal :=
    (Ideal.span_singleton_le_iff_mem _).2 hmem
  obtain ⟨Q, hQ⟩ := Ideal.dvd_iff_le.2 hle
  haveI hPm : p.asIdeal.IsMaximal := p.isMaximal
  have hcop : IsCoprime p.asIdeal Q := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    have h1 : p.asIdeal = p.asIdeal ⊔ Q := Ideal.IsMaximal.eq_of_le hPm hne le_sup_left
    have h2 : Q ≤ p.asIdeal := by
      rw [h1]
      exact le_sup_right
    apply hsq
    have h3 : Ideal.span {((Loc.resChar p : ℕ) : 𝓞 D.host.F)} ≤ p.asIdeal ^ 2 := by
      rw [hQ, sq]
      exact Ideal.mul_mono_right h2
    exact (Ideal.span_singleton_le_iff_mem _).1 h3
  have hmap : p.asIdeal * Q =
      Ideal.map (algebraMap ℤ (𝓞 D.host.F)) (Ideal.span {((Loc.resChar p : ℕ) : ℤ)}) := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast, ← hQ]
  haveI : (Ideal.span {((Loc.resChar p : ℕ) : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hℓ.out).irreducible
  haveI : NeZero (Loc.resChar p) := ⟨hℓ.out.ne_zero⟩
  haveI : Finite (ℤ ⧸ Ideal.span {((Loc.resChar p : ℕ) : ℤ)}) :=
    Finite.of_equiv _ (Int.quotientSpanNatEquivZMod (Loc.resChar p)).symm.toEquiv
  exact not_dvd_differentIdeal_of_isCoprime ℤ (p := Ideal.span {((Loc.resChar p : ℕ) : ℤ)})
    p.asIdeal Q hcop hmap

/- English proof (translation)
Introduce `D p hs t ht`. Take `⟨sg, hsg⟩` from `Option.isSome_iff_exists.1 hs`. Establish `hnd` using `not_dvd_diff (D := D) p sg`. Rewrite `hnd` using `[Ideal.dvd_iff_le]`. Take `⟨d, hdD, hdp⟩` from `SetLike.not_le_iff_exists.1 hnd`.

Establish `hdt : ∃ b : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) D.host.F b = algebraMap (𝓞 D.host.F) D.host.F d * t`. Establish `h1 : algebraMap (𝓞 D.host.F) D.host.F d ∈ (1 / Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 D.host.F) D.host.F))`. Rewrite using `[← coeSubmodule_differentIdeal ℤ ℚ (𝓞 D.host.F)]`. Conclude with `(IsLocalization.mem_coeSubmodule _ _).2 ⟨d, hdD, rfl⟩`. Establish `h2 : t ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 D.host.F) D.host.F)`.

Rewrite using `[Submodule.mem_traceDual]`. Introduce `a ha`. Take `⟨b, rfl⟩` from `Submodule.mem_one.1 ha`. Take `⟨n, hn⟩` from `ht b`. Rewrite using `[Algebra.traceForm_apply]`.

Conclude with `RingHom.mem_range.2 ⟨n, by simpa using hn.symm⟩`. Establish `h3` using `(Submodule.mem_div_iff_forall_mul_mem.1 h1) t h2`. Conclude with `Submodule.mem_one.1 h3`. Take `⟨b, hb⟩` from `hdt`. Establish `hv` using `val_one_of_notMem (D := D) p d hdp`.

Establish `hb1 : valuation (D.s.atP p).Fp ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F b)) ≤ 1`. Establish `h4` using `(vle_iff (D := D) p (algebraMap (𝓞 D.host.F) D.host.F b) 1).2 (by rw [map_one]; exact p.valuation_le_one b)`. Simplify `h4` using `only [map_one]`. Rewrite `hb1` using `[hb, map_mul, map_mul, hv, one_mul]`. Conclude with `(Valuation.mem_integer_iff _ _).2 hb1`.
-/
theorem different_lattice_index : DiffG := by
  intro D p hs t ht
  obtain ⟨sg, hsg⟩ := Option.isSome_iff_exists.1 hs
  have hnd := not_dvd_diff (D := D) p sg
  rw [Ideal.dvd_iff_le] at hnd
  obtain ⟨d, hdD, hdp⟩ := SetLike.not_le_iff_exists.1 hnd
  have hdt : ∃ b : 𝓞 D.host.F,
      algebraMap (𝓞 D.host.F) D.host.F b = algebraMap (𝓞 D.host.F) D.host.F d * t := by
    have h1 : algebraMap (𝓞 D.host.F) D.host.F d ∈
        (1 / Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 D.host.F) D.host.F)) := by
      rw [← coeSubmodule_differentIdeal ℤ ℚ (𝓞 D.host.F)]
      exact (IsLocalization.mem_coeSubmodule _ _).2 ⟨d, hdD, rfl⟩
    have h2 : t ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 D.host.F) D.host.F) := by
      rw [Submodule.mem_traceDual]
      intro a ha
      obtain ⟨b, rfl⟩ := Submodule.mem_one.1 ha
      obtain ⟨n, hn⟩ := ht b
      rw [Algebra.traceForm_apply]
      exact RingHom.mem_range.2 ⟨n, by simpa using hn.symm⟩
    have h3 := (Submodule.mem_div_iff_forall_mul_mem.1 h1) t h2
    exact Submodule.mem_one.1 h3
  obtain ⟨b, hb⟩ := hdt
  have hv := val_one_of_notMem (D := D) p d hdp
  have hb1 : valuation (D.s.atP p).Fp ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F b)) ≤ 1 := by
    have h4 := (vle_iff (D := D) p (algebraMap (𝓞 D.host.F) D.host.F b) 1).2
      (by rw [map_one]; exact p.valuation_le_one b)
    simpa only [map_one] using h4
  rw [hb, map_mul, map_mul, hv, one_mul] at hb1
  exact (Valuation.mem_integer_iff _ _).2 hb1

end PI.CntNotIntW
