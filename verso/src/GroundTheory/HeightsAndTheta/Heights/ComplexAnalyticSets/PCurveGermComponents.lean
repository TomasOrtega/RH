import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveGermComponents
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalDimDomain
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

namespace CurveGermComponents

variable {n : ℕ}

/- English proof (translation)
Simplify using `only [zeroSet, Set.mem_ofPred_eq, SetLike.le_def, RingHom.mem_ker]`.
-/
theorem mem_zeroSet_iff_le_ker (J : Ideal (MvPolynomial (Fin n) ℂ)) (x : Fin n → ℂ) :
    x ∈ zeroSet J ↔ J ≤ RingHom.ker (eval x : MvPolynomial (Fin n) ℂ →+* ℂ) := by
  simp only [zeroSet, Set.mem_ofPred_eq, SetLike.le_def, RingHom.mem_ker]

/- English proof (translation)
Establish `h : zeroSet J = ⋂ f ∈ J, {x : Fin n → ℂ | eval x f = 0}`. Use extensionality with `x`. Simplify using `[zeroSet]`. Rewrite using `[h]`. Conclude with `isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval f) continuous_const`.
-/
theorem isClosed_zeroSet (J : Ideal (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroSet J) := by
  have h : zeroSet J = ⋂ f ∈ J, {x : Fin n → ℂ | eval x f = 0} := by
    ext x
    simp [zeroSet]
  rw [h]
  exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval f) continuous_const

/- English proof (translation)
Rewrite `hx` using `[mem_zeroSet_iff_le_ker]`. Take `⟨W, hW, hle⟩` from `Ideal.exists_minimalPrimes_le hx`. Conclude with `⟨W, hW, (mem_zeroSet_iff_le_ker W x).2 hle⟩`.
-/
theorem exists_minimalPrime_mem_zeroSet {I : Ideal (MvPolynomial (Fin n) ℂ)} {x : Fin n → ℂ}
    (hx : x ∈ zeroSet I) : ∃ W ∈ I.minimalPrimes, x ∈ zeroSet W := by
  rw [mem_zeroSet_iff_le_ker] at hx
  obtain ⟨W, hW, hle⟩ := Ideal.exists_minimalPrimes_le hx
  exact ⟨W, hW, (mem_zeroSet_iff_le_ker W x).2 hle⟩

/- English proof (translation)
Use `set m := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) with hmdef`. Set `L` to `Localization.AtPrime m`. Set `J : Ideal L` to `I.map (algebraMap (MvPolynomial (Fin n) ℂ) L)`. Express the relevant statement in the definitionally equal form `ringKrullDim (L ⧸ J) ≤ 0`. Establish `hK : Ring.KrullDimLE 0 (L ⧸ J)`.

Rewrite using `[Ring.krullDimLE_zero_iff]`. Introduce `p hp`. Use `set Q := p.comap (Ideal.Quotient.mk J) with hQdef`. Establish `hQ : Q.IsPrime` using `Ideal.comap_isPrime _ _`. Establish `hP : (Q.comap (algebraMap (MvPolynomial (Fin n) ℂ) L)).IsPrime` using `Ideal.comap_isPrime _ _`.

Establish `hIP : I ≤ Q.comap (algebraMap (MvPolynomial (Fin n) ℂ) L)`. Rewrite using `[← Ideal.map_le_iff_le_comap]`. Introduce `y hy`. Rewrite using `[hQdef, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hy]`. Conclude with `p.zero_mem`.

Establish `hPm : Q.comap (algebraMap (MvPolynomial (Fin n) ℂ) L) ≤ m`. Conclude with `(Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQ.ne_top)).trans (Localization.AtPrime.under_maximalIdeal (I := m)).le`. Establish `hPeq : Q.under (MvPolynomial (Fin n) ℂ) = m` using `le_antisymm hPm (hm.2 ⟨hP, hIP⟩ hPm)`. Establish `hQmax : Q = IsLocalRing.maximalIdeal L` using `Localization.AtPrime.eq_maximalIdeal_iff_under_eq.1 hPeq`. Establish `hQm : Q.IsMaximal` using `hQmax ▸ IsLocalRing.maximalIdeal.isMaximal L`.

Establish `h` using `Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective hQm`. Rewrite `h` using `[hQdef, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]`. Conclude with `h.resolve_left hp.ne_top`. Conclude with `Ring.krullDimLE_iff.1 hK` after adjusting the coercions.
-/
theorem ringKrullDim_curveLocalRing_le_zero {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (hm : RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) ∈ I.minimalPrimes) :
    ringKrullDim (curveLocalRing I q) ≤ 0 := by
  set m := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) with hmdef
  let L := Localization.AtPrime m
  let J : Ideal L := I.map (algebraMap (MvPolynomial (Fin n) ℂ) L)
  change ringKrullDim (L ⧸ J) ≤ 0
  have hK : Ring.KrullDimLE 0 (L ⧸ J) := by
    rw [Ring.krullDimLE_zero_iff]
    intro p hp
    set Q := p.comap (Ideal.Quotient.mk J) with hQdef
    have hQ : Q.IsPrime := Ideal.comap_isPrime _ _
    have hP : (Q.comap (algebraMap (MvPolynomial (Fin n) ℂ) L)).IsPrime := Ideal.comap_isPrime _ _
    have hIP : I ≤ Q.comap (algebraMap (MvPolynomial (Fin n) ℂ) L) := by
      rw [← Ideal.map_le_iff_le_comap]
      intro y hy
      rw [hQdef, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hy]
      exact p.zero_mem
    have hPm : Q.comap (algebraMap (MvPolynomial (Fin n) ℂ) L) ≤ m := by
      exact (Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQ.ne_top)).trans
        (Localization.AtPrime.under_maximalIdeal (I := m)).le
    have hPeq : Q.under (MvPolynomial (Fin n) ℂ) = m := le_antisymm hPm (hm.2 ⟨hP, hIP⟩ hPm)
    have hQmax : Q = IsLocalRing.maximalIdeal L := Localization.AtPrime.eq_maximalIdeal_iff_under_eq.1 hPeq
    have hQm : Q.IsMaximal := hQmax ▸ IsLocalRing.maximalIdeal.isMaximal L
    have h := Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective hQm
    rw [hQdef, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h
    exact h.resolve_left hp.ne_top
  exact_mod_cast Ring.krullDimLE_iff.1 hK

/- English proof (translation)
Use `set m := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) with hmdef`. Establish `hWm : W ≤ m` using `(mem_zeroSet_iff_le_ker W q).1 hq`. Establish `hWp : W.IsPrime` using `hW.1.1`. Set `L` to `Localization.AtPrime m`. Establish `hle : I.map (algebraMap (MvPolynomial (Fin n) ℂ) L) ≤ W.map (algebraMap (MvPolynomial (Fin n) ℂ) L)` using `Ideal.map_mono hW.1.2`.

Establish `hup : ringKrullDim (localRingAt W q) ≤ 1`. Rewrite using `[← hdim]`. Conclude with `ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)`. Establish `disj : Disjoint (m.primeCompl : Set (MvPolynomial (Fin n) ℂ)) W`. Rewrite using `[Set.disjoint_left]`.

Introduce `a ha haW`. Conclude with `ha (hWm haW)`. Establish `hWL : (W.map (algebraMap (MvPolynomial (Fin n) ℂ) L)).IsPrime` using `IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl L W hWp disj`. Establish `hne : ¬ ringKrullDim (localRingAt W q) ≤ 0`. Introduce `h0`.

Establish `: Ring.KrullDimLE 0 (localRingAt W q)` using `Ring.krullDimLE_iff.2 (by exact_mod_cast h0)`. Establish `: IsDomain (localRingAt W q)` using `Ideal.Quotient.isDomain _`. Establish `hf : IsField (localRingAt W q)` using `Ring.KrullDimLE.isField_of_isDomain (R := localRingAt W q)`. Establish `hmax : (W.map (algebraMap (MvPolynomial (Fin n) ℂ) L)).IsMaximal` using `Ideal.Quotient.maximal_of_isField _ hf`. Establish `hWeq : W = m`.

Establish `h1` using `IsLocalization.under_map_of_isPrime_disjoint m.primeCompl L hWp disj`. Rewrite `h1` using `[IsLocalRing.eq_maximalIdeal hmax, Localization.AtPrime.under_maximalIdeal]`. Conclude with `h1.symm`. Rewrite `hW` using `[hWeq]`. Establish `h2` using `ringKrullDim_curveLocalRing_le_zero hW`.

Rewrite `h2` using `[hdim]`. Conclude with `absurd h2 (by decide)`. Conclude with `le_antisymm hup (Order.succ_le_of_lt (lt_of_not_ge hne))`.
-/
theorem ringKrullDim_localRingAt_eq_one {I W : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (hW : W ∈ I.minimalPrimes) (hq : q ∈ zeroSet W) (hdim : ringKrullDim (curveLocalRing I q) = 1) :
    ringKrullDim (localRingAt W q) = 1 := by
  set m := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) with hmdef
  have hWm : W ≤ m := (mem_zeroSet_iff_le_ker W q).1 hq
  have hWp : W.IsPrime := hW.1.1
  let L := Localization.AtPrime m
  have hle : I.map (algebraMap (MvPolynomial (Fin n) ℂ) L) ≤ W.map (algebraMap (MvPolynomial (Fin n) ℂ) L) :=
    Ideal.map_mono hW.1.2
  have hup : ringKrullDim (localRingAt W q) ≤ 1 := by
    rw [← hdim]
    exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
  have disj : Disjoint (m.primeCompl : Set (MvPolynomial (Fin n) ℂ)) W := by
    rw [Set.disjoint_left]
    intro a ha haW
    exact ha (hWm haW)
  have hWL : (W.map (algebraMap (MvPolynomial (Fin n) ℂ) L)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl L W hWp disj
  have hne : ¬ ringKrullDim (localRingAt W q) ≤ 0 := by
    intro h0
    have : Ring.KrullDimLE 0 (localRingAt W q) := Ring.krullDimLE_iff.2 (by exact_mod_cast h0)
    have : IsDomain (localRingAt W q) := Ideal.Quotient.isDomain _
    have hf : IsField (localRingAt W q) := Ring.KrullDimLE.isField_of_isDomain (R := localRingAt W q)
    have hmax : (W.map (algebraMap (MvPolynomial (Fin n) ℂ) L)).IsMaximal :=
      Ideal.Quotient.maximal_of_isField _ hf
    have hWeq : W = m := by
      have h1 := IsLocalization.under_map_of_isPrime_disjoint m.primeCompl L hWp disj
      rw [IsLocalRing.eq_maximalIdeal hmax, Localization.AtPrime.under_maximalIdeal] at h1
      exact h1.symm
    rw [hWeq] at hW
    have h2 := ringKrullDim_curveLocalRing_le_zero hW
    rw [hdim] at h2
    exact absurd h2 (by decide)
  exact le_antisymm hup (Order.succ_le_of_lt (lt_of_not_ge hne))

/- English proof (translation)
Establish `h0` using `ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ W)`. Establish `h1 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ (n : ℕ)` using `(ringKrullDim_quotient_le W).trans (by simp)`. Generalize the expression as in `ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = d at h0 h1 ⊢`. Proceed by induction on `d using WithBot.recBotCoe with`. Consider the case `bot => simp at h0`.

Consider the case `coe d`. Proceed by induction on `d using ENat.recTopCoe with`. Consider the case `top`. Rewrite `h1` using `[← WithBot.coe_natCast, WithBot.coe_le_coe]`. Conclude with `absurd h1 (not_le.2 (ENat.natCast_lt_top n))`.

Consider the case `coe e => exact ⟨e, rfl⟩`.
-/
theorem exists_ringKrullDim_quotient_eq_nat (W : Ideal (MvPolynomial (Fin n) ℂ)) [W.IsPrime] :
    ∃ e : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (e : ℕ) := by
  have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ W)
  have h1 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ (n : ℕ) :=
    (ringKrullDim_quotient_le W).trans (by simp)
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = d at h0 h1 ⊢
  induction d using WithBot.recBotCoe with
  | bot => simp at h0
  | coe d =>
    induction d using ENat.recTopCoe with
    | top =>
      rw [← WithBot.coe_natCast, WithBot.coe_le_coe] at h1
      exact absurd h1 (not_le.2 (ENat.natCast_lt_top n))
    | coe e => exact ⟨e, rfl⟩

/- English proof (translation)
Introduce `n I q hdim`. Establish `hfin : I.minimalPrimes.Finite` using `Ideal.finite_minimalPrimes_of_isNoetherianRing _ I`. Use `⟨⋂ W ∈ {W ∈ I.minimalPrimes | q ∉ zeroSet W}, (zeroSet W)ᶜ, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(Filter.biInter_mem (hfin.subset (Set.sep_subset _ _))).2 fun W hW => (isClosed_zeroSet W).isOpen_compl.mem_nhds hW.2`. Introduce and unpack `x ⟨hxI, hxN⟩`.

Take `⟨W, hW, hxW⟩` from `exists_minimalPrime_mem_zeroSet hxI`. Establish `hqW : q ∈ zeroSet W`. Assume the negation of the conclusion as `hq`. Conclude with `Set.mem_iInter₂.1 hxN W ⟨hW, hq⟩ hxW`. Use `⟨W, hW, ?_, hqW, hxW⟩` and prove the remaining obligations.

Establish `hWp : W.IsPrime` using `hW.1.1`. Take `⟨e, he⟩` from `exists_ringKrullDim_quotient_eq_nat W`. Establish `h1` using `LocalDimDomain.proof n e W hWp he q hqW`. Rewrite `h1` using `[ringKrullDim_localRingAt_eq_one hW hqW hdim]`. Rewrite using `[he]`.

Conclude with `h1.symm` after adjusting the coercions.
-/
theorem proof : CurveGermComponents.Statement := by
  intro n I q hdim
  classical
  have hfin : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ I
  refine ⟨⋂ W ∈ {W ∈ I.minimalPrimes | q ∉ zeroSet W}, (zeroSet W)ᶜ, ?_, ?_⟩
  · exact (Filter.biInter_mem (hfin.subset (Set.sep_subset _ _))).2 fun W hW =>
      (isClosed_zeroSet W).isOpen_compl.mem_nhds hW.2
  · rintro x ⟨hxI, hxN⟩
    obtain ⟨W, hW, hxW⟩ := exists_minimalPrime_mem_zeroSet hxI
    have hqW : q ∈ zeroSet W := by
      by_contra hq
      exact Set.mem_iInter₂.1 hxN W ⟨hW, hq⟩ hxW
    refine ⟨W, hW, ?_, hqW, hxW⟩
    have hWp : W.IsPrime := hW.1.1
    obtain ⟨e, he⟩ := exists_ringKrullDim_quotient_eq_nat W
    have h1 := LocalDimDomain.proof n e W hWp he q hqW
    rw [ringKrullDim_localRingAt_eq_one hW hqW hdim] at h1
    rw [he]
    exact_mod_cast h1.symm

end CurveGermComponents

end

end GroundTheory.Heights₂.Heights
