import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanSingletonClosedOfBoundedTorsionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemNonZeroDivisorsOfInvertibleSpanSingletonStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeltaRingHomPowerSeriesOfRankOneImageStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerSeriesRingHomOfIsAdicCompleteStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittVectorLiftOfIsAdicCompleteStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorRingHomEqOfSubMemStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

/- English proof (translation)
Establish `h : Polynomial.C (l : Wq l bk.a) ∣ bk.Ep - Polynomial.X ^ bk.Ep.natDegree`. Rewrite using `[Polynomial.C_dvd_iff_dvd_coeff]`. Introduce `i`. Rewrite using `[Polynomial.coeff_sub, Polynomial.coeff_X_pow]`. Break down `lt_trichotomy i bk.Ep.natDegree with hi | rfl | hi` into its components or cases.

Rewrite using `[if_neg hi.ne, sub_zero]`. Conclude with `bk.dvd_coeff i hi`. Rewrite using `[if_pos rfl, bk.monic.coeff_natDegree, sub_self]`. Conclude with `dvd_zero _`. Rewrite using `[if_neg hi.ne', sub_zero, Polynomial.coeff_eq_zero_of_natDegree_lt hi]`.

Conclude with `dvd_zero _`. Take `⟨q, hq⟩` from `h`. Use `⟨(q : bk.S), ?_⟩` and prove the remaining obligations. Use `congrArg (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) hq` as an intermediate fact. Simplify using `only [map_sub, map_pow, map_mul, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X, Polynomial.coe_C, map_natCast] at this`.

Take the linear combination `-this`.
-/
theorem BK.X_pow_eq_sub {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) :
    ∃ q : bk.S, (X : bk.S) ^ bk.Ep.natDegree = bk.E - (l : bk.S) * q := by
  have h : Polynomial.C (l : Wq l bk.a) ∣ bk.Ep - Polynomial.X ^ bk.Ep.natDegree := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    rcases lt_trichotomy i bk.Ep.natDegree with hi | rfl | hi
    · rw [if_neg hi.ne, sub_zero]; exact bk.dvd_coeff i hi
    · rw [if_pos rfl, bk.monic.coeff_natDegree, sub_self]; exact dvd_zero _
    · rw [if_neg hi.ne', sub_zero, Polynomial.coeff_eq_zero_of_natDegree_lt hi]; exact dvd_zero _
  obtain ⟨q, hq⟩ := h
  refine ⟨(q : bk.S), ?_⟩
  have := congrArg (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) hq
  simp only [map_sub, map_pow, map_mul, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X,
    Polynomial.coe_C, map_natCast] at this
  linear_combination -this

/- English proof (translation)
Establish `hinv` using `P.inv`. Rewrite `hinv` using `[hd]`. Establish `hnzd : d ∈ nonZeroDivisors P.A` using `GlobalTheory.T.mem_nonZeroDivisors_of_invertible_span_singleton' P.A d hinv`. Take `⟨N, hN⟩` from `P.bdd`. Establish `hbdd : ∀ (x : P.A) (m : ℕ), (l : P.A) ^ m * x ∈ Ideal.span {d} → (l : P.A) ^ N * x ∈ Ideal.span {d}`.

Introduce `x m hx`. Rewrite `hx`, the goal using `[← hd, ← Ideal.Quotient.eq_zero_iff_mem]`. Rewrite `hx`, the goal using `[map_mul, map_pow, map_natCast]`. Conclude with `hN _ ⟨m, hx⟩`. Establish `hc` using `P.complete`.

Rewrite `hc` using `[hd]`. Use `⟨fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, hd]`. Use `GlobalTheory.T.mem_span_singleton_of_bounded_torsion_of_adic_limit l P.A d N hnzd hbdd hc x fun n => ?_` and prove the remaining obligations.

Establish `h1` using `hy n`. Simplify using `only [SModEq.zero, smul_eq_mul, Ideal.mul_top] at h1`. Rewrite `h1` using `[← Ideal.map_pow, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]`. Take `⟨y, hy, hyx⟩` from `h1`. Rewrite `hyx` using `[Ideal.Quotient.eq, hd, Ideal.mem_span_singleton']`.

Take `⟨z, hz⟩` from `hyx`. Use `⟨-z, ?_⟩` and prove the remaining obligations. Establish `e : x - d * -z = y` using `by linear_combination hz`. Rewrite using `[e]`. Rewrite `hy` using `[JJ, hd]`.

Conclude with `hy`.
-/
theorem isHausdorff_quot {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] (P : Obj l R) (d : P.A)
    (hd : P.I = Ideal.span {d}) : IsHausdorff ((JJ P).map (Ideal.Quotient.mk P.I)) (P.A ⧸ P.I) := by
  have hinv := P.inv
  rw [hd] at hinv
  have hnzd : d ∈ nonZeroDivisors P.A := GlobalTheory.T.mem_nonZeroDivisors_of_invertible_span_singleton' P.A d hinv
  obtain ⟨N, hN⟩ := P.bdd
  have hbdd : ∀ (x : P.A) (m : ℕ), (l : P.A) ^ m * x ∈ Ideal.span {d} →
      (l : P.A) ^ N * x ∈ Ideal.span {d} := by
    intro x m hx
    rw [← hd, ← Ideal.Quotient.eq_zero_iff_mem] at hx ⊢
    rw [map_mul, map_pow, map_natCast] at hx ⊢
    exact hN _ ⟨m, hx⟩
  have hc := P.complete
  rw [hd] at hc
  refine ⟨fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [Ideal.Quotient.eq_zero_iff_mem, hd]
  refine GlobalTheory.T.mem_span_singleton_of_bounded_torsion_of_adic_limit l P.A d N hnzd hbdd hc x fun n => ?_
  have h1 := hy n
  simp only [SModEq.zero, smul_eq_mul, Ideal.mul_top] at h1
  rw [← Ideal.map_pow, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at h1
  obtain ⟨y, hy, hyx⟩ := h1
  rw [Ideal.Quotient.eq, hd, Ideal.mem_span_singleton'] at hyx
  obtain ⟨z, hz⟩ := hyx
  refine ⟨-z, ?_⟩
  have e : x - d * -z = y := by linear_combination hz
  rw [e]
  rw [JJ, hd] at hy
  exact hy

/- English proof (translation)
Establish `hsurj : Function.Surjective (WittVector.constantCoeff : WittVector l k →+* k)` using `fun x => ⟨WittVector.teichmuller l x, by simp [WittVector.constantCoeff_apply]⟩`. Establish `hker : ∀ a ∈ RingHom.ker (WittVector.constantCoeff : WittVector l k →+* k), f0 a = 0`. Introduce `a ha`. Rewrite `ha` using `[WittVector.ker_constantCoeff, Ideal.mem_span_singleton']`. Take `⟨b, rfl⟩` from `ha`.

Rewrite using `[map_mul, hl, mul_zero]`. Use `⟨(Ideal.Quotient.lift _ f0 hker).comp (RingHom.quotientKerEquivOfSurjective hsurj).symm.toRingHom, fun w => ?_⟩` and prove the remaining obligations. Establish `e : (RingHom.quotientKerEquivOfSurjective hsurj).symm (w.coeff 0) = Ideal.Quotient.mk _ w`. Rewrite using `[RingEquiv.symm_apply_eq]`. Both sides reduce to the same expression.

Use `show Ideal.Quotient.lift _ f0 hker ((RingHom.quotientKerEquivOfSurjective hsurj).symm (w.coeff 0)) = _`. Rewrite using `[e, Ideal.Quotient.lift_mk]`.
-/
theorem exists_lift_coeff_zero {l : ℕ} [Fact l.Prime] {k B : Type} [CommRing k] [CharP k l] [PerfectRing k l]
    [CommRing B] (f0 : WittVector l k →+* B) (hl : f0 (l : WittVector l k) = 0) :
    ∃ ψ : k →+* B, ∀ w : WittVector l k, ψ (w.coeff 0) = f0 w := by
  have hsurj : Function.Surjective (WittVector.constantCoeff : WittVector l k →+* k) :=
    fun x => ⟨WittVector.teichmuller l x, by simp [WittVector.constantCoeff_apply]⟩
  have hker : ∀ a ∈ RingHom.ker (WittVector.constantCoeff : WittVector l k →+* k), f0 a = 0 := by
    intro a ha
    rw [WittVector.ker_constantCoeff, Ideal.mem_span_singleton'] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, hl, mul_zero]
  refine ⟨(Ideal.Quotient.lift _ f0 hker).comp (RingHom.quotientKerEquivOfSurjective hsurj).symm.toRingHom,
    fun w => ?_⟩
  have e : (RingHom.quotientKerEquivOfSurjective hsurj).symm (w.coeff 0) = Ideal.Quotient.mk _ w := by
    rw [RingEquiv.symm_apply_eq]; rfl
  show Ideal.Quotient.lift _ f0 hker ((RingHom.quotientKerEquivOfSurjective hsurj).symm (w.coeff 0)) = _
  rw [e, Ideal.Quotient.lift_mk]

/- English proof (translation)
Establish `a2` using `congrArg τ hq`. Rewrite `a2` using `[map_pow, map_sub, map_mul, map_natCast, hx, hE]`. Take `⟨t, ht⟩` from `Ideal.Quotient.mk_surjective (τ q)`. Establish `h1 : Ideal.Quotient.mk I (v ^ e + (l : A) * t) = 0`. Rewrite using `[map_add, map_pow, map_mul, map_natCast, ht, a2]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h2` using `hIJ (Ideal.Quotient.eq_zero_iff_mem.1 h1)`. Establish `h3 : (l : A) * t ∈ J` using `Ideal.mul_mem_right _ _ hl`. Simplify using `using J.sub_mem h2 h3`.
-/
theorem pow_mem_of_eq_sub {A S : Type} [CommRing A] [CommRing S] {I J : Ideal A} (hIJ : I ≤ J) {l : ℕ}
    (hl : (l : A) ∈ J) (τ : S →+* A ⧸ I) {x E q : S} {e : ℕ} {v : A} (hq : x ^ e = E - (l : S) * q)
    (hE : τ E = 0) (hx : τ x = Ideal.Quotient.mk I v) : v ^ e ∈ J := by
  have a2 := congrArg τ hq
  rw [map_pow, map_sub, map_mul, map_natCast, hx, hE] at a2
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (τ q)
  have h1 : Ideal.Quotient.mk I (v ^ e + (l : A) * t) = 0 := by
    rw [map_add, map_pow, map_mul, map_natCast, ht, a2]
    ring
  have h2 := hIJ (Ideal.Quotient.eq_zero_iff_mem.1 h1)
  have h3 : (l : A) * t ∈ J := Ideal.mul_mem_right _ _ hl
  simpa using J.sub_mem h2 h3

/- English proof (translation)
Take `⟨t, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Rewrite `h` using `[Ideal.Quotient.factor_mk, Ideal.Quotient.eq]`. Rewrite using `[← map_sub]`. Conclude with `Ideal.mem_map_of_mem _ h`.
-/
theorem sub_mem_map_of_mk_eq {A : Type} [CommRing A] {I J : Ideal A} (hIJ : I ≤ J) (a : A) (y : A ⧸ I)
    (h : Ideal.Quotient.mk J a = Ideal.Quotient.factor hIJ y) :
    Ideal.Quotient.mk I a - y ∈ J.map (Ideal.Quotient.mk I) := by
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq] at h
  rw [← map_sub]
  exact Ideal.mem_map_of_mem _ h

/- English proof (translation)
Use `ringHom_ext_of_sep _ _ hC ?_ ?_` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, hσX, hτX]`. Introduce `y hy`. Use `hH.haus y fun n => ?_` and prove the remaining obligations. Simplify using `only [SModEq.zero, smul_eq_mul, Ideal.mul_top]`.

Take `⟨c, hc⟩` from `hy (e * n)`. Rewrite using `[hc, RingHom.comp_apply, hσX, pow_mul, ← map_pow]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ hve) n)`.
-/
theorem quot_comp_eq {W A : Type} [CommRing W] [CommRing A] {I J : Ideal A}
    (hH : IsHausdorff (J.map (Ideal.Quotient.mk I)) (A ⧸ I)) (σ : W⟦X⟧ →+* A) (τ : W⟦X⟧ →+* A ⧸ I)
    {v : A} {e : ℕ} (hve : v ^ e ∈ J) (hσX : σ X = v) (hτX : τ X = Ideal.Quotient.mk I v)
    (hC : ∀ w, Ideal.Quotient.mk I (σ (C w)) = τ (C w)) : (Ideal.Quotient.mk I).comp σ = τ := by
  refine ringHom_ext_of_sep _ _ hC ?_ ?_
  · rw [RingHom.comp_apply, hσX, hτX]
  · intro y hy
    refine hH.haus y fun n => ?_
    simp only [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    obtain ⟨c, hc⟩ := hy (e * n)
    rw [hc, RingHom.comp_apply, hσX, pow_mul, ← map_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ hve) n)

/- English proof (translation)
Take `⟨y, rfl⟩` from `Ideal.mem_span_singleton'.1 ha`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, ← RingHom.comp_apply, heq, map_mul, hE, mul_zero]`.
-/
theorem mem_of_comp_eq {S A : Type} [CommRing S] [CommRing A] {I : Ideal A} (σ : S →+* A)
    (τ : S →+* A ⧸ I) (heq : (Ideal.Quotient.mk I).comp σ = τ) {E : S} (hE : τ E = 0) (a : S)
    (ha : a ∈ Ideal.span {E}) : σ a ∈ I := by
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← RingHom.comp_apply, heq, map_mul, hE, mul_zero]

/- English proof (translation)
Use `Ideal.mem_map_of_mem (Ideal.Quotient.mk I) h` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis.
-/
theorem natCast_mem_map_quot {A : Type} [CommRing A] {I J : Ideal A} {l : ℕ} (h : (l : A) ∈ J) :
    (l : A ⧸ I) ∈ J.map (Ideal.Quotient.mk I) := by
  have := Ideal.mem_map_of_mem (Ideal.Quotient.mk I) h
  rwa [map_natCast] at this

/- English proof (translation)
Introduce `l _ K bk P d v hF hδ`. Take `⟨hd, hv⟩` from `hF`. Take `⟨τ, hτ⟩ : ∃ τ : bk.S →+* P.A ⧸ P.I, τ = P.str.comp (bk.str.symm.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {bk.E})))` from `⟨_, rfl⟩`. Establish `hτX : τ X = Ideal.Quotient.mk P.I v` using `by rw [hτ]; exact hv.symm`. Establish `hτE : τ bk.E = 0`.

Rewrite using `[hτ]`. Use `show P.str (bk.str.symm (Ideal.Quotient.mk (Ideal.span {bk.E}) bk.E)) = 0`. Rewrite using `[Ideal.Quotient.mk_singleton_self, map_zero, map_zero]`. Use `set J : Ideal P.A := JJ P with hJ`. Establish `hIJ : P.I ≤ J` using `le_sup_right`.

Establish `hlJ : (l : P.A) ∈ J` using `Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)`. Take `⟨f0, hf0⟩ : ∃ f0 : Wq l bk.a →+* P.A ⧸ J, f0 = ((Ideal.Quotient.factor hIJ).comp τ).comp PowerSeries.C` from `⟨_, rfl⟩`. Establish `hl0 : f0 (l : Wq l bk.a) = 0`. Rewrite using `[map_natCast, ← map_natCast (Ideal.Quotient.mk J) l]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 hlJ`.

Take `⟨ψ, hψ⟩` from `exists_lift_coeff_zero f0 hl0`. Take `⟨ω, hω⟩` from `GlobalTheory.T.exists_wittVector_lift_of_isAdicComplete' l (Fq l bk.a) P.A J hlJ P.complete ψ`. Take `⟨q, hq⟩` from `bk.X_pow_eq_sub`. Generalize the expression as in `bk.Ep.natDegree = e at hq`. Establish `hve : v ^ e ∈ J` using `pow_mem_of_eq_sub hIJ hlJ τ hq hτE hτX`.

Take `⟨σ, hσC, hσX⟩` from `GlobalTheory.T.exists_powerSeries_ringHom_of_isAdicComplete (Wq l bk.a) P.A J P.complete ω v _ hve`. Establish `hσδ` using `GlobalTheory.T.isDeltaRingHom_powerSeries_of_rank_one_image l bk.a P.A P.D J hlJ P.complete.toIsHausdorff σ _ (by rw [hσX]; exact hve) (by rw [hσX]; exact hδ)`. Establish `hH` using `isHausdorff_quot P d hd`. Establish `hlJ'` using `natCast_mem_map_quot (I := P.I) hlJ`. Establish `hωC : (Ideal.Quotient.mk P.I).comp ω = τ.comp PowerSeries.C`.

Use `GlobalTheory.T.wittVector_ringHom_eq_of_sub_mem' l (Fq l bk.a) (P.A ⧸ P.I) (J.map (Ideal.Quotient.mk P.I)) hlJ' hH _ _ ?_` and prove the remaining obligations. Introduce `w`. Use `sub_mem_map_of_mk_eq hIJ (ω w) (τ (PowerSeries.C w)) ((hω w).trans ((hψ w).trans ?_))` and prove the remaining obligations. Rewrite using `[hf0]`. Simplify using `only [RingHom.comp_apply]`.

Establish `heq : (Ideal.Quotient.mk P.I).comp σ = τ` using `quot_comp_eq hH σ τ hve hσX hτX fun w => (congrArg (Ideal.Quotient.mk P.I) (hσC w)).trans (RingHom.congr_fun hωC w)`. Use `⟨{ f := σ, f_δ := fun a => hσδ a, f_I := mem_of_comp_eq σ τ heq hτE, f_str := ?_ }, hσX⟩` and prove the remaining obligations. Introduce `r a h`. Establish `h' : Ideal.Quotient.mk (Ideal.span {bk.E}) a = bk.str r` using `h`. Establish `h2` using `RingHom.congr_fun heq a`.

Rewrite `h2` using `[hτ]`. Use `h2.trans ?_` and prove the remaining obligations. Use `show P.str (bk.str.symm (Ideal.Quotient.mk (Ideal.span {bk.E}) a)) = P.str r`. Conclude with `congrArg P.str ((congrArg bk.str.symm h').trans (bk.str.symm_apply_apply r))`.
-/
theorem exists_hom_of_frame : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Obj l ↥(OL K)) (d v : C.A),
    IsFrame bk C d v → C.D.δ v = 0 → ∃ g : Hom bk.prism C, BK.hf g X = v := by
  intro l _ K bk P d v hF hδ
  obtain ⟨hd, hv⟩ := hF
  obtain ⟨τ, hτ⟩ : ∃ τ : bk.S →+* P.A ⧸ P.I,
      τ = P.str.comp (bk.str.symm.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {bk.E}))) := ⟨_, rfl⟩
  have hτX : τ X = Ideal.Quotient.mk P.I v := by rw [hτ]; exact hv.symm
  have hτE : τ bk.E = 0 := by
    rw [hτ]
    show P.str (bk.str.symm (Ideal.Quotient.mk (Ideal.span {bk.E}) bk.E)) = 0
    rw [Ideal.Quotient.mk_singleton_self, map_zero, map_zero]
  set J : Ideal P.A := JJ P with hJ
  have hIJ : P.I ≤ J := le_sup_right
  have hlJ : (l : P.A) ∈ J := Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  obtain ⟨f0, hf0⟩ : ∃ f0 : Wq l bk.a →+* P.A ⧸ J,
      f0 = ((Ideal.Quotient.factor hIJ).comp τ).comp PowerSeries.C := ⟨_, rfl⟩
  have hl0 : f0 (l : Wq l bk.a) = 0 := by
    rw [map_natCast, ← map_natCast (Ideal.Quotient.mk J) l]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hlJ
  obtain ⟨ψ, hψ⟩ := exists_lift_coeff_zero f0 hl0
  obtain ⟨ω, hω⟩ := GlobalTheory.T.exists_wittVector_lift_of_isAdicComplete' l (Fq l bk.a) P.A J hlJ P.complete ψ
  obtain ⟨q, hq⟩ := bk.X_pow_eq_sub
  generalize bk.Ep.natDegree = e at hq
  have hve : v ^ e ∈ J := pow_mem_of_eq_sub hIJ hlJ τ hq hτE hτX
  obtain ⟨σ, hσC, hσX⟩ := GlobalTheory.T.exists_powerSeries_ringHom_of_isAdicComplete (Wq l bk.a) P.A J P.complete ω v _ hve
  have hσδ := GlobalTheory.T.isDeltaRingHom_powerSeries_of_rank_one_image l bk.a P.A P.D J hlJ P.complete.toIsHausdorff σ _ (by rw [hσX]; exact hve)
    (by rw [hσX]; exact hδ)
  have hH := isHausdorff_quot P d hd
  have hlJ' := natCast_mem_map_quot (I := P.I) hlJ
  have hωC : (Ideal.Quotient.mk P.I).comp ω = τ.comp PowerSeries.C := by
    refine GlobalTheory.T.wittVector_ringHom_eq_of_sub_mem' l (Fq l bk.a) (P.A ⧸ P.I) (J.map (Ideal.Quotient.mk P.I)) hlJ' hH _ _ ?_
    intro w
    refine sub_mem_map_of_mk_eq hIJ (ω w) (τ (PowerSeries.C w)) ((hω w).trans ((hψ w).trans ?_))
    rw [hf0]
    simp only [RingHom.comp_apply]
  have heq : (Ideal.Quotient.mk P.I).comp σ = τ :=
    quot_comp_eq hH σ τ hve hσX hτX fun w =>
      (congrArg (Ideal.Quotient.mk P.I) (hσC w)).trans (RingHom.congr_fun hωC w)
  refine ⟨{ f := σ, f_δ := fun a => hσδ a, f_I := mem_of_comp_eq σ τ heq hτE, f_str := ?_ }, hσX⟩
  intro r a h
  have h' : Ideal.Quotient.mk (Ideal.span {bk.E}) a = bk.str r := h
  have h2 := RingHom.congr_fun heq a
  rw [hτ] at h2
  refine h2.trans ?_
  show P.str (bk.str.symm (Ideal.Quotient.mk (Ideal.span {bk.E}) a)) = P.str r
  exact congrArg P.str ((congrArg bk.str.symm h').trans (bk.str.symm_apply_apply r))

end GlobalTheory.BSP
