import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinMinpolyUniformizerWittTotallyRamifiedStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.EisShift

/- English proof (translation)
Establish `h1 : (Polynomial.hasseDeriv n f).natDegree ≤ 1`. Use `Polynomial.natDegree_hasseDeriv_le f n` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hl : f.coeff (1 + n) = 1`. Rewrite using `[add_comm, ← hn]`.

Conclude with `hf.coeff_natDegree`. Rewrite using `[Polynomial.taylor_coeff, Polynomial.eq_X_add_C_of_natDegree_le_one h1]`. Simplify using `only [Polynomial.hasseDeriv_coeff, hl, zero_add, Nat.choose_self, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]`. Rewrite using `[add_comm 1 n, Nat.choose_succ_self_right]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem taylor_coeff_pred {R : Type*} [CommRing R] (f : Polynomial R) (hf : f.Monic) (n : ℕ)
    (hn : f.natDegree = n + 1) (r : R) :
    (Polynomial.taylor r f).coeff n = f.coeff n + ((n + 1 : ℕ) : R) * r := by
  have h1 : (Polynomial.hasseDeriv n f).natDegree ≤ 1 := by
    have := Polynomial.natDegree_hasseDeriv_le f n
    omega
  have hl : f.coeff (1 + n) = 1 := by
    rw [add_comm, ← hn]; exact hf.coeff_natDegree
  rw [Polynomial.taylor_coeff, Polynomial.eq_X_add_C_of_natDegree_le_one h1]
  simp only [Polynomial.hasseDeriv_coeff, hl, zero_add, Nat.choose_self, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [add_comm 1 n, Nat.choose_succ_self_right]
  push_cast
  ring

/- English proof (translation)
Establish `hg : Polynomial.C p ∣ E - Polynomial.X ^ E.natDegree`. Rewrite using `[Polynomial.C_dvd_iff_dvd_coeff]`. Introduce `i`. Rewrite using `[Polynomial.coeff_sub, Polynomial.coeff_X_pow]`. Break down `lt_trichotomy i E.natDegree with h | h | h` into its components or cases.

Rewrite using `[if_neg h.ne, sub_zero]`. Conclude with `hd i h`. Rewrite using `[if_pos h, h, hE.coeff_natDegree, sub_self]`. Conclude with `dvd_zero _`. Rewrite using `[if_neg h.ne', Polynomial.coeff_eq_zero_of_natDegree_lt h, sub_self]`.

Conclude with `dvd_zero _`. Take `⟨g, hg⟩` from `hg`. Establish `hg0 : g.coeff 0 = w`. Use `congrArg (fun q => Polynomial.coeff q 0) hg` as an intermediate fact. Simplify using `only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul] at this`.

Rewrite `this` using `[if_neg (by omega), sub_zero, h0]`. Conclude with `(mul_left_cancel₀ hp this).symm`. Establish `hu : IsUnit (Polynomial.aeval π g)`. Establish `e : Polynomial.aeval π g = algebraMap R O w + π * Polynomial.aeval π g.divX` using `by conv_lhs => rw [← Polynomial.X_mul_divX_add g]`. Simplify using `[hg0, add_comm]`.

Assume the negation of the conclusion as `hn`. Establish `h1 : Polynomial.aeval π g ∈ IsLocalRing.maximalIdeal O` using `hn`. Establish `h3 : π * Polynomial.aeval π g.divX ∈ IsLocalRing.maximalIdeal O` using `Ideal.mul_mem_right _ _ hπ`. Establish `h4` using `Ideal.sub_mem _ h1 h3`. Rewrite `h4` using `[e, add_sub_cancel_right]`.

Conclude with `h4 ((Units.isUnit w).map (algebraMap R O))`. Establish `e` using `congrArg (Polynomial.aeval π) hg`. Simplify using `only [map_sub, hr, map_pow, Polynomial.aeval_X, map_mul, Polynomial.aeval_C, zero_sub] at e`. Rewrite using `[← hu.dvd_mul_right, ← e, dvd_neg]`. Conclude with `pow_dvd_pow _ h2`.
-/
theorem sq_dvd {R O : Type*} [CommRing R] [IsDomain R] [CommRing O] [IsLocalRing O] [Algebra R O]
    (p : R) (hp : p ≠ 0) (π : O) (hπ : ¬ IsUnit π) (E : Polynomial R) (hE : E.Monic)
    (h2 : 2 ≤ E.natDegree) (hd : ∀ i < E.natDegree, p ∣ E.coeff i)
    (w : Rˣ) (h0 : E.coeff 0 = p * w) (hr : Polynomial.aeval π E = 0) :
    π ^ 2 ∣ algebraMap R O p := by
  have hg : Polynomial.C p ∣ E - Polynomial.X ^ E.natDegree := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    rcases lt_trichotomy i E.natDegree with h | h | h
    · rw [if_neg h.ne, sub_zero]; exact hd i h
    · rw [if_pos h, h, hE.coeff_natDegree, sub_self]; exact dvd_zero _
    · rw [if_neg h.ne', Polynomial.coeff_eq_zero_of_natDegree_lt h, sub_self]; exact dvd_zero _
  obtain ⟨g, hg⟩ := hg
  have hg0 : g.coeff 0 = w := by
    have := congrArg (fun q => Polynomial.coeff q 0) hg
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul] at this
    rw [if_neg (by omega), sub_zero, h0] at this
    exact (mul_left_cancel₀ hp this).symm
  have hu : IsUnit (Polynomial.aeval π g) := by
    have e : Polynomial.aeval π g
        = algebraMap R O w + π * Polynomial.aeval π g.divX := by
      conv_lhs => rw [← Polynomial.X_mul_divX_add g]
      simp [hg0, add_comm]
    by_contra hn
    have h1 : Polynomial.aeval π g ∈ IsLocalRing.maximalIdeal O := hn
    have h3 : π * Polynomial.aeval π g.divX ∈ IsLocalRing.maximalIdeal O :=
      Ideal.mul_mem_right _ _ hπ
    have h4 := Ideal.sub_mem _ h1 h3
    rw [e, add_sub_cancel_right] at h4
    exact h4 ((Units.isUnit w).map (algebraMap R O))
  have e := congrArg (Polynomial.aeval π) hg
  simp only [map_sub, hr, map_pow, Polynomial.aeval_X, map_mul, Polynomial.aeval_C, zero_sub] at e
  rw [← hu.dvd_mul_right, ← e, dvd_neg]
  exact pow_dvd_pow _ h2

/- English proof (translation)
Introduce `l _ a _ O _ _ _ _ _ hinj hres`. Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨E, hm, hpos, hd, ⟨w, h0⟩, hr, hs, hmin⟩` from `GlobalTheory.T.eisenstein_minpoly_uniformizer_witt_totallyRamified l a O hinj hres π hπ`. Distinguish the cases in `h : ∃ i, ¬ l ∣ i ∧ E.coeff i ≠ 0`. Conclude with `⟨π, E, hπ, ⟨hm, hpos, hd, w, h0⟩, h, hr, hs, hmin⟩`.

Use `push_neg at h`. Use `haveI : CharZero (Wq l a) := by`. Use `charZero_of_inj_zero fun n hn => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hn0`. Establish `hx : (n : ℤ_[l]) ≠ 0` using `Nat.cast_ne_zero.2 hn0`.

Establish `e` using `congrArg (algebraMap ℤ_[l] (Wq l a)) (PadicInt.unitCoeff_spec hx)`. Rewrite `e` using `[map_natCast, hn, map_mul, map_pow, map_natCast]`. Conclude with `mul_ne_zero ((Units.isUnit _).map (algebraMap ℤ_[l] (Wq l a))).ne_zero (pow_ne_zero _ (WittVector.p_nonzero l (Fq l a))) e.symm`. Establish `hl : l.Prime` using `Fact.out`. Establish `hl0 : (l : Wq l a) ≠ 0` using `Nat.cast_ne_zero.2 hl.ne_zero`.

Establish `hle : l ∣ E.natDegree`. Assume the negation of the conclusion as `hn`. Use `h _ hn` as an intermediate fact. Rewrite `this` using `[hm.coeff_natDegree]`. Conclude with `one_ne_zero this`.

Establish `h2 : 2 ≤ E.natDegree` using `hl.two_le.trans (Nat.le_of_dvd hpos hle)`. Take `⟨t, ht⟩` from `sq_dvd (l : Wq l a) hl0 π hπ.not_isUnit E hm h2 hd w h0 hr`. Establish `hu : IsUnit (1 + π * t)`. Assume the negation of the conclusion as `hn`. Establish `h1 : 1 + π * t ∈ IsLocalRing.maximalIdeal O` using `hn`.

Establish `h3 : π * t ∈ IsLocalRing.maximalIdeal O` using `Ideal.mul_mem_right _ _ hπ.not_isUnit`. Establish `h4` using `Ideal.sub_mem _ h1 h3`. Rewrite `h4` using `[add_sub_cancel_right]`. Conclude with `h4 isUnit_one`. Establish `hπ' : Irreducible (π + algebraMap (Wq l a) O l)`.

Establish `: π + algebraMap (Wq l a) O l = π * (1 + π * t)` using `by rw [ht]; ring`. Rewrite using `[this]`. Conclude with `(irreducible_mul_isUnit hu).2 hπ`. Take `⟨F, fm, fpos, fd, fw, fr, fs, fmin⟩` from `GlobalTheory.T.eisenstein_minpoly_uniformizer_witt_totallyRamified l a O hinj hres _ hπ'`. Use `⟨_, F, hπ', ⟨fm, fpos, fd, fw⟩, ?_, fr, fs, fmin⟩` and prove the remaining obligations.

Establish `d1 : F ∣ Polynomial.taylor (-(l : Wq l a)) E`. Apply `fmin` to reduce the goal to its premises. Rewrite using `[Polynomial.taylor_apply, Polynomial.aeval_comp]`. Simplify using `using hr`. Establish `d2 : E ∣ Polynomial.taylor (l : Wq l a) F`.

Apply `hmin` to reduce the goal to its premises. Rewrite using `[Polynomial.taylor_apply, Polynomial.aeval_comp]`. Simplify using `using fr`. Establish `mt : ∀ (r : Wq l a) (f : Polynomial (Wq l a)), f.Monic → (Polynomial.taylor r f).Monic`. Introduce `r f hf`.

Rewrite using `[Polynomial.taylor_apply]`. Conclude with `hf.comp_X_add_C r`. Establish `n2` using `Polynomial.natDegree_le_of_dvd d2 (mt _ _ fm).ne_zero`. Rewrite `n2` using `[Polynomial.natDegree_taylor]`. Establish `heq : Polynomial.taylor (-(l : Wq l a)) E = F` using `Polynomial.eq_of_monic_of_dvd_of_natDegree_le fm (mt _ _ hm) d1 (by rw [Polynomial.natDegree_taylor]; exact n2)`.

Take `⟨n, hn⟩ : ∃ n, E.natDegree = n + 1` from `⟨E.natDegree - 1, by omega⟩`. Establish `hnd : ¬ l ∣ n`. Introduce `hc`. Rewrite `hle` using `[hn]`. Conclude with `hl.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right hc).1 hle))`.

Use `⟨n, hnd, ?_⟩` and prove the remaining obligations. Rewrite using `[← heq, taylor_coeff_pred E hm n hn, h n hnd, zero_add]`. Conclude with `mul_ne_zero (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n)) (neg_ne_zero.2 hl0)`.
-/
theorem exists_uniformiser : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (Wq l a) O] [Module.Finite (Wq l a) O], Function.Injective (algebraMap (Wq l a) O) → (∀ x : O, ∃ c : Wq l a, ¬ IsUnit (x - algebraMap (Wq l a) O c)) → ∃ (π : O) (Ep : Polynomial (Wq l a)), Irreducible π ∧ (Ep.Monic ∧ 0 < Ep.natDegree ∧ (∀ i < Ep.natDegree, (l : Wq l a) ∣ Ep.coeff i) ∧ (∃ w : (Wq l a)ˣ, Ep.coeff 0 = (l : Wq l a) * w)) ∧ (∃ i, ¬ l ∣ i ∧ Ep.coeff i ≠ 0) ∧ Polynomial.aeval π Ep = 0 ∧ (∀ x : O, ∃ f : Polynomial (Wq l a), Polynomial.aeval π f = x) ∧ ∀ f : Polynomial (Wq l a), Polynomial.aeval π f = 0 → Ep ∣ f := by
  intro l _ a _ O _ _ _ _ _ hinj hres
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨E, hm, hpos, hd, ⟨w, h0⟩, hr, hs, hmin⟩ := GlobalTheory.T.eisenstein_minpoly_uniformizer_witt_totallyRamified l a O hinj hres π hπ
  by_cases h : ∃ i, ¬ l ∣ i ∧ E.coeff i ≠ 0
  · exact ⟨π, E, hπ, ⟨hm, hpos, hd, w, h0⟩, h, hr, hs, hmin⟩
  push_neg at h
  haveI : CharZero (Wq l a) := by
    refine charZero_of_inj_zero fun n hn => ?_
    by_contra hn0
    have hx : (n : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hn0
    have e := congrArg (algebraMap ℤ_[l] (Wq l a)) (PadicInt.unitCoeff_spec hx)
    rw [map_natCast, hn, map_mul, map_pow, map_natCast] at e
    exact mul_ne_zero ((Units.isUnit _).map (algebraMap ℤ_[l] (Wq l a))).ne_zero
      (pow_ne_zero _ (WittVector.p_nonzero l (Fq l a))) e.symm
  have hl : l.Prime := Fact.out
  have hl0 : (l : Wq l a) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hle : l ∣ E.natDegree := by
    by_contra hn
    have := h _ hn
    rw [hm.coeff_natDegree] at this
    exact one_ne_zero this
  have h2 : 2 ≤ E.natDegree := hl.two_le.trans (Nat.le_of_dvd hpos hle)
  obtain ⟨t, ht⟩ := sq_dvd (l : Wq l a) hl0 π hπ.not_isUnit E hm h2 hd w h0 hr
  have hu : IsUnit (1 + π * t) := by
    by_contra hn
    have h1 : 1 + π * t ∈ IsLocalRing.maximalIdeal O := hn
    have h3 : π * t ∈ IsLocalRing.maximalIdeal O := Ideal.mul_mem_right _ _ hπ.not_isUnit
    have h4 := Ideal.sub_mem _ h1 h3
    rw [add_sub_cancel_right] at h4
    exact h4 isUnit_one
  have hπ' : Irreducible (π + algebraMap (Wq l a) O l) := by
    have : π + algebraMap (Wq l a) O l = π * (1 + π * t) := by rw [ht]; ring
    rw [this]
    exact (irreducible_mul_isUnit hu).2 hπ
  obtain ⟨F, fm, fpos, fd, fw, fr, fs, fmin⟩ := GlobalTheory.T.eisenstein_minpoly_uniformizer_witt_totallyRamified l a O hinj hres _ hπ'
  refine ⟨_, F, hπ', ⟨fm, fpos, fd, fw⟩, ?_, fr, fs, fmin⟩
  have d1 : F ∣ Polynomial.taylor (-(l : Wq l a)) E := by
    apply fmin
    rw [Polynomial.taylor_apply, Polynomial.aeval_comp]
    simpa using hr
  have d2 : E ∣ Polynomial.taylor (l : Wq l a) F := by
    apply hmin
    rw [Polynomial.taylor_apply, Polynomial.aeval_comp]
    simpa using fr
  have mt : ∀ (r : Wq l a) (f : Polynomial (Wq l a)), f.Monic → (Polynomial.taylor r f).Monic := by
    intro r f hf
    rw [Polynomial.taylor_apply]
    exact hf.comp_X_add_C r
  have n2 := Polynomial.natDegree_le_of_dvd d2 (mt _ _ fm).ne_zero
  rw [Polynomial.natDegree_taylor] at n2
  have heq : Polynomial.taylor (-(l : Wq l a)) E = F :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le fm (mt _ _ hm) d1
      (by rw [Polynomial.natDegree_taylor]; exact n2)
  obtain ⟨n, hn⟩ : ∃ n, E.natDegree = n + 1 := ⟨E.natDegree - 1, by omega⟩
  have hnd : ¬ l ∣ n := by
    intro hc
    rw [hn] at hle
    exact hl.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right hc).1 hle))
  refine ⟨n, hnd, ?_⟩
  rw [← heq, taylor_coeff_pred E hm n hn, h n hnd, zero_add]
  exact mul_ne_zero (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n)) (neg_ne_zero.2 hl0)

end GlobalTheory.EisShift
