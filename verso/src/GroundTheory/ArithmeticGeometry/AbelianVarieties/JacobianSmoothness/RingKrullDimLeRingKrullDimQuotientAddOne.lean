import Mathlib
import GroundTheory.ArithmeticGeometry.ToricVarieties.Dimension

namespace GroundTheory.Arith.Abelian.Jacobian

open Algebra Cardinal

universe u

section Normalization

variable (k : Type u) [Field k] {A : Type u} [CommRing A] [Algebra k A]

/- English proof (translation)
Set `_ : Algebra (MvPolynomial (Fin s) k) A` to `g.toRingHom.toAlgebra`. Establish `_ : Algebra.IsIntegral (MvPolynomial (Fin s) k) A` using `⟨fun x => hint x⟩`. Rewrite using `[GroundTheory.Arith.Toric.ringKrullDim_eq_of_isIntegral hinj, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]`. Simplify using the standard rewrite rules.
-/
theorem ringKrullDim_eq_of_normalization {s : ℕ} (g : MvPolynomial (Fin s) k →ₐ[k] A)
    (hinj : Function.Injective g) (hint : g.IsIntegral) : ringKrullDim A = s := by
  let _ : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  have _ : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨fun x => hint x⟩
  rw [GroundTheory.Arith.Toric.ringKrullDim_eq_of_isIntegral hinj,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

/- English proof (translation)
Set `_ : Algebra (MvPolynomial (Fin s) k) A` to `g.toRingHom.toAlgebra`. Establish `_ : IsScalarTower k (MvPolynomial (Fin s) k) A` using `IsScalarTower.of_algebraMap_eq fun c => (g.commutes c).symm`. Establish `_ : Algebra.IsIntegral (MvPolynomial (Fin s) k) A` using `⟨fun x => hint x⟩`. Establish `_ : FaithfulSMul (MvPolynomial (Fin s) k) A` using `(faithfulSMul_iff_algebraMap_injective _ _).2 hinj`. Establish `h` using `trdeg_add_eq k (MvPolynomial (Fin s) k) (A := A)`.

Rewrite `h` using `[MvPolynomial.trdeg_of_isDomain, trdeg_eq_zero (R := MvPolynomial (Fin s) k) (A := A)]`. Simplify using `using h.symm`.
-/
theorem trdeg_eq_of_normalization [IsDomain A] {s : ℕ} (g : MvPolynomial (Fin s) k →ₐ[k] A)
    (hinj : Function.Injective g) (hint : g.IsIntegral) : trdeg k A = s := by
  let _ : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  have _ : IsScalarTower k (MvPolynomial (Fin s) k) A :=
    IsScalarTower.of_algebraMap_eq fun c => (g.commutes c).symm
  have _ : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨fun x => hint x⟩
  have _ : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have h := trdeg_add_eq k (MvPolynomial (Fin s) k) (A := A)
  rw [MvPolynomial.trdeg_of_isDomain, trdeg_eq_zero (R := MvPolynomial (Fin s) k) (A := A)] at h
  simpa using h.symm

variable [Algebra.FiniteType k A]

/- English proof (translation)
Take `⟨s, g, hinj, hint⟩` from `exists_integral_inj_algHom_of_fg k A`. Conclude with `⟨s, ringKrullDim_eq_of_normalization k g hinj hint, trdeg_eq_of_normalization k g hinj hint⟩`.
-/
theorem exists_ringKrullDim_eq_trdeg [IsDomain A] :
    ∃ n : ℕ, ringKrullDim A = n ∧ trdeg k A = n := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  exact ⟨s, ringKrullDim_eq_of_normalization k g hinj hint,
    trdeg_eq_of_normalization k g hinj hint⟩

/- English proof (translation)
Take `⟨n, h1, h2⟩` from `exists_ringKrullDim_eq_trdeg (k := k) (A := A)`. Rewrite using `[h1, h2]`. Simplify using the standard rewrite rules.
-/
theorem ringKrullDim_eq_trdeg [IsDomain A] : ringKrullDim A = (trdeg k A).toENat := by
  obtain ⟨n, h1, h2⟩ := exists_ringKrullDim_eq_trdeg (k := k) (A := A)
  rw [h1, h2]
  simp

include k in

/- English proof (translation)
Use `nontriviality A`. Take `⟨s, g, hinj, hint⟩` from `exists_integral_inj_algHom_of_fg k A`. Rewrite using `[ringKrullDim_eq_of_normalization k g hinj hint]`. Conclude with `WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top s)`.
-/
theorem ringKrullDim_lt_top : ringKrullDim A < ⊤ := by
  nontriviality A
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  rw [ringKrullDim_eq_of_normalization k g hinj hint]
  exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top s)

omit [Algebra.FiniteType k A] in

/- English proof (translation)
Establish `_ : FaithfulSMul A K` using `(faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective A K)`. Establish `_ : Algebra.IsAlgebraic A K` using `IsLocalization.isAlgebraic K (nonZeroDivisors A)`. Rewrite using `[← trdeg_add_eq k A (A := K), trdeg_eq_zero (R := A) (A := K), add_zero]`.
-/
theorem trdeg_eq_of_isFractionRing [IsDomain A] (K : Type u) [Field K] [Algebra A K]
    [IsFractionRing A K] [Algebra k K] [IsScalarTower k A K] : trdeg k K = trdeg k A := by
  have _ : FaithfulSMul A K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective A K)
  have _ : Algebra.IsAlgebraic A K := IsLocalization.isAlgebraic K (nonZeroDivisors A)
  rw [← trdeg_add_eq k A (A := K), trdeg_eq_zero (R := A) (A := K), add_zero]

/- English proof (translation)
Rewrite using `[trdeg_eq_of_isFractionRing (k := k) (A := A) K, ringKrullDim_eq_trdeg k]`.
-/
theorem ringKrullDim_eq_trdeg_fractionRing [IsDomain A] (K : Type u) [Field K] [Algebra A K]
    [IsFractionRing A K] [Algebra k K] [IsScalarTower k A K] :
    ringKrullDim A = (trdeg k K).toENat := by
  rw [trdeg_eq_of_isFractionRing (k := k) (A := A) K, ringKrullDim_eq_trdeg k]

end Normalization

section Drop

variable {A : Type u} [CommRing A] [IsDomain A]

/- English proof (translation)
Take `⟨r, hr, hr0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hp`. Conclude with `ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_of_ne_zero hr0) (Ideal.Quotient.eq_zero_iff_mem.mpr hr)`.
-/
theorem ringKrullDim_quotient_add_one_le (p : Ideal A) (hp : p ≠ ⊥) :
    ringKrullDim (A ⧸ p) + 1 ≤ ringKrullDim A := by
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
  exact ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
    (mem_nonZeroDivisors_of_ne_zero hr0) (Ideal.Quotient.eq_zero_iff_mem.mpr hr)

end Drop

section Hypersurface

variable (k : Type u) [Field k]

/- English proof (translation)
Establish `hg0 : g ≠ 0` using `hg.ne_zero`. Take `⟨i, hi⟩ : ∃ i, g.degreeOf i ≠ 0` from `by by_contra! h`. Establish `hv : g.vars = ∅`. Use extensionality with `i`. Simplify using `[MvPolynomial.mem_vars_iff_degreeOf_ne_zero, h i]`.

Rewrite `hv` using `[MvPolynomial.vars_eq_empty_iff_eq_C]`. Establish `hc : g.coeff 0 ≠ 0` using `fun h0 => hg0 (by rw [hv, h0, map_zero])`. Conclude with `hg.not_isUnit (hv ▸ ((isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C))`. Set `x : {j : Fin s // j ≠ i} → MvPolynomial (Fin s) k ⧸ Ideal.span {g}` to `fun j => Ideal.Quotient.mk _ (MvPolynomial.X j.1)`. Establish `hx : AlgebraicIndependent k x`.

Rewrite using `[algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]`. Introduce `h hh`. Establish `e' : (MvPolynomial.aeval x : MvPolynomial _ k →ₐ[k] _) = (Ideal.Quotient.mkₐ k (Ideal.span {g})).comp (MvPolynomial.rename Subtype.val)` using `MvPolynomial.algHom_ext fun j => by simp [x]`. Establish `e : MvPolynomial.aeval x h = Ideal.Quotient.mk _ (MvPolynomial.rename Subtype.val h)`. Rewrite using `[e']`.

Both sides reduce to the same expression. Rewrite `hh` using `[e, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`. Take `⟨c, hc⟩` from `hh`. Establish `hdeg : (MvPolynomial.rename Subtype.val h).degreeOf i = 0`. Assume the negation of the conclusion as `hne`.

Rewrite `hne` using `[← ne_eq, ← MvPolynomial.mem_vars_iff_degreeOf_ne_zero]`. Take `⟨j, -, hj⟩` from `Finset.mem_image.mp (MvPolynomial.vars_rename _ _ hne)`. Conclude with `j.2 hj`. Distinguish the cases in `hc0 : c = 0`. Rewrite `hc` using `[hc0, mul_zero]`.

Conclude with `MvPolynomial.rename_injective _ Subtype.val_injective (by simpa using hc)`. Rewrite `hdeg` using `[hc, MvPolynomial.degreeOf_mul_eq hg0 hc0]`. Use linear arithmetic over natural numbers and integers. Establish `h1` using `hx.lift_cardinalMk_le_trdeg`. Establish `hcard : Fintype.card {j : Fin s // j ≠ i} = s - 1`.

Rewrite using `[Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]`. Rewrite `h1` using `[Cardinal.mk_fintype, hcard, Cardinal.lift_natCast]`. Simplify using `using h1`.
-/
theorem sub_one_le_trdeg_quotient_span_prime {s : ℕ} {g : MvPolynomial (Fin s) k} (hg : Prime g) :
    ((s - 1 : ℕ) : Cardinal) ≤ trdeg k (MvPolynomial (Fin s) k ⧸ Ideal.span {g}) := by
  classical
  have hg0 : g ≠ 0 := hg.ne_zero

  obtain ⟨i, hi⟩ : ∃ i, g.degreeOf i ≠ 0 := by
    by_contra! h
    have hv : g.vars = ∅ := by
      ext i
      simp [MvPolynomial.mem_vars_iff_degreeOf_ne_zero, h i]
    rw [MvPolynomial.vars_eq_empty_iff_eq_C] at hv
    have hc : g.coeff 0 ≠ 0 := fun h0 => hg0 (by rw [hv, h0, map_zero])
    exact hg.not_isUnit (hv ▸ ((isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C))
  let x : {j : Fin s // j ≠ i} → MvPolynomial (Fin s) k ⧸ Ideal.span {g} :=
    fun j => Ideal.Quotient.mk _ (MvPolynomial.X j.1)
  have hx : AlgebraicIndependent k x := by
    rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
    intro h hh
    have e' : (MvPolynomial.aeval x : MvPolynomial _ k →ₐ[k] _) =
        (Ideal.Quotient.mkₐ k (Ideal.span {g})).comp (MvPolynomial.rename Subtype.val) :=
      MvPolynomial.algHom_ext fun j => by simp [x]
    have e : MvPolynomial.aeval x h =
        Ideal.Quotient.mk _ (MvPolynomial.rename Subtype.val h) := by
      rw [e']
      rfl
    rw [e, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hh
    obtain ⟨c, hc⟩ := hh
    have hdeg : (MvPolynomial.rename Subtype.val h).degreeOf i = 0 := by
      by_contra hne
      rw [← ne_eq, ← MvPolynomial.mem_vars_iff_degreeOf_ne_zero] at hne
      obtain ⟨j, -, hj⟩ := Finset.mem_image.mp (MvPolynomial.vars_rename _ _ hne)
      exact j.2 hj
    by_cases hc0 : c = 0
    · rw [hc0, mul_zero] at hc
      exact MvPolynomial.rename_injective _ Subtype.val_injective (by simpa using hc)
    · rw [hc, MvPolynomial.degreeOf_mul_eq hg0 hc0] at hdeg
      omega
  have h1 := hx.lift_cardinalMk_le_trdeg
  have hcard : Fintype.card {j : Fin s // j ≠ i} = s - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
  rw [Cardinal.mk_fintype, hcard, Cardinal.lift_natCast] at h1
  simpa using h1

end Hypersurface

section Formula

variable (k : Type u) [Field k] {A : Type u} [CommRing A] [IsDomain A] [Algebra k A]
  [Algebra.FiniteType k A]

include k in

/- English proof (translation)
Take `⟨s, g, hinj, hint⟩` from `exists_integral_inj_algHom_of_fg k A`. Set `_ : Algebra (MvPolynomial (Fin s) k) A` to `g.toRingHom.toAlgebra`. Establish `_ : IsScalarTower k (MvPolynomial (Fin s) k) A` using `IsScalarTower.of_algebraMap_eq fun c => (g.commutes c).symm`. Establish `_ : Algebra.IsIntegral (MvPolynomial (Fin s) k) A` using `⟨fun x => hint x⟩`. Establish `_ : FaithfulSMul (MvPolynomial (Fin s) k) A` using `(faithfulSMul_iff_algebraMap_injective _ _).2 hinj`.

Establish `_ : IsNoetherianRing A` using `Algebra.FiniteType.isNoetherianRing k A`. Establish `hdimA : ringKrullDim A = s` using `ringKrullDim_eq_of_normalization k g hinj hint`. Use `set q : Ideal (MvPolynomial (Fin s) k) := p.under (MvPolynomial (Fin s) k) with hq`. Establish `hpne : p ≠ ⊥` using `fun h => by rw [h, Ideal.height_bot] at hp; exact zero_ne_one hp`. Establish `hqne : q ≠ ⊥` using `Ideal.under_ne_bot _ hpne`.

Establish `hqle : q.height ≤ 1`. Establish `h` using `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q p`. Rewrite using `[← hp, h]`. Conclude with `le_self_add`. Take `⟨f, hfq, hf⟩` from `Ideal.IsPrime.exists_mem_prime_of_ne_bot (inferInstance : q.IsPrime) hqne`.

Establish `hspan : Ideal.span {f} = q`. Assume the negation of the conclusion as `hne`. Establish `hlt : Ideal.span {f} < q` using `lt_of_le_of_ne ((Ideal.span_singleton_le_iff_mem _).2 hfq) hne`. Establish `_ : (Ideal.span {f}).IsPrime` using `(Ideal.span_singleton_prime hf.ne_zero).2 hf`. Establish `h0 : (⊥ : Ideal (MvPolynomial (Fin s) k)) < Ideal.span {f}`.

Rewrite using `[bot_lt_iff_ne_bot, ne_eq, Ideal.span_singleton_eq_bot]`. Conclude with `hf.ne_zero`. Establish `h1` using `Ideal.height_add_one_le_of_lt_of_isPrime h0`. Establish `h2` using `Ideal.height_add_one_le_of_lt_of_isPrime hlt`. Rewrite `h1` using `[Ideal.height_bot, zero_add]`.

Establish `: (2 : ℕ∞) ≤ q.height` using `le_trans (by`. Combine the equalities or inequalities in the displayed calculation. Conclude with `absurd (this.trans hqle) (by decide)`. Establish `hdimq : ringKrullDim (A ⧸ p) = ringKrullDim (MvPolynomial (Fin s) k ⧸ q)` using `GroundTheory.Arith.Toric.ringKrullDim_eq_of_isIntegral (Ideal.algebraMap_quotient_injective)`. Establish `_ : (Ideal.span {f}).IsPrime` using `(Ideal.span_singleton_prime hf.ne_zero).2 hf`.

Take `⟨m, hm, htr⟩` from `exists_ringKrullDim_eq_trdeg (k := k) (A := MvPolynomial (Fin s) k ⧸ Ideal.span {f})`. Establish `hsm : s - 1 ≤ m`. Use `sub_one_le_trdeg_quotient_span_prime k hf` as an intermediate fact. Rewrite `this` using `[htr]`. Conclude with `this` after adjusting the coercions.

Rewrite using `[hdimA, hdimq, ← hspan, hm]`. Establish `: s ≤ m + 1` using `by omega`. Conclude with `this` after adjusting the coercions.
-/
theorem ringKrullDim_le_ringKrullDim_quotient_add_one (p : Ideal A) [p.IsPrime]
    (hp : p.height = 1) : ringKrullDim A ≤ ringKrullDim (A ⧸ p) + 1 := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  let _ : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  have _ : IsScalarTower k (MvPolynomial (Fin s) k) A :=
    IsScalarTower.of_algebraMap_eq fun c => (g.commutes c).symm
  have _ : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨fun x => hint x⟩
  have _ : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have _ : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hdimA : ringKrullDim A = s := ringKrullDim_eq_of_normalization k g hinj hint
  set q : Ideal (MvPolynomial (Fin s) k) := p.under (MvPolynomial (Fin s) k) with hq
  have hpne : p ≠ ⊥ := fun h => by rw [h, Ideal.height_bot] at hp; exact zero_ne_one hp
  have hqne : q ≠ ⊥ := Ideal.under_ne_bot _ hpne

  have hqle : q.height ≤ 1 := by
    have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q p
    rw [← hp, h]
    exact le_self_add

  obtain ⟨f, hfq, hf⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot (inferInstance : q.IsPrime) hqne
  have hspan : Ideal.span {f} = q := by
    by_contra hne
    have hlt : Ideal.span {f} < q :=
      lt_of_le_of_ne ((Ideal.span_singleton_le_iff_mem _).2 hfq) hne
    have _ : (Ideal.span {f}).IsPrime := (Ideal.span_singleton_prime hf.ne_zero).2 hf
    have h0 : (⊥ : Ideal (MvPolynomial (Fin s) k)) < Ideal.span {f} := by
      rw [bot_lt_iff_ne_bot, ne_eq, Ideal.span_singleton_eq_bot]
      exact hf.ne_zero
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime h0
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    rw [Ideal.height_bot, zero_add] at h1
    have : (2 : ℕ∞) ≤ q.height := le_trans (by
      calc (2 : ℕ∞) = 1 + 1 := by norm_num
        _ ≤ (Ideal.span {f}).height + 1 := by gcongr) h2
    exact absurd (this.trans hqle) (by decide)

  have hdimq : ringKrullDim (A ⧸ p) = ringKrullDim (MvPolynomial (Fin s) k ⧸ q) :=
    GroundTheory.Arith.Toric.ringKrullDim_eq_of_isIntegral (Ideal.algebraMap_quotient_injective)

  have _ : (Ideal.span {f}).IsPrime := (Ideal.span_singleton_prime hf.ne_zero).2 hf
  obtain ⟨m, hm, htr⟩ := exists_ringKrullDim_eq_trdeg (k := k)
    (A := MvPolynomial (Fin s) k ⧸ Ideal.span {f})
  have hsm : s - 1 ≤ m := by
    have := sub_one_le_trdeg_quotient_span_prime k hf
    rw [htr] at this
    exact_mod_cast this
  rw [hdimA, hdimq, ← hspan, hm]
  have : s ≤ m + 1 := by omega
  exact_mod_cast this

omit [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] in

/- English proof (translation)
Rewrite using `[ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]`. Use `Order.krullDim_eq_of_orderIso (OrderIso.setCongr _ _ ?_)` and prove the remaining obligations. Use extensionality with `q`. Simplify using `[PrimeSpectrum.mem_zeroLocus, ← PrimeSpectrum.asIdeal_le_asIdeal]`.
-/
lemma coheight_eq_ringKrullDim_quotient (p : PrimeSpectrum A) :
    (Order.coheight p : WithBot ℕ∞) = ringKrullDim (A ⧸ p.asIdeal) := by
  rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]
  refine Order.krullDim_eq_of_orderIso (OrderIso.setCongr _ _ ?_)
  ext q
  simp [PrimeSpectrum.mem_zeroLocus, ← PrimeSpectrum.asIdeal_le_asIdeal]

omit [Algebra k A] [Algebra.FiniteType k A] in

/- English proof (translation)
Establish `_ : (p.map (Ideal.Quotient.mk p₁)).IsPrime` using `Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])`. Take `⟨l, hl, hlen⟩` from `(p.map (Ideal.Quotient.mk p₁)).exists_ltSeries_length_eq_height`. Set `l'` to `l.map (PrimeSpectrum.comap (Ideal.Quotient.mk p₁)) (RingHom.strictMono_comap_of_surjective Ideal.Quotient.mk_surjective)`. Establish `hhead : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) < l'.head`. Rewrite using `[← PrimeSpectrum.asIdeal_lt_asIdeal, bot_lt_iff_ne_bot]`.

Introduce `hb`. Apply `h0` to reduce the goal to its premises. Rewrite using `[eq_bot_iff, ← hb]`. Simplify using `only [l', LTSeries.head_map, PrimeSpectrum.comap_asIdeal]`. Introduce `x hx`.

Rewrite using `[Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]`. Conclude with `Ideal.zero_mem _`. Set `l''` to `l'.cons _ hhead`. Establish `hlast : l''.last = ⟨p, inferInstance⟩` using `by ext1`. Simplify using `only [l'', l', RelSeries.last_cons, LTSeries.last_map, hl, PrimeSpectrum.comap_asIdeal]`.

Rewrite using `[Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr h]`. Establish `hle` using `Order.length_le_height hlast.le`. Rewrite `hle` using `[← PrimeSpectrum.height_eq_orderHeight]`. Simplify `hle` using `[l'', l', ← hlen]`.
-/
lemma height_map_quotient_add_one_le [IsNoetherianRing A] {p₁ p : Ideal A} [p₁.IsPrime]
    [p.IsPrime] (h : p₁ ≤ p) (h0 : p₁ ≠ ⊥) :
    (p.map (Ideal.Quotient.mk p₁)).height + 1 ≤ p.height := by
  have _ : (p.map (Ideal.Quotient.mk p₁)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  obtain ⟨l, hl, hlen⟩ := (p.map (Ideal.Quotient.mk p₁)).exists_ltSeries_length_eq_height
  let l' := l.map (PrimeSpectrum.comap (Ideal.Quotient.mk p₁))
    (RingHom.strictMono_comap_of_surjective Ideal.Quotient.mk_surjective)
  have hhead : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) < l'.head := by
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal, bot_lt_iff_ne_bot]
    intro hb
    apply h0
    rw [eq_bot_iff, ← hb]
    simp only [l', LTSeries.head_map, PrimeSpectrum.comap_asIdeal]
    intro x hx
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact Ideal.zero_mem _
  let l'' := l'.cons _ hhead
  have hlast : l''.last = ⟨p, inferInstance⟩ := by
    ext1
    simp only [l'', l', RelSeries.last_cons, LTSeries.last_map, hl, PrimeSpectrum.comap_asIdeal]
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr h]
  have hle := Order.length_le_height hlast.le
  rw [← PrimeSpectrum.height_eq_orderHeight] at hle
  simpa [l'', l', ← hlen] using hle

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `A _ _ _ _ hA p _`. Establish `_ : IsNoetherianRing A` using `Algebra.FiniteType.isNoetherianRing k A`.

Distinguish the cases in `hp : p = ⊥`. Substitute `hp` using the available equality. Rewrite using `[Ideal.height_bot, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot A)]`. Simplify using the standard rewrite rules. Take `⟨a, ha, ha0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hp`.

Take `⟨p₁, hp₁min, hp₁le⟩` from `Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem _).2 ha)`. Establish `_ : p₁.IsPrime` using `hp₁min.1.1`. Establish `hp₁ne : p₁ ≠ ⊥` using `fun h => ha0 (by`. Use `hp₁min.1.2 (Ideal.mem_span_singleton_self a)` as an intermediate fact. Rewrite `this` using `[h]`.

Simplify using `using this)`. Establish `hht : p₁.height = 1`. Use `le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hp₁min) ?_` and prove the remaining obligations. Use `Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.2 hp₁ne)` as an intermediate fact. Simplify using `using this`.

Establish `hC1` using `ringKrullDim_le_ringKrullDim_quotient_add_one k p₁ hht`. Establish `hdrop` using `ringKrullDim_quotient_add_one_le p₁ hp₁ne`. Take `⟨m, hm, -⟩` from `exists_ringKrullDim_eq_trdeg (k := k) (A := A ⧸ p₁)`. Establish `hmn : m < n`. Rewrite `hdrop` using `[hm, hA]`.

Establish `: ((m + 1 : ℕ) : WithBot ℕ∞) ≤ n` using `by exact_mod_cast hdrop`. Establish `: m + 1 ≤ n` using `by exact_mod_cast this`. Use linear arithmetic over natural numbers and integers. Establish `_ : (p.map (Ideal.Quotient.mk p₁)).IsPrime` using `Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])`. Establish `ih'` using `ih m hmn (A ⧸ p₁) hm (p.map (Ideal.Quotient.mk p₁))`.

Establish `e : ringKrullDim ((A ⧸ p₁) ⧸ p.map (Ideal.Quotient.mk p₁)) = ringKrullDim (A ⧸ p)` using `ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hp₁le)`. Establish `hh` using `height_map_quotient_add_one_le hp₁le hp₁ne`. Rewrite `ih'` using `[e]`. Combine the equalities or inequalities in the displayed calculation. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ p.height + ringKrullDim (A ⧸ p) := by gcongr; exact_mod_cast hh`.
-/
theorem ringKrullDim_le_height_add_ringKrullDim_quotient : ∀ (n : ℕ) (A : Type u) [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A], ringKrullDim A = n →
    ∀ (p : Ideal A) [p.IsPrime], ringKrullDim A ≤ p.height + ringKrullDim (A ⧸ p) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A _ _ _ _ hA p _
  have _ : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  by_cases hp : p = ⊥
  · subst hp
    rw [Ideal.height_bot, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot A)]
    simp
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
  obtain ⟨p₁, hp₁min, hp₁le⟩ :=
    Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem _).2 ha)
  have _ : p₁.IsPrime := hp₁min.1.1
  have hp₁ne : p₁ ≠ ⊥ := fun h => ha0 (by
    have := hp₁min.1.2 (Ideal.mem_span_singleton_self a)
    rw [h] at this
    simpa using this)
  have hht : p₁.height = 1 := by
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hp₁min) ?_
    have := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.2 hp₁ne)
    simpa using this
  have hC1 := ringKrullDim_le_ringKrullDim_quotient_add_one k p₁ hht
  have hdrop := ringKrullDim_quotient_add_one_le p₁ hp₁ne
  obtain ⟨m, hm, -⟩ := exists_ringKrullDim_eq_trdeg (k := k) (A := A ⧸ p₁)
  have hmn : m < n := by
    rw [hm, hA] at hdrop
    have : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ n := by exact_mod_cast hdrop
    have : m + 1 ≤ n := by exact_mod_cast this
    omega
  have _ : (p.map (Ideal.Quotient.mk p₁)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have ih' := ih m hmn (A ⧸ p₁) hm (p.map (Ideal.Quotient.mk p₁))
  have e : ringKrullDim ((A ⧸ p₁) ⧸ p.map (Ideal.Quotient.mk p₁)) = ringKrullDim (A ⧸ p) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hp₁le)
  have hh := height_map_quotient_add_one_le hp₁le hp₁ne
  rw [e] at ih'
  calc ringKrullDim A ≤ ringKrullDim (A ⧸ p₁) + 1 := hC1
    _ ≤ ((p.map (Ideal.Quotient.mk p₁)).height + ringKrullDim (A ⧸ p)) + 1 := by gcongr
    _ = (((p.map (Ideal.Quotient.mk p₁)).height + 1 : ℕ∞) : WithBot ℕ∞) + ringKrullDim (A ⧸ p) := by
      push_cast
      ring
    _ ≤ p.height + ringKrullDim (A ⧸ p) := by gcongr; exact_mod_cast hh

include k in

/- English proof (translation)
Use `le_antisymm ?_ ?_` and prove the remaining obligations. Rewrite using `[← coheight_eq_ringKrullDim_quotient (⟨p, inferInstance⟩ : PrimeSpectrum A), show p.height = (⟨p, inferInstance⟩ : PrimeSpectrum A).asIdeal.height from rfl, PrimeSpectrum.height_eq_orderHeight, ringKrullDim, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]`. Conclude with `le_iSup (fun a : PrimeSpectrum A => Order.height a + Order.coheight a) _` after adjusting the coercions. Take `⟨n, hn, -⟩` from `exists_ringKrullDim_eq_trdeg (k := k) (A := A)`. Conclude with `ringKrullDim_le_height_add_ringKrullDim_quotient k n A hn p`.
-/
theorem height_add_ringKrullDim_quotient (p : Ideal A) [p.IsPrime] :
    (p.height : WithBot ℕ∞) + ringKrullDim (A ⧸ p) = ringKrullDim A := by
  refine le_antisymm ?_ ?_
  · rw [← coheight_eq_ringKrullDim_quotient (⟨p, inferInstance⟩ : PrimeSpectrum A),
      show p.height = (⟨p, inferInstance⟩ : PrimeSpectrum A).asIdeal.height from rfl,
      PrimeSpectrum.height_eq_orderHeight, ringKrullDim,
      Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
    exact_mod_cast le_iSup (fun a : PrimeSpectrum A => Order.height a + Order.coheight a) _
  · obtain ⟨n, hn, -⟩ := exists_ringKrullDim_eq_trdeg (k := k) (A := A)
    exact ringKrullDim_le_height_add_ringKrullDim_quotient k n A hn p

end Formula

end GroundTheory.Arith.Abelian.Jacobian
