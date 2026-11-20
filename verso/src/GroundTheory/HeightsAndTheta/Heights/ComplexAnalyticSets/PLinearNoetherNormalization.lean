import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

/- English proof (translation)
Rewrite using `[ringKrullDim_quotient]`. Use `iSup_le fun l => ?_` and prove the remaining obligations. Take `⟨W, hW, hle⟩` from `Ideal.exists_minimalPrimes_le (show J ≤ l.head.1.asIdeal from l.head.2)`. Set `l' : LTSeries (PrimeSpectrum.zeroLocus (R` to `R) W) := ⟨l.length, fun i => ⟨(l i).1, show (W : Set R) ⊆ (l i).1.asIdeal from hle.trans (l.head_le i)⟩, fun i => l.step i⟩`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem LinearNoetherNormalization.ringKrullDim_quotient_le {R : Type*} [CommRing R] (J : Ideal R)
    (k : WithBot ℕ∞) (h : ∀ W ∈ J.minimalPrimes, ringKrullDim (R ⧸ W) ≤ k) :
    ringKrullDim (R ⧸ J) ≤ k := by
  rw [ringKrullDim_quotient]
  refine iSup_le fun l => ?_
  obtain ⟨W, hW, hle⟩ := Ideal.exists_minimalPrimes_le (show J ≤ l.head.1.asIdeal from l.head.2)
  let l' : LTSeries (PrimeSpectrum.zeroLocus (R := R) W) :=
    ⟨l.length, fun i => ⟨(l i).1, show (W : Set R) ⊆ (l i).1.asIdeal from hle.trans (l.head_le i)⟩,
      fun i => l.step i⟩
  calc (l.length : WithBot ℕ∞) = l'.length := rfl
    _ ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := R) W) := Order.LTSeries.length_le_krullDim l'
    _ = ringKrullDim (R ⧸ W) := (ringKrullDim_quotient W).symm
    _ ≤ k := h W hW

/- English proof (translation)
Proceed by induction on `x using WithBot.recBotCoe with`. Consider the case `bot => exact absurd h0 (by simp)`. Consider the case `coe y`. Proceed by induction on `y using ENat.recTopCoe with`. Consider the case `top`.

It suffices to derive a contradiction. Establish `h1 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((d : ℕ∞) : WithBot ℕ∞)` using `by exact_mod_cast hd`. Conclude with `absurd (WithBot.coe_le_coe.mp h1) (by simp)`. Consider the case `coe e => exact ⟨e, by exact_mod_cast hd, rfl⟩`.
-/
theorem LinearNoetherNormalization.exists_nat_of_le {x : WithBot ℕ∞} {d : ℕ} (h0 : 0 ≤ x)
    (hd : x ≤ d) : ∃ e : ℕ, e ≤ d ∧ x = e := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h0 (by simp)
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      have h1 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((d : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast hd
      exact absurd (WithBot.coe_le_coe.mp h1) (by simp)
    | coe e => exact ⟨e, by exact_mod_cast hd, rfl⟩

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `i`. Simplify using `[pullback, linPoly, Matrix.submatrix]`.
-/
theorem LinearNoetherNormalization.pullback_comp_rename {d e n : ℕ} (h : e ≤ d)
    (A : Matrix (Fin d) (Fin n) ℂ) :
    (pullback A).comp (rename (Fin.castLE h)) = pullback (A.submatrix (Fin.castLE h) id) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [pullback, linPoly, Matrix.submatrix]

/- English proof (translation)
Take `⟨g, hg, hg0⟩` from `hP.finite.to_isIntegral (Ideal.Quotient.mk P (X j))`. Use `⟨g.map (rename (R := ℂ) (Fin.castLE h)).toRingHom, hg.map _, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map, ← Ideal.Quotient.eq_zero_iff_mem, Polynomial.hom_eval₂]`. Use `(congrArg (fun φ => Polynomial.eval₂ φ (Ideal.Quotient.mk P (X j)) g) ?_).trans hg0` and prove the remaining obligations. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises.

Introduce `r`. Simplify using `[projHom, pullback]`. Both sides reduce to the same expression. Introduce `i`. Simplify using `[projHom, pullback, linPoly]`.
-/
theorem LinearNoetherNormalization.exists_monic_of_prefix {d e n : ℕ} (h : e ≤ d)
    (A : Matrix (Fin d) (Fin n) ℂ) (P : Ideal (MvPolynomial (Fin n) ℂ))
    (hP : IsFiniteProjection P (A.submatrix (Fin.castLE h) id)) (j : Fin n) :
    ∃ f : Polynomial (MvPolynomial (Fin d) ℂ), f.Monic ∧
      f.eval₂ (pullback A).toRingHom (X j) ∈ P := by
  obtain ⟨g, hg, hg0⟩ := hP.finite.to_isIntegral (Ideal.Quotient.mk P (X j))
  refine ⟨g.map (rename (R := ℂ) (Fin.castLE h)).toRingHom, hg.map _, ?_⟩
  rw [Polynomial.eval₂_map, ← Ideal.Quotient.eq_zero_iff_mem, Polynomial.hom_eval₂]
  refine (congrArg (fun φ => Polynomial.eval₂ φ (Ideal.Quotient.mk P (X j)) g) ?_).trans hg0
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [projHom, pullback]
    rfl
  · intro i
    simp [projHom, pullback, linPoly]

/- English proof (translation)
Introduce `n d J hJ`. Establish `hdim : ∀ P ∈ J.minimalPrimes, ∃ e : ℕ, e ≤ d ∧ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) = e`. Introduce `P hP`. Establish `: P.IsPrime` using `hP.1.1`. Use `LinearNoetherNormalization.exists_nat_of_le ringKrullDim_nonneg_of_nontrivial ?_` and prove the remaining obligations.

Rewrite using `[← hJ]`. Conclude with `ringKrullDim_le_of_surjective (Ideal.Quotient.factor hP.1.2) (Ideal.Quotient.factor_surjective hP.1.2)`. Establish `htop : ∃ P ∈ J.minimalPrimes, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) = d`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`.

Break down `d with _ | d'` into its components or cases. Establish `hJt : J ≠ ⊤`. Introduce and unpack `rfl`. Establish `: Subsingleton (MvPolynomial (Fin n) ℂ ⧸ (⊤ : Ideal (MvPolynomial (Fin n) ℂ)))` using `Ideal.Quotient.subsingleton_iff.mpr rfl`. Rewrite `hJ` using `[ringKrullDim_eq_bot_of_subsingleton]`.

Simplify using `at hJ`. Take `⟨M, hM, hJM⟩` from `Ideal.exists_le_maximal J hJt`. Take `⟨P, hP, -⟩` from `Ideal.exists_minimalPrimes_le (J := M) hJM`. Take `⟨e, he, he'⟩` from `hdim P hP`. Conclude with `hne P hP (by rw [he', Nat.le_zero.mp he])`.

Establish `hle` using `LinearNoetherNormalization.ringKrullDim_quotient_le J (d' : WithBot ℕ∞) (fun P hP => by`. Take `⟨e, he, he'⟩` from `hdim P hP`. Establish `hne' : e ≠ d' + 1` using `fun h => hne P hP (by rw [he', h])`. Rewrite using `[he']`. Conclude with `(by omega : e ≤ d'))` after adjusting the coercions.

Rewrite `hle` using `[hJ]`. Conclude with `absurd hle (by norm_cast; omega)`. Take `⟨P₀, hP₀, hP₀d⟩` from `htop`. Establish `hP₀p : P₀.IsPrime` using `hP₀.1.1`. Take `⟨W₀, ⟨S₀, rfl⟩, ⟨A₀, p₀, hp₀S, hp₀⟩, hW₀⟩` from `FiniteProjectionsContainOpen.full n d P₀ hP₀p hP₀d`.

Establish `hp₀0 : p₀ ≠ 0` using `fun h => hp₀ (by rw [h, map_zero])`. Establish `hq : ∀ P ∈ J.minimalPrimes, ∃ q : MvPolynomial (Fin d × Fin n) ℂ, q ≠ 0 ∧ ∀ A : Matrix (Fin d) (Fin n) ℂ, eval (fun ij : Fin d × Fin n => A ij.1 ij.2) q ≠ 0 → ∀ j, ∃ f : Polynomial (MvPolynomial (Fin d) ℂ), f.Monic ∧ f.eval₂ (pullback A).toRingHom (X j) ∈ P`. Introduce `P hP`. Establish `: P.IsPrime` using `hP.1.1`. Take `⟨e, he, hPe⟩` from `hdim P hP`.

Take `⟨W, ⟨S, rfl⟩, ⟨B, p, hpS, hp⟩, hW⟩` from `FiniteProjectionsContainOpen.full n e P this hPe`. Use `⟨rename (Prod.map (Fin.castLE he) id) p, fun h0 => ?_, fun A hA j => ?_⟩` and prove the remaining obligations. Apply `hp` to reduce the goal to its premises. Rewrite using `[rename_injective _ ((Fin.castLE_injective he).prodMap Function.injective_id) (h0.trans (map_zero _).symm), map_zero]`. Rewrite `hA` using `[eval_rename]`.

Conclude with `LinearNoetherNormalization.exists_monic_of_prefix he A P (hW ⟨p, hpS, hA⟩) j`. Use `choose! q hq0 hqA using hq`. Establish `hfin` using `Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) ℂ) J`. Establish `hQ : p₀ * ∏ P ∈ hfin.toFinset, q P ≠ 0` using `mul_ne_zero hp₀0 (Finset.prod_ne_zero_iff.mpr fun P hP => hq0 P (hfin.mem_toFinset.mp hP))`. Take `⟨x, hx⟩ : ∃ x, eval x (p₀ * ∏ P ∈ hfin.toFinset, q P) ≠ 0` from `by by_contra! h`.

Conclude with `hQ (MvPolynomial.funext fun x => by rw [h x, map_zero])`. Set `A : Matrix (Fin d) (Fin n) ℂ` to `Matrix.of fun i j => x (i, j)`. Establish `hxA : (fun ij : Fin d × Fin n => A ij.1 ij.2) = x` using `rfl`. Rewrite `hx` using `[← hxA, map_mul, map_prod]`. Establish `hall` using `Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hx)`.

Establish `hA₀ : IsFiniteProjection P₀ A` using `hW₀ ⟨p₀, hp₀S, left_ne_zero_of_mul hx⟩`. Establish `hint : ∀ j, (projHom J A).toRingHom.IsIntegralElem (Ideal.Quotient.mk J (X j))`. Introduce `j`. Establish `hf : ∀ P ∈ J.minimalPrimes, ∃ f : Polynomial (MvPolynomial (Fin d) ℂ), f.Monic ∧ f.eval₂ (pullback A).toRingHom (X j) ∈ P` using `fun P hP => hqA P hP A (hall P (hfin.mem_toFinset.mpr hP)) j`. Use `choose! f hfm hfP using hf`.

Establish `hFm : (∏ P ∈ hfin.toFinset, f P).Monic` using `Polynomial.monic_prod_of_monic _ _ fun P hP => hfm P (hfin.mem_toFinset.mp hP)`. Establish `hFrad : (∏ P ∈ hfin.toFinset, f P).eval₂ (pullback A).toRingHom (X j) ∈ J.radical`. Rewrite using `[← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]`. Introduce `P hP`. Rewrite using `[show (∏ P ∈ hfin.toFinset, f P).eval₂ (pullback A).toRingHom (X j) = ∏ P ∈ hfin.toFinset, (f P).eval₂ (pullback A).toRingHom (X j) from map_prod (Polynomial.eval₂RingHom (pullback A).toRingHom (X j)) _ _]`.

Take `⟨c, hc⟩` from `Finset.dvd_prod_of_mem (fun P => (f P).eval₂ (pullback A).toRingHom (X j)) (hfin.mem_toFinset.mpr hP)`. Rewrite using `[hc]`. Conclude with `Ideal.mul_mem_right c P (hfP P hP)`. Take `⟨m, hm⟩` from `hFrad`. Use `⟨(∏ P ∈ hfin.toFinset, f P) ^ m, hFm.pow m, ?_⟩` and prove the remaining obligations.

Rewrite `hm` using `[← Polynomial.eval₂_pow, ← Ideal.Quotient.eq_zero_iff_mem, Polynomial.hom_eval₂]`. Conclude with `hm`. Use `⟨A, fun a b hab => hA₀.injective ?_, ?_⟩` and prove the remaining obligations. Establish `hfac : ∀ c, projHom P₀ A c = Ideal.Quotient.factor hP₀.1.2 (projHom J A c)` using `fun c => (Ideal.Quotient.factor_mk hP₀.1.2 _).symm`. Rewrite using `[hfac, hfac, hab]`.

Establish `hI : (projHom J A).toRingHom.IsIntegral`. Introduce `y`. Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a`.

Establish `: Ideal.Quotient.mk J (C a) = (projHom J A).toRingHom (C a)`. Simplify using `[projHom, pullback]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `(projHom J A).toRingHom.isIntegralElem_map`.

Consider the case `add p q hp hq => rw [map_add]`. Conclude with `RingHom.IsIntegralElem.add _ hp hq`. Consider the case `mul_X p i hp => rw [map_mul]`. Conclude with `RingHom.IsIntegralElem.mul _ hp (hint i)`. Use `hI.to_finite ?_` and prove the remaining obligations.

Apply `RingHom.FiniteType.of_comp_finiteType (f := algebraMap ℂ (MvPolynomial (Fin d) ℂ))` to reduce the goal to its premises. Rewrite using `[show (projHom J A).toRingHom.comp (algebraMap ℂ (MvPolynomial (Fin d) ℂ)) = algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ J) from (projHom J A).comp_algebraMap]`. Conclude with `RingHom.finiteType_algebraMap.mpr inferInstance`.
-/
theorem LinearNoetherNormalization.proof : LinearNoetherNormalization.Statement := by
  classical
  intro n d J hJ

  have hdim : ∀ P ∈ J.minimalPrimes, ∃ e : ℕ, e ≤ d ∧
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) = e := by
    intro P hP
    have : P.IsPrime := hP.1.1
    refine LinearNoetherNormalization.exists_nat_of_le ringKrullDim_nonneg_of_nontrivial ?_
    rw [← hJ]
    exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hP.1.2)
      (Ideal.Quotient.factor_surjective hP.1.2)

  have htop : ∃ P ∈ J.minimalPrimes, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) = d := by
    by_contra hne
    push Not at hne
    rcases d with _ | d'
    · have hJt : J ≠ ⊤ := by
        rintro rfl
        have : Subsingleton (MvPolynomial (Fin n) ℂ ⧸ (⊤ : Ideal (MvPolynomial (Fin n) ℂ))) :=
          Ideal.Quotient.subsingleton_iff.mpr rfl
        rw [ringKrullDim_eq_bot_of_subsingleton] at hJ
        simp at hJ
      obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hJt
      obtain ⟨P, hP, -⟩ := Ideal.exists_minimalPrimes_le (J := M) hJM
      obtain ⟨e, he, he'⟩ := hdim P hP
      exact hne P hP (by rw [he', Nat.le_zero.mp he])
    · have hle := LinearNoetherNormalization.ringKrullDim_quotient_le J (d' : WithBot ℕ∞)
        (fun P hP => by
          obtain ⟨e, he, he'⟩ := hdim P hP
          have hne' : e ≠ d' + 1 := fun h => hne P hP (by rw [he', h])
          rw [he']
          exact_mod_cast (by omega : e ≤ d'))
      rw [hJ] at hle
      exact absurd hle (by norm_cast; omega)
  obtain ⟨P₀, hP₀, hP₀d⟩ := htop
  have hP₀p : P₀.IsPrime := hP₀.1.1
  obtain ⟨W₀, ⟨S₀, rfl⟩, ⟨A₀, p₀, hp₀S, hp₀⟩, hW₀⟩ :=
    FiniteProjectionsContainOpen.full n d P₀ hP₀p hP₀d
  have hp₀0 : p₀ ≠ 0 := fun h => hp₀ (by rw [h, map_zero])

  have hq : ∀ P ∈ J.minimalPrimes, ∃ q : MvPolynomial (Fin d × Fin n) ℂ, q ≠ 0 ∧
      ∀ A : Matrix (Fin d) (Fin n) ℂ, eval (fun ij : Fin d × Fin n => A ij.1 ij.2) q ≠ 0 →
        ∀ j, ∃ f : Polynomial (MvPolynomial (Fin d) ℂ), f.Monic ∧
          f.eval₂ (pullback A).toRingHom (X j) ∈ P := by
    intro P hP
    have : P.IsPrime := hP.1.1
    obtain ⟨e, he, hPe⟩ := hdim P hP
    obtain ⟨W, ⟨S, rfl⟩, ⟨B, p, hpS, hp⟩, hW⟩ := FiniteProjectionsContainOpen.full n e P this hPe
    refine ⟨rename (Prod.map (Fin.castLE he) id) p, fun h0 => ?_, fun A hA j => ?_⟩
    · apply hp
      rw [rename_injective _ ((Fin.castLE_injective he).prodMap Function.injective_id)
        (h0.trans (map_zero _).symm), map_zero]
    · rw [eval_rename] at hA
      exact LinearNoetherNormalization.exists_monic_of_prefix he A P (hW ⟨p, hpS, hA⟩) j
  choose! q hq0 hqA using hq
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) ℂ) J
  have hQ : p₀ * ∏ P ∈ hfin.toFinset, q P ≠ 0 :=
    mul_ne_zero hp₀0 (Finset.prod_ne_zero_iff.mpr fun P hP => hq0 P (hfin.mem_toFinset.mp hP))

  obtain ⟨x, hx⟩ : ∃ x, eval x (p₀ * ∏ P ∈ hfin.toFinset, q P) ≠ 0 := by
    by_contra! h
    exact hQ (MvPolynomial.funext fun x => by rw [h x, map_zero])
  let A : Matrix (Fin d) (Fin n) ℂ := Matrix.of fun i j => x (i, j)
  have hxA : (fun ij : Fin d × Fin n => A ij.1 ij.2) = x := rfl
  rw [← hxA, map_mul, map_prod] at hx
  have hall := Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hx)
  have hA₀ : IsFiniteProjection P₀ A := hW₀ ⟨p₀, hp₀S, left_ne_zero_of_mul hx⟩

  have hint : ∀ j, (projHom J A).toRingHom.IsIntegralElem (Ideal.Quotient.mk J (X j)) := by
    intro j
    have hf : ∀ P ∈ J.minimalPrimes, ∃ f : Polynomial (MvPolynomial (Fin d) ℂ), f.Monic ∧
        f.eval₂ (pullback A).toRingHom (X j) ∈ P :=
      fun P hP => hqA P hP A (hall P (hfin.mem_toFinset.mpr hP)) j
    choose! f hfm hfP using hf
    have hFm : (∏ P ∈ hfin.toFinset, f P).Monic :=
      Polynomial.monic_prod_of_monic _ _ fun P hP => hfm P (hfin.mem_toFinset.mp hP)
    have hFrad : (∏ P ∈ hfin.toFinset, f P).eval₂ (pullback A).toRingHom (X j) ∈ J.radical := by
      rw [← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
      intro P hP
      rw [show (∏ P ∈ hfin.toFinset, f P).eval₂ (pullback A).toRingHom (X j) =
          ∏ P ∈ hfin.toFinset, (f P).eval₂ (pullback A).toRingHom (X j) from
        map_prod (Polynomial.eval₂RingHom (pullback A).toRingHom (X j)) _ _]
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem
        (fun P => (f P).eval₂ (pullback A).toRingHom (X j)) (hfin.mem_toFinset.mpr hP)
      rw [hc]
      exact Ideal.mul_mem_right c P (hfP P hP)
    obtain ⟨m, hm⟩ := hFrad
    refine ⟨(∏ P ∈ hfin.toFinset, f P) ^ m, hFm.pow m, ?_⟩
    rw [← Polynomial.eval₂_pow, ← Ideal.Quotient.eq_zero_iff_mem, Polynomial.hom_eval₂] at hm
    exact hm
  refine ⟨A, fun a b hab => hA₀.injective ?_, ?_⟩
  · have hfac : ∀ c, projHom P₀ A c = Ideal.Quotient.factor hP₀.1.2 (projHom J A c) :=
      fun c => (Ideal.Quotient.factor_mk hP₀.1.2 _).symm
    rw [hfac, hfac, hab]
  · have hI : (projHom J A).toRingHom.IsIntegral := by
      intro y
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
      induction p using MvPolynomial.induction_on with
      | C a =>
        have : Ideal.Quotient.mk J (C a) = (projHom J A).toRingHom (C a) := by
          simp [projHom, pullback]
          rfl
        rw [this]
        exact (projHom J A).toRingHom.isIntegralElem_map
      | add p q hp hq => rw [map_add]; exact RingHom.IsIntegralElem.add _ hp hq
      | mul_X p i hp => rw [map_mul]; exact RingHom.IsIntegralElem.mul _ hp (hint i)
    refine hI.to_finite ?_
    apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap ℂ (MvPolynomial (Fin d) ℂ))
    rw [show (projHom J A).toRingHom.comp (algebraMap ℂ (MvPolynomial (Fin d) ℂ)) =
      algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ J) from (projHom J A).comp_algebraMap]
    exact RingHom.finiteType_algebraMap.mpr inferInstance

end

end GroundTheory.Heights₂.Heights.ComplexSets
