import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsDimensionInequalitySteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

open Polynomial

/- English proof (translation)
Introduce `A _ _ _ P _`. Use `set p := P.under A with hp`. Set `I : Ideal A[X]` to `p.map (algebraMap A A[X])`. Set `Pb : Ideal (A[X] ⧸ I)` to `P.map (Ideal.Quotient.mk I)`. Establish `hIP : I ≤ P` using `Ideal.map_comap_le`.

Establish `hPb : Pb.IsPrime` using `Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hIP)`. Set `x : A[X] ⧸ P` to `Ideal.Quotient.mk P X`. Establish `key : ∀ f : A[X], aeval x (f.map (Ideal.Quotient.mk p)) = Ideal.Quotient.mk P f`. Introduce `f`. Rewrite using `[← Ideal.Quotient.algebraMap_eq, aeval_map_algebraMap]`.

Express the relevant statement in the definitionally equal form `aeval (Ideal.Quotient.mkₐ A P X) f = _`. Rewrite using `[aeval_algHom_apply, aeval_X_left_apply]`. Both sides reduce to the same expression. Establish `hsurj : Function.Surjective (aeval (R` using `A ⧸ p) x) := by`. Introduce `y`.

Take `⟨f, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Conclude with `⟨_, key f⟩`. Establish `hPb1 : Pb.height ≤ 1`. Set `e : (A[X] ⧸ I) ≃+* (A ⧸ p)[X]` to `(Ideal.polynomialQuotientEquivQuotientPolynomial p).symm`. Set `Q : Ideal (A ⧸ p)[X]` to `Pb.map e`.

Establish `hQ : Q.IsPrime` using `Ideal.map_isPrime_of_equiv e`. Establish `hQb : Q.comap (C : A ⧸ p →+* (A ⧸ p)[X]) = ⊥`. Use `le_bot_iff.mp fun a ha => ?_` and prove the remaining obligations. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Rewrite `ha` using `[Ideal.mem_comap]`.

Establish `he : C (Ideal.Quotient.mk p b) = e (Ideal.Quotient.mk I (C b))`. Express the relevant statement in the definitionally equal form `_ = (Ideal.polynomialQuotientEquivQuotientPolynomial p).symm (Ideal.Quotient.mk (p.map C) (C b))`. Rewrite using `[Ideal.polynomialQuotientEquivQuotientPolynomial_symm_mk, Polynomial.map_C]`. Rewrite `ha` using `[he]`. Take `⟨y, hy, hye⟩` from `(Ideal.mem_map_of_equiv e _).mp ha`.

Rewrite `hy` using `[e.injective hye, Ideal.mem_quotient_iff_mem hIP]`. Rewrite using `[Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem, hp, Ideal.under_def, Ideal.mem_comap, Polynomial.algebraMap_eq]`. Conclude with `hy`. Use `h (A ⧸ p) Q hQb` as an intermediate fact. Rewrite `this` using `[RingEquiv.height_map]`. Then use the resulting hypothesis.

Establish `hht : P.height ≤ p.height + Pb.height` using `Ideal.height_le_height_add_of_liesOver p P`. Distinguish the cases in `hb : Pb = ⊥`. Establish `: Nontrivial (A[X] ⧸ I)` using `Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (Ideal.IsPrime.ne_top inferInstance) hIP)`. Rewrite `hht` using `[hb, Ideal.height_bot, add_zero]`. Establish `htr : Algebra.trdeg (A ⧸ p) (A[X] ⧸ P) ≤ 1` using `(trdeg_le_of_surjective _ hsurj).trans (Polynomial.trdeg_of_isDomain).le`.

Conclude with `add_le_add (Cardinal.ofENat_le_ofENat.mpr hht) htr`. Take `⟨y, hyPb, hy0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hb`. Take `⟨f, hfP, rfl⟩` from `(Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hyPb`. Establish `hfI : f ∉ I` using `fun hf => hy0 (Ideal.Quotient.eq_zero_iff_mem.mpr hf)`. Establish `hg : f.map (Ideal.Quotient.mk p) ≠ 0`.

Introduce `hg`. Apply `hfI` to reduce the goal to its premises. Rewrite using `[show I = p.map C from rfl, Ideal.mem_map_C_iff]`. Introduce `n`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map, hg, coeff_zero]`.

Establish `hx : IsAlgebraic (A ⧸ p) x` using `⟨_, hg, by rw [key]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hfP⟩`. Establish `hadj : Algebra.adjoin (A ⧸ p) {x} = ⊤`. Rewrite using `[Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top]`. Conclude with `hsurj`. Establish `halg : Algebra.IsAlgebraic (A ⧸ p) (A[X] ⧸ P)`.

Use `Algebra.isAlgebraic_adjoin_singleton_iff.mpr hx` as an intermediate fact. Rewrite `this` using `[hadj]`. Conclude with `⟨fun z => this z Algebra.mem_top⟩`. Rewrite using `[trdeg_eq_zero_iff.mpr halg, add_zero, ← Cardinal.ofENat_one, ← Cardinal.ofENat_add, Cardinal.ofENat_le_ofENat]`. Conclude with `hht.trans (add_le_add le_rfl hPb1)`.
-/
theorem PolynomialDimensionInequality.proof (h : PolynomialPrimeOverZeroHeight.Statement.{u}) :
    PolynomialDimensionInequality.Statement.{u} := by
  intro A _ _ _ P _
  set p := P.under A with hp
  let I : Ideal A[X] := p.map (algebraMap A A[X])
  let Pb : Ideal (A[X] ⧸ I) := P.map (Ideal.Quotient.mk I)
  have hIP : I ≤ P := Ideal.map_comap_le
  have hPb : Pb.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hIP)

  let x : A[X] ⧸ P := Ideal.Quotient.mk P X
  have key : ∀ f : A[X], aeval x (f.map (Ideal.Quotient.mk p)) = Ideal.Quotient.mk P f := by
    intro f
    rw [← Ideal.Quotient.algebraMap_eq, aeval_map_algebraMap]
    change aeval (Ideal.Quotient.mkₐ A P X) f = _
    rw [aeval_algHom_apply, aeval_X_left_apply]
    rfl
  have hsurj : Function.Surjective (aeval (R := A ⧸ p) x) := by
    intro y
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨_, key f⟩

  have hPb1 : Pb.height ≤ 1 := by
    let e : (A[X] ⧸ I) ≃+* (A ⧸ p)[X] := (Ideal.polynomialQuotientEquivQuotientPolynomial p).symm
    let Q : Ideal (A ⧸ p)[X] := Pb.map e
    have hQ : Q.IsPrime := Ideal.map_isPrime_of_equiv e
    have hQb : Q.comap (C : A ⧸ p →+* (A ⧸ p)[X]) = ⊥ := by
      refine le_bot_iff.mp fun a ha => ?_
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [Ideal.mem_comap] at ha
      have he : C (Ideal.Quotient.mk p b) = e (Ideal.Quotient.mk I (C b)) := by
        change _ = (Ideal.polynomialQuotientEquivQuotientPolynomial p).symm
          (Ideal.Quotient.mk (p.map C) (C b))
        rw [Ideal.polynomialQuotientEquivQuotientPolynomial_symm_mk, Polynomial.map_C]
      rw [he] at ha
      obtain ⟨y, hy, hye⟩ := (Ideal.mem_map_of_equiv e _).mp ha
      rw [e.injective hye, Ideal.mem_quotient_iff_mem hIP] at hy
      rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem, hp, Ideal.under_def, Ideal.mem_comap,
        Polynomial.algebraMap_eq]
      exact hy
    have := h (A ⧸ p) Q hQb
    rwa [RingEquiv.height_map] at this
  have hht : P.height ≤ p.height + Pb.height := Ideal.height_le_height_add_of_liesOver p P
  by_cases hb : Pb = ⊥
  ·
    have : Nontrivial (A[X] ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (Ideal.IsPrime.ne_top inferInstance) hIP)
    rw [hb, Ideal.height_bot, add_zero] at hht
    have htr : Algebra.trdeg (A ⧸ p) (A[X] ⧸ P) ≤ 1 :=
      (trdeg_le_of_surjective _ hsurj).trans (Polynomial.trdeg_of_isDomain).le
    exact add_le_add (Cardinal.ofENat_le_ofENat.mpr hht) htr
  ·
    obtain ⟨y, hyPb, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    obtain ⟨f, hfP, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hyPb
    have hfI : f ∉ I := fun hf => hy0 (Ideal.Quotient.eq_zero_iff_mem.mpr hf)
    have hg : f.map (Ideal.Quotient.mk p) ≠ 0 := by
      intro hg
      apply hfI
      rw [show I = p.map C from rfl, Ideal.mem_map_C_iff]
      intro n
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map, hg, coeff_zero]
    have hx : IsAlgebraic (A ⧸ p) x :=
      ⟨_, hg, by rw [key]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hfP⟩
    have hadj : Algebra.adjoin (A ⧸ p) {x} = ⊤ := by
      rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top]
      exact hsurj
    have halg : Algebra.IsAlgebraic (A ⧸ p) (A[X] ⧸ P) := by
      have := Algebra.isAlgebraic_adjoin_singleton_iff.mpr hx
      rw [hadj] at this
      exact ⟨fun z => this z Algebra.mem_top⟩
    rw [trdeg_eq_zero_iff.mpr halg, add_zero, ← Cardinal.ofENat_one, ← Cardinal.ofENat_add,
      Cardinal.ofENat_le_ofENat]
    exact hht.trans (add_le_add le_rfl hPb1)

end GroundTheory.Heights₂.Heights.NumbersDVR
