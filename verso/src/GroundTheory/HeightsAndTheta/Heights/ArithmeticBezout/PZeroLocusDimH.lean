import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsZeroLocusDimH
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ZeroLocusDimHGeo
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ZeroLocusDimHAlg
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LeOfAddOneLeSucc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ZeroLocusDimH

/- English proof (translation)
Rewrite using `[Polynomial.hom_eval₂, Polynomial.eval_map, MvPolynomial.eval_X]`. Use `congr 1`. Use `MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using `[paramMap]`.
-/
theorem eval_eval₂_aeval {n s : ℕ} (π : Fin s → MvPolynomial (Fin n) ℂ)
    (Q : Polynomial (MvPolynomial (Fin s) ℂ)) (x : Fin n → ℂ) (i : Fin n) :
    MvPolynomial.eval x (Q.eval₂ (MvPolynomial.aeval π).toRingHom (X i)) =
      Polynomial.eval (x i) (Q.map (MvPolynomial.eval (paramMap π x))) := by
  rw [Polynomial.hom_eval₂, Polynomial.eval_map, MvPolynomial.eval_X]
  congr 1
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
  · simp
  · simp [paramMap]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h q hq => RingHom.mem_ker.2 (h q hq), fun h _ hq => RingHom.mem_ker.1 (h hq)⟩`.
-/
theorem mem_zeroSet_iff {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (x : Fin n → ℂ) :
    (∀ q ∈ I, MvPolynomial.eval x q = 0) ↔ I ≤ RingHom.ker (MvPolynomial.eval x) :=
  ⟨fun h q hq => RingHom.mem_ker.2 (h q hq), fun h _ hq => RingHom.mem_ker.1 (h hq)⟩

/- English proof (translation)
Establish `hne : Ideal.Quotient.mk p g ≠ 0` using `by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]`. Establish `h` using `ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hne)`. Establish `e : ((MvPolynomial (Fin n) ℂ ⧸ p) ⧸ Ideal.span {Ideal.Quotient.mk p g}) ≃+* MvPolynomial (Fin n) ℂ ⧸ (p ⊔ Ideal.span {g})` using `(Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])).trans (DoubleQuot.quotQuotEquivQuotSup p (Ideal.span {g}))`. Rewrite `h` using `[ringKrullDim_eq_of_ringEquiv e]`. Then use the resulting hypothesis.
-/
theorem ringKrullDim_quot_sup_add_one_le {n : ℕ} (p : Ideal (MvPolynomial (Fin n) ℂ)) [p.IsPrime]
    (g : MvPolynomial (Fin n) ℂ) (hg : g ∉ p) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (p ⊔ Ideal.span {g})) + 1 ≤
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) := by
  have hne : Ideal.Quotient.mk p g ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have h := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hne)
  have e : ((MvPolynomial (Fin n) ℂ ⧸ p) ⧸ Ideal.span {Ideal.Quotient.mk p g}) ≃+*
      MvPolynomial (Fin n) ℂ ⧸ (p ⊔ Ideal.span {g}) :=
    (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])).trans
      (DoubleQuot.quotQuotEquivQuotSup p (Ideal.span {g}))
  rwa [ringKrullDim_eq_of_ringEquiv e] at h

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qn14.le_of_add_one_le_succ h`.
-/
theorem le_of_add_one_le_succ {a : WithBot ℕ∞} {k : ℕ} (h : a + 1 ≤ ((k + 1 : ℕ) : WithBot ℕ∞)) :
    a ≤ (k : WithBot ℕ∞) :=
  _root_.UpperTheory.Reformulated.B.Qn14.le_of_add_one_le_succ h

/- English proof (translation)
Establish `hcover : {x : Fin n → ℂ | ∀ q ∈ J, MvPolynomial.eval x q = 0} ⊆ ⋃ p ∈ J.minimalPrimes, {x : Fin n → ℂ | ∀ q ∈ p, MvPolynomial.eval x q = 0}`. Introduce `x hx`. Rewrite `hx` using `[Set.mem_ofPred_eq, mem_zeroSet_iff]`. Establish `: (RingHom.ker (MvPolynomial.eval x)).IsPrime` using `RingHom.ker_isPrime _`. Take `⟨p, hp, hpx⟩` from `Ideal.exists_minimalPrimes_le hx`.

Conclude with `Set.mem_biUnion hp ((mem_zeroSet_iff p x).2 hpx)`. Use `(dimH_mono hcover).trans ?_` and prove the remaining obligations. Rewrite using `[dimH_bUnion (Ideal.finite_minimalPrimes_of_isNoetherianRing _ J).countable]`. Use `iSup₂_le fun p hp => ?_` and prove the remaining obligations. Establish `: p.IsPrime` using `hp.1.1`.

Establish `hpd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) ≤ d` using `(ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hp.1.2)).trans hJ`. Take `⟨s, hs, π, P, hP, hP'⟩` from `exists_simple_root_data p`. Use `set g := ∏ i, (Polynomial.derivative (P i)).eval₂ (MvPolynomial.aeval π).toRingHom (X i) with hgdef`. Establish `hg : g ∉ p`. Rewrite using `[hgdef, Ideal.IsPrime.prod_mem_iff]`.

Introduce and unpack `⟨i, -, hi⟩`. Conclude with `hP' i hi`. Establish `hsplit : {x : Fin n → ℂ | ∀ q ∈ p, MvPolynomial.eval x q = 0} ⊆ {x | x ∈ {x : Fin n → ℂ | ∀ q ∈ p, MvPolynomial.eval x q = 0} ∧ ∀ i, Polynomial.eval (x i) ((Polynomial.derivative (P i)).map (MvPolynomial.eval (paramMap π x))) ≠ 0} ∪ {x : Fin n → ℂ | ∀ q ∈ p ⊔ Ideal.span {g}, MvPo …`. Introduce `x hx`. Distinguish the cases in `h : ∀ i, Polynomial.eval (x i) ((Polynomial.derivative (P i)).map (MvPolynomial.eval (paramMap π x))) ≠ 0`.

Conclude with `Or.inl ⟨hx, h⟩`. Use `right push Not at h`. Take `⟨i, hi⟩` from `h`. Rewrite using `[Set.mem_ofPred_eq, mem_zeroSet_iff, sup_le_iff, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]`. Use `⟨(mem_zeroSet_iff p x).1 hx, ?_⟩` and prove the remaining obligations.

Rewrite using `[hgdef, map_prod]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (by rw [eval_eval₂_aeval]; exact hi)`. Use `(dimH_mono hsplit).trans ?_` and prove the remaining obligations. Rewrite using `[dimH_union]`. Use `max_le ?_ ?_` and prove the remaining obligations.

Establish `hV : ∀ x ∈ {x : Fin n → ℂ | ∀ q ∈ p, MvPolynomial.eval x q = 0}, ∀ i, Polynomial.eval (x i) ((P i).map (MvPolynomial.eval (paramMap π x))) = 0`. Introduce `x hx i`. Rewrite using `[← eval_eval₂_aeval]`. Conclude with `hx _ (hP i)`. Use `(dimH_simple_roots_le π P _ hV).trans ?_` and prove the remaining obligations.

Establish `hsd : s ≤ d` using `by exact_mod_cast hs.trans hpd`. Establish `: (s : ENNReal) ≤ d` using `by exact_mod_cast hsd`. Use `gcongr`. Conclude with `hIH _ ((ringKrullDim_quot_sup_add_one_le p g hg).trans hpd)`.
-/
theorem dimH_le_of_step {n : ℕ} (d : ℕ)
    (hIH : ∀ J' : Ideal (MvPolynomial (Fin n) ℂ), ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J') + 1 ≤ d →
      dimH {x : Fin n → ℂ | ∀ q ∈ J', MvPolynomial.eval x q = 0} ≤ 2 * (d : ENNReal))
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ d) :
    dimH {x : Fin n → ℂ | ∀ q ∈ J, MvPolynomial.eval x q = 0} ≤ 2 * (d : ENNReal) := by

  have hcover : {x : Fin n → ℂ | ∀ q ∈ J, MvPolynomial.eval x q = 0} ⊆
      ⋃ p ∈ J.minimalPrimes, {x : Fin n → ℂ | ∀ q ∈ p, MvPolynomial.eval x q = 0} := by
    intro x hx
    rw [Set.mem_ofPred_eq, mem_zeroSet_iff] at hx
    have : (RingHom.ker (MvPolynomial.eval x)).IsPrime := RingHom.ker_isPrime _
    obtain ⟨p, hp, hpx⟩ := Ideal.exists_minimalPrimes_le hx
    exact Set.mem_biUnion hp ((mem_zeroSet_iff p x).2 hpx)
  refine (dimH_mono hcover).trans ?_
  rw [dimH_bUnion (Ideal.finite_minimalPrimes_of_isNoetherianRing _ J).countable]
  refine iSup₂_le fun p hp => ?_
  have : p.IsPrime := hp.1.1
  have hpd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) ≤ d :=
    (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hp.1.2)).trans hJ
  obtain ⟨s, hs, π, P, hP, hP'⟩ := exists_simple_root_data p
  set g := ∏ i, (Polynomial.derivative (P i)).eval₂ (MvPolynomial.aeval π).toRingHom (X i) with hgdef
  have hg : g ∉ p := by
    rw [hgdef, Ideal.IsPrime.prod_mem_iff]
    rintro ⟨i, -, hi⟩
    exact hP' i hi
  have hsplit : {x : Fin n → ℂ | ∀ q ∈ p, MvPolynomial.eval x q = 0} ⊆
      {x | x ∈ {x : Fin n → ℂ | ∀ q ∈ p, MvPolynomial.eval x q = 0} ∧ ∀ i, Polynomial.eval (x i)
        ((Polynomial.derivative (P i)).map (MvPolynomial.eval (paramMap π x))) ≠ 0} ∪
      {x : Fin n → ℂ | ∀ q ∈ p ⊔ Ideal.span {g}, MvPolynomial.eval x q = 0} := by
    intro x hx
    by_cases h : ∀ i, Polynomial.eval (x i)
        ((Polynomial.derivative (P i)).map (MvPolynomial.eval (paramMap π x))) ≠ 0
    · exact Or.inl ⟨hx, h⟩
    · right
      push Not at h
      obtain ⟨i, hi⟩ := h
      rw [Set.mem_ofPred_eq, mem_zeroSet_iff, sup_le_iff, Ideal.span_singleton_le_iff_mem,
        RingHom.mem_ker]
      refine ⟨(mem_zeroSet_iff p x).1 hx, ?_⟩
      rw [hgdef, map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [eval_eval₂_aeval]; exact hi)
  refine (dimH_mono hsplit).trans ?_
  rw [dimH_union]
  refine max_le ?_ ?_
  · have hV : ∀ x ∈ {x : Fin n → ℂ | ∀ q ∈ p, MvPolynomial.eval x q = 0}, ∀ i,
        Polynomial.eval (x i) ((P i).map (MvPolynomial.eval (paramMap π x))) = 0 := by
      intro x hx i
      rw [← eval_eval₂_aeval]
      exact hx _ (hP i)
    refine (dimH_simple_roots_le π P _ hV).trans ?_
    have hsd : s ≤ d := by exact_mod_cast hs.trans hpd
    have : (s : ENNReal) ≤ d := by exact_mod_cast hsd
    gcongr
  · exact hIH _ ((ringKrullDim_quot_sup_add_one_le p g hg).trans hpd)

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `zero`. Introduce `n J hJ`. Use `dimH_le_of_step 0 (fun J' hJ' => ?_) J hJ` and prove the remaining obligations. Distinguish the cases in `htop : J' = ⊤`.

Establish `: {x : Fin n → ℂ | ∀ q ∈ J', MvPolynomial.eval x q = 0} = ∅`. Use extensionality with `x`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall]`. Conclude with `⟨1, htop ▸ Submodule.mem_top, by simp⟩`. Rewrite using `[this, dimH_empty]`.

Simplify using the standard rewrite rules. Establish `: Nontrivial (MvPolynomial (Fin n) ℂ ⧸ J')` using `Ideal.Quotient.nontrivial_iff.2 htop`. Establish `h0` using `ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ J')`. Establish `h1 : (0 : WithBot ℕ∞) + 1 ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J') + 1` using `by gcongr`. Establish `h2` using `h1.trans hJ'`.

Rewrite `h2` using `[zero_add, Nat.cast_zero]`. Conclude with `absurd h2 (not_le.2 zero_lt_one)`. Consider the case `succ k ih`. Introduce `n J hJ`. Use `dimH_le_of_step (k + 1) (fun J' hJ' => ?_) J hJ` and prove the remaining obligations.

Use `(ih n J' (le_of_add_one_le_succ hJ')).trans ?_` and prove the remaining obligations. Establish `: (k : ENNReal) ≤ ((k + 1 : ℕ) : ENNReal)` using `by exact_mod_cast Nat.le_succ k`. Use `gcongr`.
-/
theorem dimH_zeroLocus_le (d : ℕ) : ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)),
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ d →
      dimH {x : Fin n → ℂ | ∀ q ∈ J, MvPolynomial.eval x q = 0} ≤ 2 * (d : ENNReal) := by
  induction d with
  | zero =>
    intro n J hJ
    refine dimH_le_of_step 0 (fun J' hJ' => ?_) J hJ
    by_cases htop : J' = ⊤
    · have : {x : Fin n → ℂ | ∀ q ∈ J', MvPolynomial.eval x q = 0} = ∅ := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall]
        exact ⟨1, htop ▸ Submodule.mem_top, by simp⟩
      rw [this, dimH_empty]
      simp
    · have : Nontrivial (MvPolynomial (Fin n) ℂ ⧸ J') := Ideal.Quotient.nontrivial_iff.2 htop
      have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ J')
      have h1 : (0 : WithBot ℕ∞) + 1 ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J') + 1 := by gcongr
      have h2 := h1.trans hJ'
      rw [zero_add, Nat.cast_zero] at h2
      exact absurd h2 (not_le.2 zero_lt_one)
  | succ k ih =>
    intro n J hJ
    refine dimH_le_of_step (k + 1) (fun J' hJ' => ?_) J hJ
    refine (ih n J' (le_of_add_one_le_succ hJ')).trans ?_
    have : (k : ENNReal) ≤ ((k + 1 : ℕ) : ENNReal) := by exact_mod_cast Nat.le_succ k
    gcongr

/- English proof (translation)
Introduce `n d J hJ` and use `dimH_zeroLocus_le d n J hJ`.
-/
theorem proof : Statement := fun n d J hJ => dimH_zeroLocus_le d n J hJ

end ZeroLocusDimH

end

end GroundTheory.Heights₂.Heights
