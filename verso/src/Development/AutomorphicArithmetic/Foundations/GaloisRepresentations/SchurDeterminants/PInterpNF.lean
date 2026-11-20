import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffClr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit

noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

/- English proof (translation)
Introduce `τ τ' h`. Conclude with `IsLocalization.ringHom_ext (nonZeroDivisors (NumberField.RingOfIntegers E)) h`.
-/
private lemma resO_injective {E K : Type} [Field E] [NumberField E] [Field K] :
    Function.Injective (resO : (E →+* K) → (NumberField.RingOfIntegers E →+* K)) := by
  intro τ τ' h
  exact IsLocalization.ringHom_ext (nonZeroDivisors (NumberField.RingOfIntegers E)) h

/- English proof (translation)
Introduce `h`. Apply `hN` to reduce the goal to its premises. Establish `h1 : τ (algebraMap (NumberField.RingOfIntegers E) E N) = 0` using `h`. Establish `h2 : algebraMap (NumberField.RingOfIntegers E) E N = 0`. Simplify using `using h1`.

Conclude with `NumberField.RingOfIntegers.coe_injective (by simpa using h2)`.
-/
private lemma resO_ne_zero {E K : Type} [Field E] [NumberField E] [Field K] (τ : E →+* K)
    {N : NumberField.RingOfIntegers E} (hN : N ≠ 0) : resO τ N ≠ 0 := by
  intro h
  apply hN
  have h1 : τ (algebraMap (NumberField.RingOfIntegers E) E N) = 0 := h
  have h2 : algebraMap (NumberField.RingOfIntegers E) E N = 0 := by
    simpa using h1
  exact NumberField.RingOfIntegers.coe_injective (by simpa using h2)

/- English proof (translation)
Introduce `h`. Use `congrArg (eval (fun _ : σ => (0 : K))) h` as an intermediate fact. Simplify using `at this`.
-/
private lemma one_sub_ne_zero {K σ : Type} [Field K] (p : σ) (b : K) :
    (1 - X p * C b : MvPolynomial σ K) ≠ 0 := by
  intro h
  have := congrArg (eval (fun _ : σ => (0 : K))) h
  simp at this

/- English proof (translation)
Introduce `hI E K _ _ _ _ n lam`. Distinguish the cases in `hE : IsEmpty (E →+* K)`. Use `⟨0, fun k _ N hN B => ?_⟩` and prove the remaining obligations. Use `⟨Finsupp.single (fun _ => N) 1, ?_, ?_⟩` and prove the remaining obligations. Introduce `α hα s`.

Establish `hα' : α = fun _ => N`. Simplify using `using Finsupp.support_single_subset hα`. Substitute `hα'` using the available equality. Conclude with `⟨hN, dvd_rfl, fun τ => hE.elim τ⟩`. Introduce `R _ _ _ g`.

Rewrite using `[Finsupp.sum_single_index (by simp)]`. Simplify using `[Finset.univ_eq_empty]`. Rewrite `hE` using `[not_isEmpty_iff]`. Take `⟨τ₀⟩` from `hE`. Take `⟨k₀, hk⟩` from `hI (NumberField.RingOfIntegers E) K (E →+* K) resO resO_injective n (fun τ => MvPolynomial.map (algebraMap ℚ K) (GroundTheory.Heights₂.Heights.RestTerms.schur (Fin n) (lam τ))) (fun τ => (GroundTheory.Heights₂.Heights.RestTerms.Schur.schur_isSymmetric _).map _)`.

Use `⟨k₀, fun k hkk N hN B => ?_⟩` and prove the remaining obligations. Set `Q : MvPolynomial ((E →+* K) × Fin k) K` to `∏ p, (X p * ∏ b ∈ B, (1 - X p * C b))`. Establish `hQ : Q ≠ 0`. Use `Finset.prod_ne_zero_iff.mpr fun p _ => mul_ne_zero (X_ne_zero p) ?_` and prove the remaining obligations. Conclude with `Finset.prod_ne_zero_iff.mpr fun b _ => one_sub_ne_zero p b`.

Take `⟨c, hc, hsum⟩` from `hk k hkk N (fun t => resO_ne_zero t hN) (fun _ => 0) Q hQ`. Use `⟨c, ?_, ?_⟩` and prove the remaining obligations. Introduce `α hα s`. Take `⟨hdvd, hev⟩` from `hc α hα`. Establish `hfac : ∀ p : (E →+* K) × Fin k, pt resO α p ≠ 0 ∧ ∀ b ∈ B, 1 - pt resO α p * b ≠ 0`.

Introduce `p`. Establish `h0 : eval (pt resO α) (X p * ∏ b ∈ B, (1 - X p * C b)) ≠ 0`. Introduce `h`. Apply `hev` to reduce the goal to its premises. Conclude with `(map_prod (eval (pt resO α)) _ _).trans (Finset.prod_eq_zero (Finset.mem_univ p) h)`.

Simplify using `only [map_mul, eval_X, map_prod, map_sub, map_one, eval_C] at h0`. Use `⟨left_ne_zero_of_mul h0, fun b hb => ?_⟩` and prove the remaining obligations. Conclude with `(Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul h0)) b hb`. Use `⟨?_, by simpa using hdvd s, fun τ b hb => (hfac (τ, s)).2 b hb⟩` and prove the remaining obligations. Introduce `h0`.

Apply `(hfac (τ₀, s)).1` to reduce the goal to its premises. Simplify using `[pt, h0]`. Introduce `R _ _ _ g`. Establish `hR` using `hsum R g`. Use `letI : IsScalarTower ℚ K R := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)`.

Rewrite using `[hR]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Conclude with `MvPolynomial.aeval_map_algebraMap _ _ _`.
-/
theorem interpNF_of : Interp → InterpNF := by
  intro hI E K _ _ _ _ n lam
  classical
  by_cases hE : IsEmpty (E →+* K)
  · refine ⟨0, fun k _ N hN B => ?_⟩
    refine ⟨Finsupp.single (fun _ => N) 1, ?_, ?_⟩
    · intro α hα s
      have hα' : α = fun _ => N := by
        simpa using Finsupp.support_single_subset hα
      subst hα'
      exact ⟨hN, dvd_rfl, fun τ => hE.elim τ⟩
    · intro R _ _ _ g
      rw [Finsupp.sum_single_index (by simp)]
      simp [Finset.univ_eq_empty]
  · rw [not_isEmpty_iff] at hE
    obtain ⟨τ₀⟩ := hE
    obtain ⟨k₀, hk⟩ := hI (NumberField.RingOfIntegers E) K (E →+* K) resO resO_injective n
      (fun τ => MvPolynomial.map (algebraMap ℚ K)
        (GroundTheory.Heights₂.Heights.RestTerms.schur (Fin n) (lam τ)))
      (fun τ => (GroundTheory.Heights₂.Heights.RestTerms.Schur.schur_isSymmetric _).map _)
    refine ⟨k₀, fun k hkk N hN B => ?_⟩
    let Q : MvPolynomial ((E →+* K) × Fin k) K :=
      ∏ p, (X p * ∏ b ∈ B, (1 - X p * C b))
    have hQ : Q ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun p _ => mul_ne_zero (X_ne_zero p) ?_
      exact Finset.prod_ne_zero_iff.mpr fun b _ => one_sub_ne_zero p b
    obtain ⟨c, hc, hsum⟩ := hk k hkk N (fun t => resO_ne_zero t hN) (fun _ => 0) Q hQ
    refine ⟨c, ?_, ?_⟩
    · intro α hα s
      obtain ⟨hdvd, hev⟩ := hc α hα
      have hfac : ∀ p : (E →+* K) × Fin k, pt resO α p ≠ 0 ∧
          ∀ b ∈ B, 1 - pt resO α p * b ≠ 0 := by
        intro p
        have h0 : eval (pt resO α) (X p * ∏ b ∈ B, (1 - X p * C b)) ≠ 0 := by
          intro h
          apply hev
          exact (map_prod (eval (pt resO α)) _ _).trans
            (Finset.prod_eq_zero (Finset.mem_univ p) h)
        simp only [map_mul, eval_X, map_prod, map_sub, map_one, eval_C] at h0
        refine ⟨left_ne_zero_of_mul h0, fun b hb => ?_⟩
        exact (Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul h0)) b hb
      refine ⟨?_, by simpa using hdvd s, fun τ b hb => (hfac (τ, s)).2 b hb⟩
      intro h0
      apply (hfac (τ₀, s)).1
      simp [pt, h0]
    · intro R _ _ _ g
      have hR := hsum R g
      letI : IsScalarTower ℚ K R := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
      rw [hR]
      refine Finset.prod_congr rfl fun τ _ => ?_
      exact MvPolynomial.aeval_map_algebraMap _ _ _

end UpperTheory.Gal.Schur
