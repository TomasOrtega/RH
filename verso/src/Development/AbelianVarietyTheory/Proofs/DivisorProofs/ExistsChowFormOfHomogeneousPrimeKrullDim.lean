import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero

set_option autoImplicit false

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal

namespace GlobalTheory.ChowHt

attribute [local instance] MvPolynomial.gradedAlgebra

/- English proof (translation)
Establish `hI : P.IsHomogeneous (homogeneousSubmodule (Fin N) K)`. Introduce `n g hg`. Establish `h1 : (DirectSum.decompose (homogeneousSubmodule (Fin N) K) g n : MvPolynomial (Fin N) K) = homogeneousComponent n g` using `MvPolynomial.decomposition.decompose'_apply g n`. Rewrite using `[h1]`. Conclude with `hh g hg n`.

Establish `hX : ∃ j, X j ∉ P`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Establish `h0` using `GlobalTheory.ringKrullDim_quotient_le_zero_of_forall_X_mem hc`. Rewrite `h0` using `[hdim]`.

Establish `h1 : ((D + 1 : ℕ) : WithBot ℕ∞) ≤ ((0 : ℕ) : WithBot ℕ∞)` using `by simpa using h0`. Establish `h2 : D + 1 ≤ 0` using `by exact_mod_cast h1`. Use linear arithmetic over natural numbers and integers. Establish `hdim' : ringKrullDim (MvPolynomial (Fin N) K ⧸ P) = (Fintype.card (Fin (D + 1)) : ℕ)`. Rewrite using `[Fintype.card_fin]`.

Conclude with `hdim`. Establish `hprime : (GlobalTheory.Chow.elimIdeal (Fin (D + 1)) P).IsPrime` using `GlobalTheory.Chow.isPrime_elimIdeal hX`. Establish `hne : GlobalTheory.Chow.elimIdeal (Fin (D + 1)) P ≠ ⊥` using `GlobalTheory.Chow.elimIdeal_ne_bot hI hX hdim'.le`. Take `⟨f, hf⟩` from `(GlobalTheory.Chow.isPrincipal_elimIdeal hdim').principal`. Establish `hf' : GlobalTheory.Chow.elimIdeal (Fin (D + 1)) P = Ideal.span {f}` using `hf`.

Establish `hf0 : f ≠ 0`. Introduce and unpack `rfl`. Conclude with `hne (by rw [hf', Ideal.span_singleton_eq_bot])`. Establish `hfmem : f ∈ GlobalTheory.Chow.elimIdeal (Fin (D + 1)) P` using `hf' ▸ Ideal.subset_span rfl`. Establish `hfp : Prime f` using `(Ideal.span_singleton_prime hf0).1 (hf' ▸ hprime)`.

Take `⟨a, ha⟩` from `GlobalTheory.Chow.exists_isWeightedHomogeneous_of_dvd (GlobalTheory.Chow.blockWeight : Fin (D + 1) × Fin N → Fin (D + 1) → ℕ) (f := f) (fun a => by`. Rewrite using `[← Ideal.mem_span_singleton, ← hf']`. Conclude with `GlobalTheory.Chow.weightedHomogeneousComponent_mem_elimIdeal hfmem a)`. Establish `ha' : GlobalTheory.Chow.IsBlockHomogeneous f a` using `ha`. Establish `hconst : ∀ i, a i = a 0`.

Introduce `i`. Establish `h1` using `GlobalTheory.Chow.map_rename_elimIdeal (Equiv.swap i 0) P`. Rewrite `h1` using `[hf', Ideal.map_span, Set.image_singleton]`. Take `⟨c, hc, hcf⟩` from `GlobalTheory.Chow.exists_eq_C_mul_of_span_eq h1`. Establish `h2 : GlobalTheory.Chow.IsBlockHomogeneous f (a ∘ (Equiv.swap i 0).symm)`.

Rewrite using `[hcf]`. Conclude with `IsWeightedHomogeneous.C_mul (ha'.rename (Equiv.swap i 0)) c`. Establish `h3` using `congrFun (GlobalTheory.Chow.IsBlockHomogeneous.unique hf0 ha' h2) i`. Simplify using `using h3`. Use `⟨a 0, f, ?_, hfp.irreducible, fun u => ?_⟩` and prove the remaining obligations.

Rewrite using `[isMultiHomogeneous_iff_block, ← (funext hconst : a = fun _ => a 0)]`. Conclude with `ha'`. Rewrite using `[← GlobalTheory.Chow.forall_aeval_eq_zero_iff hI u, hf']`. Use `⟨fun hu p hp => ?_, fun hu => hu f (Ideal.subset_span rfl)⟩` and prove the remaining obligations. Take `⟨q, rfl⟩` from `Ideal.mem_span_singleton'.1 hp`.

Rewrite using `[map_mul, hu, mul_zero]`.
-/
theorem exists_isChowFormInt_of_ringKrullDim_eq (K : Type) [Field K] (N D : ℕ)
    (P : Ideal (MvPolynomial (Fin N) K)) (hP : P.IsPrime)
    (hh : ∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P)
    (hdim : ringKrullDim (MvPolynomial (Fin N) K ⧸ P) = (D + 1 : ℕ)) :
    ∃ (δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) K), IsChowFormInt P D δ f := by
  classical
  have hI : P.IsHomogeneous (homogeneousSubmodule (Fin N) K) := by
    intro n g hg
    have h1 : (DirectSum.decompose (homogeneousSubmodule (Fin N) K) g n : MvPolynomial (Fin N) K) =
        homogeneousComponent n g := MvPolynomial.decomposition.decompose'_apply g n
    rw [h1]
    exact hh g hg n
  have hX : ∃ j, X j ∉ P := by
    by_contra hc
    push Not at hc
    have h0 := GlobalTheory.ringKrullDim_quotient_le_zero_of_forall_X_mem hc
    rw [hdim] at h0
    have h1 : ((D + 1 : ℕ) : WithBot ℕ∞) ≤ ((0 : ℕ) : WithBot ℕ∞) := by simpa using h0
    have h2 : D + 1 ≤ 0 := by exact_mod_cast h1
    omega
  have hdim' : ringKrullDim (MvPolynomial (Fin N) K ⧸ P) = (Fintype.card (Fin (D + 1)) : ℕ) := by
    rw [Fintype.card_fin]; exact hdim
  have hprime : (GlobalTheory.Chow.elimIdeal (Fin (D + 1)) P).IsPrime := GlobalTheory.Chow.isPrime_elimIdeal hX
  have hne : GlobalTheory.Chow.elimIdeal (Fin (D + 1)) P ≠ ⊥ := GlobalTheory.Chow.elimIdeal_ne_bot hI hX hdim'.le
  obtain ⟨f, hf⟩ := (GlobalTheory.Chow.isPrincipal_elimIdeal hdim').principal
  have hf' : GlobalTheory.Chow.elimIdeal (Fin (D + 1)) P = Ideal.span {f} := hf
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hne (by rw [hf', Ideal.span_singleton_eq_bot])
  have hfmem : f ∈ GlobalTheory.Chow.elimIdeal (Fin (D + 1)) P := hf' ▸ Ideal.subset_span rfl
  have hfp : Prime f := (Ideal.span_singleton_prime hf0).1 (hf' ▸ hprime)
  obtain ⟨a, ha⟩ := GlobalTheory.Chow.exists_isWeightedHomogeneous_of_dvd
    (GlobalTheory.Chow.blockWeight : Fin (D + 1) × Fin N → Fin (D + 1) → ℕ) (f := f) (fun a => by
      rw [← Ideal.mem_span_singleton, ← hf']
      exact GlobalTheory.Chow.weightedHomogeneousComponent_mem_elimIdeal hfmem a)
  have ha' : GlobalTheory.Chow.IsBlockHomogeneous f a := ha
  have hconst : ∀ i, a i = a 0 := by
    intro i
    have h1 := GlobalTheory.Chow.map_rename_elimIdeal (Equiv.swap i 0) P
    rw [hf', Ideal.map_span, Set.image_singleton] at h1
    obtain ⟨c, hc, hcf⟩ := GlobalTheory.Chow.exists_eq_C_mul_of_span_eq h1
    have h2 : GlobalTheory.Chow.IsBlockHomogeneous f (a ∘ (Equiv.swap i 0).symm) := by
      rw [hcf]
      exact IsWeightedHomogeneous.C_mul (ha'.rename (Equiv.swap i 0)) c
    have h3 := congrFun (GlobalTheory.Chow.IsBlockHomogeneous.unique hf0 ha' h2) i
    simpa using h3
  refine ⟨a 0, f, ?_, hfp.irreducible, fun u => ?_⟩
  · rw [isMultiHomogeneous_iff_block, ← (funext hconst : a = fun _ => a 0)]
    exact ha'
  · rw [← GlobalTheory.Chow.forall_aeval_eq_zero_iff hI u, hf']
    refine ⟨fun hu p hp => ?_, fun hu => hu f (Ideal.subset_span rfl)⟩
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 hp
    rw [map_mul, hu, mul_zero]

end GlobalTheory.ChowHt
