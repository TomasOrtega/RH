import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Introduce `A ι _ c s hs hc`. Assume the negation of the conclusion as `hc0`. Establish `hmem : ∀ a : A, a ∈ (Submodule.span A {c}).annihilator ↔ a * c = 0`. Introduce `a`. Rewrite using `[Submodule.mem_annihilator_span_singleton, smul_eq_mul]`.

Establish `hIt : (Submodule.span A {c}).annihilator ≠ ⊤`. Introduce `h`. Establish `h1 : (1:A) ∈ (Submodule.span A {c}).annihilator`. Rewrite using `[h]`. Conclude with `Submodule.mem_top`.

Rewrite `h1` using `[hmem, one_mul]`. Conclude with `hc0 h1`. Take `⟨M, hM, hIM⟩` from `Ideal.exists_le_maximal _ hIt`. Use `haveI := hM`. Use `letI := Ideal.Quotient.field M`.

Establish `hprod : MvPolynomial.map (Ideal.Quotient.mk M) s.prod = 0`. Use extensionality with `m`. Rewrite using `[MvPolynomial.coeff_map, MvPolynomial.coeff_zero, Ideal.Quotient.eq_zero_iff_mem]`. Apply `hIM` to reduce the goal to its premises. Rewrite using `[hmem, mul_comm, ← MvPolynomial.coeff_C_mul, hc, MvPolynomial.coeff_zero]`.

Rewrite `hprod` using `[map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map]`. Take `⟨p, hp, hp0⟩` from `hprod`. Take `⟨m, hm⟩` from `hs p hp`. Establish `h2` using `congrArg (MvPolynomial.coeff m) hp0`. Rewrite `h2` using `[MvPolynomial.coeff_map, hm, map_one, MvPolynomial.coeff_zero]`.

Conclude with `one_ne_zero h2`.
-/
theorem UpperTheory.Gal.crystallineComparison.gaussLin_of :
    GaussLin := by
  intro A ι _ c s hs hc
  by_contra hc0
  have hmem : ∀ a : A, a ∈ (Submodule.span A {c}).annihilator ↔ a * c = 0 := by
    intro a
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
  have hIt : (Submodule.span A {c}).annihilator ≠ ⊤ := by
    intro h
    have h1 : (1:A) ∈ (Submodule.span A {c}).annihilator := by
      rw [h]; exact Submodule.mem_top
    rw [hmem, one_mul] at h1
    exact hc0 h1
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal _ hIt
  haveI := hM
  letI := Ideal.Quotient.field M
  have hprod : MvPolynomial.map (Ideal.Quotient.mk M) s.prod = 0 := by
    ext m
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
    apply hIM
    rw [hmem, mul_comm, ← MvPolynomial.coeff_C_mul, hc, MvPolynomial.coeff_zero]
  rw [map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hprod
  obtain ⟨p, hp, hp0⟩ := hprod
  obtain ⟨m, hm⟩ := hs p hp
  have h2 := congrArg (MvPolynomial.coeff m) hp0
  rw [MvPolynomial.coeff_map, hm, map_one, MvPolynomial.coeff_zero] at h2
  exact one_ne_zero h2
