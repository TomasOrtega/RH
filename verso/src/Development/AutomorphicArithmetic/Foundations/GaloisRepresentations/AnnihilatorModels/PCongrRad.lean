import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Introduce `R _ 𝔞 h𝔞 ι N N' H B' _ g hg`. Establish `key : ∀ (a : ℕ) (m : ι →₀ ℕ), MvPolynomial.coeff m (N.coeff a) - MvPolynomial.coeff m (N'.coeff a) ∈ 𝔞`. Introduce `a m`. Rewrite using `[← h𝔞.radical, ← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]`. Introduce `𝔭 h𝔭`.

Take `⟨κ, _, f, hker, hf⟩` from `H 𝔭 h𝔭`. Rewrite using `[← hker, RingHom.mem_ker, map_sub, sub_eq_zero]`. Use `congrArg (fun p => MvPolynomial.coeff m (p.coeff a)) hf` as an intermediate fact. Simplify `this` using `[mapP, Polynomial.coeff_map, MvPolynomial.coeff_map]`. Use `Polynomial.ext fun a => MvPolynomial.ext _ _ fun m => ?_` and prove the remaining obligations.

Simplify using `only [mapP, Polynomial.coeff_map, MvPolynomial.coeff_map]`. Rewrite using `[← sub_eq_zero, ← map_sub]`. Conclude with `hg _ (key a m)`.
-/
theorem UpperTheory.Gal.crystallineComparison.congrRad_of :
    CongrRad := by
  intro R _ 𝔞 h𝔞 ι N N' H B' _ g hg
  have key : ∀ (a : ℕ) (m : ι →₀ ℕ),
      MvPolynomial.coeff m (N.coeff a) - MvPolynomial.coeff m (N'.coeff a) ∈ 𝔞 := by
    intro a m
    rw [← h𝔞.radical, ← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
    intro 𝔭 h𝔭
    obtain ⟨κ, _, f, hker, hf⟩ := H 𝔭 h𝔭
    rw [← hker, RingHom.mem_ker, map_sub, sub_eq_zero]
    have := congrArg (fun p => MvPolynomial.coeff m (p.coeff a)) hf
    simpa [mapP, Polynomial.coeff_map, MvPolynomial.coeff_map] using this
  refine Polynomial.ext fun a => MvPolynomial.ext _ _ fun m => ?_
  simp only [mapP, Polynomial.coeff_map, MvPolynomial.coeff_map]
  rw [← sub_eq_zero, ← map_sub]
  exact hg _ (key a m)
