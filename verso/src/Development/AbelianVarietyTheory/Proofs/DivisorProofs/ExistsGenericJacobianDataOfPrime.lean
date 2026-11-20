import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSqLocalizationOfPderivMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetNeZeroOfRowsSeparatingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMinimalLocalGeneratorsStatement
open IsLocalRing TensorProduct

namespace GlobalTheory

/- English proof (translation)
Take `⟨h, f, g, hgQ, hfQ, hgen, -, hmin⟩` from `GlobalTheory.T.exists_minimal_local_generators' (MvPolynomial σ Λ) Q`. Use `set φ : MvPolynomial σ Λ →+* FractionRing (MvPolynomial σ Λ ⧸ Q) := (algebraMap (MvPolynomial σ Λ ⧸ Q) (FractionRing (MvPolynomial σ Λ ⧸ Q))).comp (Ideal.Quotient.mk Q) with hφ`. Establish `hφker : ∀ x, φ x = 0 ↔ x ∈ Q`. Introduce `x`. Rewrite using `[hφ, RingHom.comp_apply, ← Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `map_eq_zero_iff _ (IsFractionRing.injective _ _)`. Establish `hind : ∀ a : Fin h → FractionRing (MvPolynomial σ Λ ⧸ Q), (∀ t, ∑ j, a j * φ (MvPolynomial.pderiv t (f j)) = 0) → a = 0`. Introduce `a ha`. Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (MvPolynomial σ Λ ⧸ Q)) a`. Use `choose c hc using fun j => RingHom.mem_rangeS.mp (hb j)`.

Use `choose a' ha' using fun j => Ideal.Quotient.mk_surjective (c j)`. Establish `hφa : ∀ j, φ (a' j) = algebraMap _ (FractionRing (MvPolynomial σ Λ ⧸ Q)) (b : MvPolynomial σ Λ ⧸ Q) * a j`. Introduce `j`. Rewrite using `[hφ, RingHom.comp_apply, ha', hc, Algebra.smul_def]`. Establish `hx : ∑ j, a' j * f j ∈ Q` using `Q.sum_mem fun j _ => Q.mul_mem_left _ (hfQ j)`.

Establish `hpd : ∀ t, MvPolynomial.pderiv t (∑ j, a' j * f j) ∈ Q`. Introduce `t`. Rewrite using `[map_sum]`. Simplify using `only [Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]`. Use `Q.add_mem ?_ (Q.sum_mem fun j _ => Q.mul_mem_right _ (hfQ j))` and prove the remaining obligations.

Rewrite using `[← hφker, map_sum]`. Simplify using `only [map_mul, hφa, mul_assoc, ← Finset.mul_sum, ha t, mul_zero]`. Take `⟨u, hu, hux⟩` from `GlobalTheory.T.exists_not_mem_mul_mem_sq_of_pderiv_mem Λ σ Q hQ _ hx hpd`. Establish `haQ` using `hmin a' u hu hux`. Use function extensionality and compare the values at `j`.

Establish `h1 : φ (a' j) = 0` using `(hφker _).mpr (haQ j)`. Rewrite `h1` using `[hφa j]`. Conclude with `(mul_eq_zero.mp h1).resolve_left (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2)`. Take `⟨s, hs⟩` from `GlobalTheory.T.exists_det_ne_zero_of_separating_functionals (FractionRing (MvPolynomial σ Λ ⧸ Q)) σ h (fun t j => φ (MvPolynomial.pderiv t (f j))) hind`. Use `⟨h, f, s, g, hgQ, hfQ, hgen, fun hdet => hs ?_⟩` and prove the remaining obligations.

Establish `hmat : (Matrix.of fun i j => φ (MvPolynomial.pderiv (s i) (f j))) = φ.mapMatrix (Matrix.of fun i j => MvPolynomial.pderiv (s i) (f j))`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[hmat, ← RingHom.map_det, hφker]`. Conclude with `hdet`.
-/
theorem exists_generic_jacobian_data_of_prime (Λ : Type) [CommRing Λ] [IsDomain Λ]
    [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (σ : Type) [Finite σ]
    (Q : Ideal (MvPolynomial σ Λ)) [Q.IsPrime] (hQ : ∀ a : Λ, MvPolynomial.C a ∈ Q → a = 0) :
    ∃ (h : ℕ) (f : Fin h → MvPolynomial σ Λ) (s : Fin h → σ) (g : MvPolynomial σ Λ),
      g ∉ Q ∧ (∀ j, f j ∈ Q) ∧ (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) ∧
      (Matrix.of fun i j => MvPolynomial.pderiv (s i) (f j)).det ∉ Q := by
  classical
  obtain ⟨h, f, g, hgQ, hfQ, hgen, -, hmin⟩ := GlobalTheory.T.exists_minimal_local_generators' (MvPolynomial σ Λ) Q

  set φ : MvPolynomial σ Λ →+* FractionRing (MvPolynomial σ Λ ⧸ Q) :=
    (algebraMap (MvPolynomial σ Λ ⧸ Q) (FractionRing (MvPolynomial σ Λ ⧸ Q))).comp
      (Ideal.Quotient.mk Q) with hφ
  have hφker : ∀ x, φ x = 0 ↔ x ∈ Q := by
    intro x
    rw [hφ, RingHom.comp_apply, ← Ideal.Quotient.eq_zero_iff_mem]
    exact map_eq_zero_iff _ (IsFractionRing.injective _ _)

  have hind : ∀ a : Fin h → FractionRing (MvPolynomial σ Λ ⧸ Q),
      (∀ t, ∑ j, a j * φ (MvPolynomial.pderiv t (f j)) = 0) → a = 0 := by
    intro a ha
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
      (nonZeroDivisors (MvPolynomial σ Λ ⧸ Q)) a
    choose c hc using fun j => RingHom.mem_rangeS.mp (hb j)
    choose a' ha' using fun j => Ideal.Quotient.mk_surjective (c j)
    have hφa : ∀ j, φ (a' j) =
        algebraMap _ (FractionRing (MvPolynomial σ Λ ⧸ Q)) (b : MvPolynomial σ Λ ⧸ Q) * a j := by
      intro j
      rw [hφ, RingHom.comp_apply, ha', hc, Algebra.smul_def]
    have hx : ∑ j, a' j * f j ∈ Q := Q.sum_mem fun j _ => Q.mul_mem_left _ (hfQ j)
    have hpd : ∀ t, MvPolynomial.pderiv t (∑ j, a' j * f j) ∈ Q := by
      intro t
      rw [map_sum]
      simp only [Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
      refine Q.add_mem ?_ (Q.sum_mem fun j _ => Q.mul_mem_right _ (hfQ j))
      rw [← hφker, map_sum]
      simp only [map_mul, hφa, mul_assoc, ← Finset.mul_sum, ha t, mul_zero]
    obtain ⟨u, hu, hux⟩ := GlobalTheory.T.exists_not_mem_mul_mem_sq_of_pderiv_mem Λ σ Q hQ _ hx hpd
    have haQ := hmin a' u hu hux
    funext j
    have h1 : φ (a' j) = 0 := (hφker _).mpr (haQ j)
    rw [hφa j] at h1
    exact (mul_eq_zero.mp h1).resolve_left
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2)
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_det_ne_zero_of_separating_functionals (FractionRing (MvPolynomial σ Λ ⧸ Q)) σ h
    (fun t j => φ (MvPolynomial.pderiv t (f j))) hind
  refine ⟨h, f, s, g, hgQ, hfQ, hgen, fun hdet => hs ?_⟩
  have hmat : (Matrix.of fun i j => φ (MvPolynomial.pderiv (s i) (f j))) =
      φ.mapMatrix (Matrix.of fun i j => MvPolynomial.pderiv (s i) (f j)) := by
    ext i j
    simp
  rw [hmat, ← RingHom.map_det, hφker]
  exact hdet

end GlobalTheory
