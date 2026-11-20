import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
open GlobalTheory.EtC

namespace GlobalTheory

/- English proof (translation)
Introduce `k K _ _ _ φ D m₀ hφD hm₀ hres hfrac`. Set `A` to `integralClosure D K`. Establish `hφA : ∀ c : k, φ c ∈ A` using `fun c => isIntegral_algebraMap (R := D) (x := (⟨φ c, hφD ⟨c, rfl⟩⟩ : D))`. Establish `hker : RingHom.ker (algebraMap D A) ≤ m₀`. Introduce `d hd`.

Establish `h0 : (algebraMap D A d : K) = 0` using `by rw [RingHom.mem_ker.mp hd]; rfl`. Establish `: d = 0` using `Subtype.ext h0`. Simplify using `[this]`. Take `⟨𝔪, h𝔪max, h𝔪comap⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := A) m₀ hker`. Set `φA : k →+* A` to `φ.codRestrict A hφA`.

Set `ψ : k →+* A ⧸ 𝔪` to `(Ideal.Quotient.mk 𝔪).comp φA`. Establish `hcoef : ∀ d : D, algebraMap D (A ⧸ 𝔪) d ∈ Set.range ψ`. Introduce `d`. Take `⟨c, hc, hdc⟩` from `hres d`. Use `⟨c, ?_⟩` and prove the remaining obligations.

Establish `hmem : algebraMap D A (d - ⟨φ c, hc⟩) ∈ 𝔪`. Rewrite using `[← Ideal.mem_comap, h𝔪comap]`. Conclude with `hdc`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk 𝔪 (φA c) = Ideal.Quotient.mk 𝔪 (algebraMap D A d)`. Use `symm`.

Rewrite `hmem` using `[map_sub]`. Conclude with `Ideal.Quotient.eq.mpr hmem`. Establish `hres' : ∀ r : A, ∃ c : k, r - φA c ∈ 𝔪`. Introduce `r`. Use `letI : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪`.

Use `letI : Algebra k (A ⧸ 𝔪) := ψ.toAlgebra`. Establish `hr : IsIntegral D (Ideal.Quotient.mkₐ D 𝔪 r)` using `(Algebra.IsIntegral.isIntegral (R := D) r).map (Ideal.Quotient.mkₐ D 𝔪)`. Take `⟨f, hfm, hf⟩` from `hr`. Establish `hlift : f.map (algebraMap D (A ⧸ 𝔪)) ∈ Polynomial.lifts ψ`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`.

Introduce `n`. Rewrite using `[Polynomial.coeff_map]`. Conclude with `hcoef _`. Take `⟨q, hq, -, hqm⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic hlift (hfm.map _)`. Establish `hint : IsIntegral k (Ideal.Quotient.mk 𝔪 r)`.

Use `⟨q, hqm, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_eq_eval_map]`. Express the relevant statement in the definitionally equal form `Polynomial.eval _ (q.map ψ) = 0`. Rewrite using `[hq, ← Polynomial.eval₂_eq_eval_map]`. Conclude with `hf`.

Establish `h1` using `IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hint)`. Take `⟨c, hc⟩` from `minpoly.mem_range_of_degree_eq_one k _ h1`. Conclude with `⟨c, Ideal.Quotient.eq.mp hc.symm⟩`. Use `⟨A.toSubring, 𝔪, ?_, h𝔪max, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨c, rfl⟩`.

Conclude with `hφA c`. Introduce `r`. Take `⟨c, hc⟩` from `hres' r`. Conclude with `⟨c, hφA c, hc⟩`. Introduce `x`.

Take `⟨d, hd, hint⟩` from `hfrac x`. Use `⟨⟨(d : K), Subalgebra.algebraMap_mem A d⟩, ?_, hint⟩` and prove the remaining obligations. Introduce `h`. Apply `hd` to reduce the goal to its premises. Conclude with `Subtype.ext (by simpa using congrArg Subtype.val h)`.

Introduce `x hx`. Establish `hx' : IsIntegral A x` using `hx`. Conclude with `isIntegral_trans x hx'`.
-/
theorem integralClosure_maximal_residue_algClosed : ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] (φ : k →+* K) (D : Subring K) (m₀ : Ideal D),
    φ.range ≤ D → m₀.IsMaximal → (∀ r : D, ∃ c : k, ∃ h : φ c ∈ D, r - ⟨φ c, h⟩ ∈ m₀) →
    (∀ x : K, ∃ d : D, d ≠ 0 ∧ IsIntegral D ((d : K) * x)) →
    ∃ (R : Subring K) (𝔪 : Ideal R), φ.range ≤ R ∧ 𝔪.IsMaximal ∧ (∀ r : R, ∃ c : k, ∃ h : φ c ∈ R, r - ⟨φ c, h⟩ ∈ 𝔪) ∧
      (∀ x : K, ∃ d : R, d ≠ 0 ∧ (d : K) * x ∈ R) ∧ ∀ x : K, IsIntegral R x → x ∈ R := by
  intro k K _ _ _ φ D m₀ hφD hm₀ hres hfrac
  let A := integralClosure D K
  have hφA : ∀ c : k, φ c ∈ A := fun c =>
    isIntegral_algebraMap (R := D) (x := (⟨φ c, hφD ⟨c, rfl⟩⟩ : D))
  have hker : RingHom.ker (algebraMap D A) ≤ m₀ := by
    intro d hd
    have h0 : (algebraMap D A d : K) = 0 := by rw [RingHom.mem_ker.mp hd]; rfl
    have : d = 0 := Subtype.ext h0
    simp [this]
  obtain ⟨𝔪, h𝔪max, h𝔪comap⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := A) m₀ hker
  let φA : k →+* A := φ.codRestrict A hφA
  let ψ : k →+* A ⧸ 𝔪 := (Ideal.Quotient.mk 𝔪).comp φA
  have hcoef : ∀ d : D, algebraMap D (A ⧸ 𝔪) d ∈ Set.range ψ := by
    intro d
    obtain ⟨c, hc, hdc⟩ := hres d
    refine ⟨c, ?_⟩
    have hmem : algebraMap D A (d - ⟨φ c, hc⟩) ∈ 𝔪 := by
      rw [← Ideal.mem_comap, h𝔪comap]; exact hdc
    change Ideal.Quotient.mk 𝔪 (φA c) = Ideal.Quotient.mk 𝔪 (algebraMap D A d)
    symm
    rw [map_sub] at hmem
    exact Ideal.Quotient.eq.mpr hmem
  have hres' : ∀ r : A, ∃ c : k, r - φA c ∈ 𝔪 := by
    intro r
    letI : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    letI : Algebra k (A ⧸ 𝔪) := ψ.toAlgebra
    have hr : IsIntegral D (Ideal.Quotient.mkₐ D 𝔪 r) :=
      (Algebra.IsIntegral.isIntegral (R := D) r).map (Ideal.Quotient.mkₐ D 𝔪)
    obtain ⟨f, hfm, hf⟩ := hr
    have hlift : f.map (algebraMap D (A ⧸ 𝔪)) ∈ Polynomial.lifts ψ := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n; rw [Polynomial.coeff_map]; exact hcoef _
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift (hfm.map _)
    have hint : IsIntegral k (Ideal.Quotient.mk 𝔪 r) := by
      refine ⟨q, hqm, ?_⟩
      rw [Polynomial.eval₂_eq_eval_map]
      change Polynomial.eval _ (q.map ψ) = 0
      rw [hq, ← Polynomial.eval₂_eq_eval_map]
      exact hf
    have h1 := IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hint)
    obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one k _ h1
    exact ⟨c, Ideal.Quotient.eq.mp hc.symm⟩
  refine ⟨A.toSubring, 𝔪, ?_, h𝔪max, ?_, ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩; exact hφA c
  · intro r
    obtain ⟨c, hc⟩ := hres' r
    exact ⟨c, hφA c, hc⟩
  · intro x
    obtain ⟨d, hd, hint⟩ := hfrac x
    refine ⟨⟨(d : K), Subalgebra.algebraMap_mem A d⟩, ?_, hint⟩
    intro h
    apply hd
    exact Subtype.ext (by simpa using congrArg Subtype.val h)
  · intro x hx
    have hx' : IsIntegral A x := hx
    exact isIntegral_trans x hx'

end GlobalTheory
