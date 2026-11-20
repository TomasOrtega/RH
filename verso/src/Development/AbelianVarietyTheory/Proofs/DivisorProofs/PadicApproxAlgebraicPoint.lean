import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgClosedDenseInCpStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicAlgebraicApproximationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialSystemSpecializationStatement
open Polynomial

namespace GlobalTheory.AlgPointsDense

/- English proof (translation)
Introduce `K _ _ R _ _ _ p _ ε s η hη`. Use `letI : Algebra K ℂ_[p] := (ε.comp (algebraMap K R)).toAlgebra`. Set `ε' : R →ₐ[K] ℂ_[p]` to `{ ε with commutes' := fun c => rfl }`. Set `ι₀ : AlgebraicClosure K →ₐ[K] ℂ_[p]` to `IsAlgClosed.lift`. Establish `hc : (ι₀ : AlgebraicClosure K →+* ℂ_[p]).comp (algebraMap K _) = algebraMap K ℂ_[p]`.

Use extensionality with `c`. Conclude with `ι₀.commutes c`. Establish `hdense` using `GlobalTheory.T.algClosed_dense_in_Cp p (AlgebraicClosure K) (ι₀ : AlgebraicClosure K →+* ℂ_[p])`. Take `⟨s0, hs0⟩` from `Algebra.FiniteType.out (R := K) (A := R)`. Set `S : Finset R` to `s0 ∪ s`.

Set `e : Fin S.card ≃ S` to `S.equivFin.symm`. Set `a : Fin S.card → ℂ_[p]` to `fun j => ε (e j)`. Take `⟨d, t, θ, P, Δ, Q, hPm, hPθ, hΔ, hQ, huniv⟩` from `GlobalTheory.T.polynomial_system_specialization K ℂ_[p] S.card a`. Take `⟨t', θ', hΔ', hP', hclose⟩` from `GlobalTheory.T.p_adic_algebraic_approximation p K (AlgebraicClosure K) (ι₀ : AlgebraicClosure K →+* ℂ_[p]) hdense hc d S.card t θ P Δ Q η hη hPm hPθ hΔ`. Take `⟨f, hf⟩` from `huniv (AlgebraicClosure K) t' θ' hΔ' hP'`.

Establish `hmem : ∀ r : R, ε' r ∈ Algebra.adjoin K (Set.range a)`. Introduce `r`. Establish `hr : r ∈ Algebra.adjoin K (s0 : Set R)` using `by rw [hs0]; trivial`. Establish `h1 : ε' r ∈ (Algebra.adjoin K (s0 : Set R)).map ε'` using `Subalgebra.mem_map.2 ⟨r, hr, rfl⟩`. Rewrite `h1` using `[← Algebra.adjoin_image]`.

Use `Algebra.adjoin_mono ?_ h1` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `⟨e.symm ⟨x, Finset.mem_union_left _ hx⟩, by simp [a, ε']⟩`. Set `g : R →ₐ[K] Algebra.adjoin K (Set.range a)` to `ε'.codRestrict _ hmem`. Use `⟨(ι₀ : AlgebraicClosure K →+* ℂ_[p]), f.comp g, ?_⟩` and prove the remaining obligations.

Introduce `h hh`. Set `j` to `e.symm ⟨h, Finset.mem_union_right _ hh⟩`. Establish `haj : a j = ε h` using `by simp [a, j]`. Establish `hg : g h = ⟨a j, Algebra.subset_adjoin (Set.mem_range_self j)⟩` using `Subtype.ext (show ε h = a j from haj.symm)`. Establish `h1 : f (g h) = Polynomial.eval₂ (MvPolynomial.aeval t').toRingHom θ' (Q j) / MvPolynomial.aeval t' Δ`.

Rewrite using `[hg, hf j]`. Clear the denominators using the available nonvanishing facts. Establish `h2 : ε h = Polynomial.eval₂ (MvPolynomial.aeval t).toRingHom θ (Q j) / MvPolynomial.aeval t Δ`. Rewrite using `[← haj, hQ j]`. Clear the denominators using the available nonvanishing facts.

Use `hclose j` as an intermediate fact. Rewrite using `[AlgHom.comp_apply, h1, map_div₀, h2]`. Conclude with `this`.
-/
theorem exists_algebraic_approx : ∀ (K : Type) [Field K] [NumberField K] (R : Type) [CommRing R] [Algebra K R] [Algebra.FiniteType K R] (p : ℕ) [Fact p.Prime] (ε : R →+* ℂ_[p]) (s : Finset R) (η : ℝ), 0 < η → ∃ (ι : AlgebraicClosure K →+* ℂ_[p]) (φ : R →ₐ[K] AlgebraicClosure K), ∀ h ∈ s, ‖ι (φ h) - ε h‖ < η := by
  intro K _ _ R _ _ _ p _ ε s η hη
  letI : Algebra K ℂ_[p] := (ε.comp (algebraMap K R)).toAlgebra
  let ε' : R →ₐ[K] ℂ_[p] := { ε with commutes' := fun c => rfl }
  let ι₀ : AlgebraicClosure K →ₐ[K] ℂ_[p] := IsAlgClosed.lift
  have hc : (ι₀ : AlgebraicClosure K →+* ℂ_[p]).comp (algebraMap K _) = algebraMap K ℂ_[p] := by
    ext c; exact ι₀.commutes c
  have hdense := GlobalTheory.T.algClosed_dense_in_Cp p (AlgebraicClosure K) (ι₀ : AlgebraicClosure K →+* ℂ_[p])
  classical
  obtain ⟨s0, hs0⟩ := Algebra.FiniteType.out (R := K) (A := R)
  let S : Finset R := s0 ∪ s
  let e : Fin S.card ≃ S := S.equivFin.symm
  let a : Fin S.card → ℂ_[p] := fun j => ε (e j)
  obtain ⟨d, t, θ, P, Δ, Q, hPm, hPθ, hΔ, hQ, huniv⟩ := GlobalTheory.T.polynomial_system_specialization K ℂ_[p] S.card a
  obtain ⟨t', θ', hΔ', hP', hclose⟩ := GlobalTheory.T.p_adic_algebraic_approximation p K (AlgebraicClosure K)
    (ι₀ : AlgebraicClosure K →+* ℂ_[p]) hdense hc d S.card t θ P Δ Q η hη hPm hPθ hΔ
  obtain ⟨f, hf⟩ := huniv (AlgebraicClosure K) t' θ' hΔ' hP'
  have hmem : ∀ r : R, ε' r ∈ Algebra.adjoin K (Set.range a) := by
    intro r
    have hr : r ∈ Algebra.adjoin K (s0 : Set R) := by rw [hs0]; trivial
    have h1 : ε' r ∈ (Algebra.adjoin K (s0 : Set R)).map ε' := Subalgebra.mem_map.2 ⟨r, hr, rfl⟩
    rw [← Algebra.adjoin_image] at h1
    refine Algebra.adjoin_mono ?_ h1
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨e.symm ⟨x, Finset.mem_union_left _ hx⟩, by simp [a, ε']⟩
  let g : R →ₐ[K] Algebra.adjoin K (Set.range a) := ε'.codRestrict _ hmem
  refine ⟨(ι₀ : AlgebraicClosure K →+* ℂ_[p]), f.comp g, ?_⟩
  intro h hh
  let j := e.symm ⟨h, Finset.mem_union_right _ hh⟩
  have haj : a j = ε h := by simp [a, j]
  have hg : g h = ⟨a j, Algebra.subset_adjoin (Set.mem_range_self j)⟩ :=
    Subtype.ext (show ε h = a j from haj.symm)
  have h1 : f (g h) = Polynomial.eval₂ (MvPolynomial.aeval t').toRingHom θ' (Q j) /
      MvPolynomial.aeval t' Δ := by
    rw [hg, hf j]; field_simp
  have h2 : ε h = Polynomial.eval₂ (MvPolynomial.aeval t).toRingHom θ (Q j) /
      MvPolynomial.aeval t Δ := by
    rw [← haj, hQ j]; field_simp
  have := hclose j
  rw [AlgHom.comp_apply, h1, map_div₀, h2]
  exact this

end GlobalTheory.AlgPointsDense
