import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingQuotientOfDetDerivationUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericJacobianDataOfPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationQuotientComapEquiv
open IsLocalRing TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `Λ _ _ _ _ B _ _ _ p _ hp`. Take `⟨n, φ, hφ⟩` from `Algebra.FiniteType.iff_quotient_mvPolynomial''.mp (inferInstance : Algebra.FiniteType Λ B)`. Use `set Q : Ideal (MvPolynomial (Fin n) Λ) := p.comap φ with hQdef`. Use `haveI : Q.IsPrime := Ideal.comap_isPrime _ _`. Establish `hQ : ∀ a : Λ, MvPolynomial.C a ∈ Q → a = 0`.

Introduce `a ha`. Apply `hp a` to reduce the goal to its premises. Establish `: φ (MvPolynomial.C a) ∈ p` using `ha`. Rewrite `this` using `[MvPolynomial.algHom_C]`. Then use the resulting hypothesis. Take `⟨h, f, s, g₀, hg₀, hfQ, hgQ, hdet⟩` from `GlobalTheory.T.exists_local_generators_jacobian_det_not_mem Λ (Fin n) Q hQ`.

Use `set δ := (Matrix.of fun i j => MvPolynomial.pderiv (s i) (f j)).det with hδ`. Use `⟨φ (g₀ * δ), ?_, ?_⟩` and prove the remaining obligations. Introduce `hmem`. Establish `: g₀ * δ ∈ Q` using `hmem`. Break down `Ideal.IsPrime.mem_or_mem inferInstance this with h1 | h1` into its components or cases.

Conclude with `hg₀ h1`. Conclude with `hdet h1`. Introduce `q _ hpq hgq set N : Ideal (MvPolynomial (Fin n) Λ) := q.comap φ with hN haveI : N.IsPrime := Ideal.comap_isPrime _ _`. Establish `hQN : Q ≤ N` using `Ideal.comap_mono hpq`. Establish `hgN : g₀ * δ ∉ N` using `hgq`.

Establish `hg₀N : g₀ ∉ N` using `fun h1 => hgN (N.mul_mem_right _ h1)`. Establish `hδN : δ ∉ N` using `fun h1 => hgN (N.mul_mem_left _ h1)`. Set `D : Fin h → Derivation ℤ (MvPolynomial (Fin n) Λ) (MvPolynomial (Fin n) Λ)` to `fun i => (MvPolynomial.pderiv (s i)).restrictScalars ℤ`. Establish `hdetD : (Matrix.of fun i j => D i (f j)).det ∉ N`. Simplify `hδN` using `[D]`.

Establish `hreg` using `GlobalTheory.T.isRegularLocalRing_quotient_of_det_derivation_unit (MvPolynomial (Fin n) Λ) h f D N (fun j => hQN (hfQ j)) hdetD`. Establish `heq : (Ideal.span (Set.range f)).map (algebraMap (MvPolynomial (Fin n) Λ) (Localization.AtPrime N)) = Q.map (algebraMap (MvPolynomial (Fin n) Λ) (Localization.AtPrime N))`. Apply `le_antisymm` to reduce the goal to its premises. Apply `Ideal.map_mono` to reduce the goal to its premises. Rewrite using `[Ideal.span_le]`.

Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `hfQ j`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `x hx`. Rewrite using `[Ideal.mem_comap]`.

Establish `hu : IsUnit (algebraMap (MvPolynomial (Fin n) Λ) (Localization.AtPrime N) g₀)` using `IsLocalization.map_units (Localization.AtPrime N) (⟨g₀, hg₀N⟩ : N.primeCompl)`. Rewrite using `[← Ideal.unit_mul_mem_iff_mem _ hu, ← map_mul]`. Conclude with `Ideal.mem_map_of_mem _ (hgQ x hx)`. Rewrite `hreg` using `[heq]`. Take `⟨e⟩` from `GlobalTheory.localization_quotient_comap_equiv (MvPolynomial (Fin n) Λ) B φ.toRingHom hφ p q`.

Use `haveI : IsRegularLocalRing (Localization.AtPrime (q.comap φ.toRingHom) ⧸ (p.comap φ.toRingHom).map (algebraMap _ (Localization.AtPrime (q.comap φ.toRingHom)))) := hreg`. Conclude with `IsRegularLocalRing.of_ringEquiv e`.
-/
theorem prime_generically_regular_quotient :
    ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)]
      (B : Type) [CommRing B] [Algebra Λ B] [Algebra.FiniteType Λ B] (p : Ideal B) [p.IsPrime],
      (∀ a : Λ, algebraMap Λ B a ∈ p → a = 0) → ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q →
        g ∉ q → IsRegularLocalRing (Localization.AtPrime q ⧸
          p.map (algebraMap B (Localization.AtPrime q))) := by
  intro Λ _ _ _ _ B _ _ _ p _ hp
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp (inferInstance : Algebra.FiniteType Λ B)
  set Q : Ideal (MvPolynomial (Fin n) Λ) := p.comap φ with hQdef
  haveI : Q.IsPrime := Ideal.comap_isPrime _ _
  have hQ : ∀ a : Λ, MvPolynomial.C a ∈ Q → a = 0 := by
    intro a ha
    apply hp a
    have : φ (MvPolynomial.C a) ∈ p := ha
    rwa [MvPolynomial.algHom_C] at this
  obtain ⟨h, f, s, g₀, hg₀, hfQ, hgQ, hdet⟩ := GlobalTheory.T.exists_local_generators_jacobian_det_not_mem Λ (Fin n) Q hQ
  set δ := (Matrix.of fun i j => MvPolynomial.pderiv (s i) (f j)).det with hδ
  refine ⟨φ (g₀ * δ), ?_, ?_⟩
  · intro hmem
    have : g₀ * δ ∈ Q := hmem
    rcases Ideal.IsPrime.mem_or_mem inferInstance this with h1 | h1
    · exact hg₀ h1
    · exact hdet h1
  · intro q _ hpq hgq
    set N : Ideal (MvPolynomial (Fin n) Λ) := q.comap φ with hN
    haveI : N.IsPrime := Ideal.comap_isPrime _ _
    have hQN : Q ≤ N := Ideal.comap_mono hpq
    have hgN : g₀ * δ ∉ N := hgq
    have hg₀N : g₀ ∉ N := fun h1 => hgN (N.mul_mem_right _ h1)
    have hδN : δ ∉ N := fun h1 => hgN (N.mul_mem_left _ h1)
    let D : Fin h → Derivation ℤ (MvPolynomial (Fin n) Λ) (MvPolynomial (Fin n) Λ) :=
      fun i => (MvPolynomial.pderiv (s i)).restrictScalars ℤ
    have hdetD : (Matrix.of fun i j => D i (f j)).det ∉ N := by
      simpa [D] using hδN
    have hreg := GlobalTheory.T.isRegularLocalRing_quotient_of_det_derivation_unit (MvPolynomial (Fin n) Λ) h f D N (fun j => hQN (hfQ j)) hdetD
    have heq : (Ideal.span (Set.range f)).map
          (algebraMap (MvPolynomial (Fin n) Λ) (Localization.AtPrime N)) =
        Q.map (algebraMap (MvPolynomial (Fin n) Λ) (Localization.AtPrime N)) := by
      apply le_antisymm
      · apply Ideal.map_mono
        rw [Ideal.span_le]
        rintro _ ⟨j, rfl⟩
        exact hfQ j
      · rw [Ideal.map_le_iff_le_comap]
        intro x hx
        rw [Ideal.mem_comap]
        have hu : IsUnit (algebraMap (MvPolynomial (Fin n) Λ) (Localization.AtPrime N) g₀) :=
          IsLocalization.map_units (Localization.AtPrime N) (⟨g₀, hg₀N⟩ : N.primeCompl)
        rw [← Ideal.unit_mul_mem_iff_mem _ hu, ← map_mul]
        exact Ideal.mem_map_of_mem _ (hgQ x hx)
    rw [heq] at hreg
    obtain ⟨e⟩ := GlobalTheory.localization_quotient_comap_equiv (MvPolynomial (Fin n) Λ) B
      φ.toRingHom hφ p q
    haveI : IsRegularLocalRing (Localization.AtPrime (q.comap φ.toRingHom) ⧸
        (p.comap φ.toRingHom).map (algebraMap _ (Localization.AtPrime (q.comap φ.toRingHom)))) := hreg
    exact IsRegularLocalRing.of_ringEquiv e

end GlobalTheory
