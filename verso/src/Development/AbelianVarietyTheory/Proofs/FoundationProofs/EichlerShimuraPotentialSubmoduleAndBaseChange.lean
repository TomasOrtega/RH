import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftApplyOfMemAdmissibleSubalgebra
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoVarPolySubstMatrixBasicLaws
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ

/- English proof (translation)
Introduce `R _ w Γ`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `F G ⟨hF, hF'⟩ ⟨hG, hG'⟩`. Use `⟨fun z => (hF z).add (hG z), fun γ hγ => ?_⟩` and prove the remaining obligations. Take `⟨p, hp⟩` from `hF' γ hγ`.

Take `⟨q, hq⟩` from `hG' γ hγ`. Use `⟨p + q, fun z hz => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.add_apply, map_add]`. Rewrite using `[← hp z hz, ← hq z hz]`. Normalize the expressions using the abelian group laws.

Use `⟨fun z => MvPolynomial.isHomogeneous_zero _ _ _, fun γ _ => ⟨0, fun z _ => ?_⟩⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce and unpack `c F ⟨hF, hF'⟩`. Use `⟨fun z => ?_, fun γ hγ => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, MvPolynomial.smul_eq_C_mul]`.

Simplify using `using (MvPolynomial.isHomogeneous_C (Fin 2) c).mul (hF z)`. Take `⟨p, hp⟩` from `hF' γ hγ`. Use `⟨c • p, fun z hz => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, map_smul]`. Rewrite using `[← hp z hz, smul_sub]`.

Introduce and unpack `F G ⟨ψ, p, hψ, hp⟩ ⟨ψ', p', hψ', hp'⟩`. Use `⟨ψ + ψ', p + p', fun γ hγ z hz => ?_, fun z hz => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.add_apply, map_add, hψ γ hγ z hz, hψ' γ hγ z hz]`. Simplify using `only [Pi.add_apply, hp z hz, hp' z hz]`. Normalize the expressions using the abelian group laws.

Introduce and unpack `c F ⟨ψ, p, hψ, hp⟩`. Use `⟨c • ψ, c • p, fun γ hγ z hz => ?_, fun z hz => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, map_smul, hψ γ hγ z hz]`. Simplify using `only [Pi.smul_apply, hp z hz, smul_add]`. Introduce and unpack `S _ f F ⟨hF, hF'⟩`.

Use `⟨fun z => (hF z).map f, fun γ hγ => ?_⟩` and prove the remaining obligations. Take `⟨p, hp⟩` from `hF' γ hγ`. Use `⟨MvPolynomial.map f p, fun z hz => ?_⟩` and prove the remaining obligations. Rewrite using `[← (polySlash_laws R).2.2.2.2.1 S f, ← map_sub, hp z hz]`. Introduce and unpack `S _ f F ⟨ψ, p, hψ, hp⟩`.

Use `⟨fun z => MvPolynomial.map f (ψ z), MvPolynomial.map f p, fun γ hγ z hz => ?_, fun z hz => ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[← (polySlash_laws R).2.2.2.2.1 S f, hψ γ hγ z hz]`. Simplify using `only [hp z hz, map_add]`.
-/
theorem pot_triv_lin : ∀ (R : Type) [CommRing R] (w : ℕ) (Γ : Subgroup SL(2, ℤ)), (∀ F G, F ∈ Pot R w Γ → G ∈ Pot R w Γ → F + G ∈ Pot R w Γ) ∧ (0 ∈ Pot R w Γ) ∧ (∀ (c : R) F, F ∈ Pot R w Γ → c • F ∈ Pot R w Γ) ∧ (∀ F G, F ∈ Triv R w Γ → G ∈ Triv R w Γ → F + G ∈ Triv R w Γ) ∧ (∀ (c : R) F, F ∈ Triv R w Γ → c • F ∈ Triv R w Γ) ∧ (∀ (S : Type) [CommRing S] (f : R →+* S) F, F ∈ Pot R w Γ → (fun z => MvPolynomial.map f (F z)) ∈ Pot S w Γ) ∧ (∀ (S : Type) [CommRing S] (f : R →+* S) F, F ∈ Triv R w Γ → (fun z => MvPolynomial.map f (F z)) ∈ Triv S w Γ) := by
  intro R _ w Γ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro F G ⟨hF, hF'⟩ ⟨hG, hG'⟩
    refine ⟨fun z => (hF z).add (hG z), fun γ hγ => ?_⟩
    obtain ⟨p, hp⟩ := hF' γ hγ
    obtain ⟨q, hq⟩ := hG' γ hγ
    refine ⟨p + q, fun z hz => ?_⟩
    simp only [Pi.add_apply, map_add]
    rw [← hp z hz, ← hq z hz]; abel
  · refine ⟨fun z => MvPolynomial.isHomogeneous_zero _ _ _, fun γ _ => ⟨0, fun z _ => ?_⟩⟩
    simp
  · rintro c F ⟨hF, hF'⟩
    refine ⟨fun z => ?_, fun γ hγ => ?_⟩
    · simp only [Pi.smul_apply, MvPolynomial.smul_eq_C_mul]
      simpa using (MvPolynomial.isHomogeneous_C (Fin 2) c).mul (hF z)
    · obtain ⟨p, hp⟩ := hF' γ hγ
      refine ⟨c • p, fun z hz => ?_⟩
      simp only [Pi.smul_apply, map_smul]
      rw [← hp z hz, smul_sub]
  · rintro F G ⟨ψ, p, hψ, hp⟩ ⟨ψ', p', hψ', hp'⟩
    refine ⟨ψ + ψ', p + p', fun γ hγ z hz => ?_, fun z hz => ?_⟩
    · simp only [Pi.add_apply, map_add, hψ γ hγ z hz, hψ' γ hγ z hz]
    · simp only [Pi.add_apply, hp z hz, hp' z hz]; abel
  · rintro c F ⟨ψ, p, hψ, hp⟩
    refine ⟨c • ψ, c • p, fun γ hγ z hz => ?_, fun z hz => ?_⟩
    · simp only [Pi.smul_apply, map_smul, hψ γ hγ z hz]
    · simp only [Pi.smul_apply, hp z hz, smul_add]
  · rintro S _ f F ⟨hF, hF'⟩
    refine ⟨fun z => (hF z).map f, fun γ hγ => ?_⟩
    obtain ⟨p, hp⟩ := hF' γ hγ
    refine ⟨MvPolynomial.map f p, fun z hz => ?_⟩
    rw [← (polySlash_laws R).2.2.2.2.1 S f, ← map_sub, hp z hz]
  · rintro S _ f F ⟨ψ, p, hψ, hp⟩
    refine ⟨fun z => MvPolynomial.map f (ψ z), MvPolynomial.map f p, fun γ hγ z hz => ?_, fun z hz => ?_⟩
    · simp only
      rw [← (polySlash_laws R).2.2.2.2.1 S f, hψ γ hγ z hz]
    · simp only [hp z hz, map_add]

end GlobalTheory.KZ
