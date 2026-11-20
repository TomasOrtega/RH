import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

/- English proof (translation)
Introduce `hθ hsemi L`. Set `σ : WittVector p k →+* k` to `(WittVector.constantCoeff).comp e.symm.toRingHom`. Establish `hσ : Function.Surjective σ`. Introduce `x`. Take `⟨a, ha⟩ : ∃ a : WittVector p k, WittVector.constantCoeff a = x` from `⟨WittVector.teichmuller p x, by simp⟩`.

Conclude with `⟨e a, by simp [σ, ha]⟩`. Use `letI : Algebra (WittVector p k) k := σ.toAlgebra`. Use `letI : Module (WittVector p k) U := Module.compHom U σ`. Use `haveI : IsScalarTower (WittVector p k) k U := ⟨fun a b u => by show (σ a * b) • u = σ a • (b • u)`. Conclude with `mul_smul _ _ _⟩`.

Establish `hlenU : Module.length (WittVector p k) U = Module.finrank k U`. Rewrite using `[Module.length_eq_of_surjective (R := k) (S := WittVector p k) (M := U) hσ, Module.length_eq_finrank]`. Set `θl : N →ₗ[WittVector p k] U` to `{ toFun := θ map_add' := θ.map_add map_smul' := fun a n => by`. Establish `h` using `hsemi (e.symm a) n`. Rewrite `h` using `[RingEquiv.apply_symm_apply]`.

Conclude with `h }`. Establish `hθl : Function.Surjective θl` using `hθ`. Use `⟨fun hL => ?_, fun hL => ?_⟩` and prove the remaining obligations. Establish `hle : L ≤ LinearMap.ker θl` using `fun n hn => hL n hn`. Rewrite using `[← hlenU]`.

Conclude with `Module.length_le_of_surjective (L.liftQ θl hle) (by`. Introduce `u`. Take `⟨n, rfl⟩` from `hθl u`. Conclude with `⟨Submodule.Quotient.mk n, rfl⟩)`. Establish `hK : L = LinearMap.ker θl`.

Use extensionality with `n`. Conclude with `hL n`. Rewrite using `[← hlenU, hK]`. Conclude with `(θl.quotKerEquivOfSurjective hθl).length_eq`.
-/
theorem length_ge_finrank_of_semilinear_surj (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (N U : Type) [AddCommGroup N] [Module (WittVector p k) N] [AddCommGroup U]
    [Module k U] [Module.Finite k U] (e : (WittVector p k) ≃+* (WittVector p k)) (θ : N →+ U) :
    Function.Surjective θ → (∀ (a : (WittVector p k)) n, θ (e a • n) = WittVector.constantCoeff a • θ n) →
    ∀ L : Submodule (WittVector p k) N, ((∀ n ∈ L, θ n = 0) →
      (Module.finrank k U : ℕ∞) ≤ Module.length (WittVector p k) (N ⧸ L)) ∧
      ((∀ n, n ∈ L ↔ θ n = 0) → Module.length (WittVector p k) (N ⧸ L) = Module.finrank k U) := by
  intro hθ hsemi L
  let σ : WittVector p k →+* k := (WittVector.constantCoeff).comp e.symm.toRingHom
  have hσ : Function.Surjective σ := by
    intro x
    obtain ⟨a, ha⟩ : ∃ a : WittVector p k, WittVector.constantCoeff a = x :=
      ⟨WittVector.teichmuller p x, by simp⟩
    exact ⟨e a, by simp [σ, ha]⟩
  letI : Algebra (WittVector p k) k := σ.toAlgebra
  letI : Module (WittVector p k) U := Module.compHom U σ
  haveI : IsScalarTower (WittVector p k) k U :=
    ⟨fun a b u => by
      show (σ a * b) • u = σ a • (b • u)
      exact mul_smul _ _ _⟩
  have hlenU : Module.length (WittVector p k) U = Module.finrank k U := by
    rw [Module.length_eq_of_surjective (R := k) (S := WittVector p k) (M := U) hσ,
      Module.length_eq_finrank]
  let θl : N →ₗ[WittVector p k] U :=
    { toFun := θ
      map_add' := θ.map_add
      map_smul' := fun a n => by
        have h := hsemi (e.symm a) n
        rw [RingEquiv.apply_symm_apply] at h
        exact h }
  have hθl : Function.Surjective θl := hθ
  refine ⟨fun hL => ?_, fun hL => ?_⟩
  · have hle : L ≤ LinearMap.ker θl := fun n hn => hL n hn
    rw [← hlenU]
    exact Module.length_le_of_surjective (L.liftQ θl hle) (by
      intro u
      obtain ⟨n, rfl⟩ := hθl u
      exact ⟨Submodule.Quotient.mk n, rfl⟩)
  · have hK : L = LinearMap.ker θl := by
      ext n
      exact hL n
    rw [← hlenU, hK]
    exact (θl.quotKerEquivOfSurjective hθl).length_eq

end GlobalTheory.Dieu
