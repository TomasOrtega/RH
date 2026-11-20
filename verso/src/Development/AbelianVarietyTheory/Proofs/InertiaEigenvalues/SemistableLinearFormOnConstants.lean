import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

/- English proof (translation)
Introduce `l _ P K`. Use `haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := (P.PD K).finK₀`. Use `haveI : Nontrivial P.R.B := by`. Use `⟨⟨(P.PD K).t, 0, fun h => (P.PD K).not_mem_filtration_two ?_⟩⟩` and prove the remaining obligations. Rewrite using `[h, map_zero]`.

Conclude with `Submodule.zero_mem _`. Set `ι : ↥(K0 K) →ₗ[ℚ_[l]] Bst P` to `((Polynomial.monomial 0 : P.R.B →ₗ[P.R.B] Polynomial P.R.B).restrictScalars ℚ_[l]).comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) P.R.B).toLinearMap`. Establish `hι : ∀ c, ι c = Polynomial.C (algebraMap ↥(K0 K) P.R.B c)` using `fun c => by`. Simplify using `[ι, Polynomial.monomial_zero_left]`. Establish `hinj : Function.Injective ι`.

Introduce `a b hab`. Rewrite `hab` using `[hι, hι]`. Conclude with `(algebraMap ↥(K0 K) P.R.B).injective (Polynomial.C_injective hab)`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective ι (LinearMap.ker_eq_bot.mpr hinj)`. Establish `hgι : ∀ c, g (ι c) = c` using `fun c => LinearMap.congr_fun hg c`.

Use `⟨(Algebra.trace ℚ_[l] ↥(K0 K)).comp g, ?_, ?_⟩` and prove the remaining obligations. Introduce `c`. Establish `hφ : phiSt P (Polynomial.C (algebraMap ↥(K0 K) P.R.B c)) = ι ((P.PD K).σ c)`. Establish `hC : ∀ b : P.R.B, phiSt P (Polynomial.C b) = Polynomial.C (P.φB b)` using `fun b => by`. Simplify using `[phiSt, stHom]`.

Rewrite using `[hC, ← P.PD_φ K, (P.PD K).φ_K₀, hι]`. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, hφ, ← hι, hgι, hgι]`. Conclude with `Algebra.trace_eq_of_algEquiv (AlgEquiv.ofBijective (P.PD K).σ (P.PD K).σ_bij) c`. Introduce `c h`. Assume the negation of the conclusion as `hc`.

Establish `h1` using `h c⁻¹`. Rewrite `h1` using `[← map_mul, ← map_mul, ← hι, LinearMap.comp_apply, hgι, inv_mul_cancel₀ hc]`. Establish `h2 : Algebra.trace ℚ_[l] ↥(K0 K) 1 = (Module.finrank ℚ_[l] ↥(K0 K) : ℚ_[l])`. Rewrite using `[← map_one (algebraMap ℚ_[l] ↥(K0 K)), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]`. Rewrite `h1` using `[h2]`.

Conclude with `(Nat.cast_ne_zero.mpr Module.finrank_pos.ne') h1`.
-/
theorem exists_phiSt_invariant_nondegenerate_linearForm :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), ∃ lam : Bst P →ₗ[ℚ_[l]] ℚ_[l], (∀ c : ↥(K0 K), lam (phiSt P (Polynomial.C (algebraMap ↥(K0 K) P.R.B c))) = lam (Polynomial.C (algebraMap ↥(K0 K) P.R.B c))) ∧ ∀ c : ↥(K0 K), (∀ c' : ↥(K0 K), lam (Polynomial.C (algebraMap ↥(K0 K) P.R.B c') * Polynomial.C (algebraMap ↥(K0 K) P.R.B c)) = 0) → c = 0 := by
  intro l _ P K
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := (P.PD K).finK₀
  haveI : Nontrivial P.R.B := by
    refine ⟨⟨(P.PD K).t, 0, fun h => (P.PD K).not_mem_filtration_two ?_⟩⟩
    rw [h, map_zero]
    exact Submodule.zero_mem _

  let ι : ↥(K0 K) →ₗ[ℚ_[l]] Bst P :=
    ((Polynomial.monomial 0 : P.R.B →ₗ[P.R.B] Polynomial P.R.B).restrictScalars ℚ_[l]).comp
      (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) P.R.B).toLinearMap
  have hι : ∀ c, ι c = Polynomial.C (algebraMap ↥(K0 K) P.R.B c) := fun c => by
    simp [ι, Polynomial.monomial_zero_left]
  have hinj : Function.Injective ι := by
    intro a b hab
    rw [hι, hι] at hab
    exact (algebraMap ↥(K0 K) P.R.B).injective (Polynomial.C_injective hab)

  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective ι (LinearMap.ker_eq_bot.mpr hinj)
  have hgι : ∀ c, g (ι c) = c := fun c => LinearMap.congr_fun hg c
  refine ⟨(Algebra.trace ℚ_[l] ↥(K0 K)).comp g, ?_, ?_⟩
  ·
    intro c
    have hφ : phiSt P (Polynomial.C (algebraMap ↥(K0 K) P.R.B c)) = ι ((P.PD K).σ c) := by
      have hC : ∀ b : P.R.B, phiSt P (Polynomial.C b) = Polynomial.C (P.φB b) := fun b => by
        simp [phiSt, stHom]
      rw [hC, ← P.PD_φ K, (P.PD K).φ_K₀, hι]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hφ, ← hι, hgι, hgι]
    exact Algebra.trace_eq_of_algEquiv (AlgEquiv.ofBijective (P.PD K).σ (P.PD K).σ_bij) c
  ·
    intro c h
    by_contra hc
    have h1 := h c⁻¹
    rw [← map_mul, ← map_mul, ← hι, LinearMap.comp_apply, hgι, inv_mul_cancel₀ hc] at h1
    have h2 : Algebra.trace ℚ_[l] ↥(K0 K) 1 = (Module.finrank ℚ_[l] ↥(K0 K) : ℚ_[l]) := by
      rw [← map_one (algebraMap ℚ_[l] ↥(K0 K)), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]
    rw [h2] at h1
    exact (Nat.cast_ne_zero.mpr Module.finrank_pos.ne') h1

end GlobalTheory.PMon
