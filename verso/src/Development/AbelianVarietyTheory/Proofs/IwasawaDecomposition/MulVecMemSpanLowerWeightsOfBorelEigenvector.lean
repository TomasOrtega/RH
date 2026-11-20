import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerTransvectionMulVecMemSpanWeightVectorsDominStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerTriangularGLComplexInductionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLUDecompositionOfLeadingMinorsNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteShiftsVanishingLeadingMinorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyRepMulVecMemOfCofiniteScalarShiftStatement
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

/- English proof (translation)
Introduce `n ι _ _ Φ hΦ v lam hv B`. Establish `hdom : DomLE lam lam` using `⟨rfl, fun _ => le_rfl⟩`. Establish `hvS : v ∈ Sle Φ lam`. Use `Submodule.subset_span ⟨lam, hdom, fun D hD => hv.2 D ?_⟩` and prove the remaining obligations. Introduce `a b hab`.

Conclude with `hD (ne_of_gt hab)`. Establish `hstab : ∀ L : GL (Fin n) ℂ, L.val.BlockTriangular OrderDual.toDual → ∀ w ∈ Sle Φ lam, Φ L *ᵥ w ∈ Sle Φ lam`. Use `GlobalTheory.T.lowerTriangular_GL_complex_induction _ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `w hw`. Rewrite using `[hΦ.one, one_mulVec]`.

Conclude with `hw`. Introduce `A C hA hC w hw`. Rewrite using `[hΦ.mul, ← mulVec_mulVec]`. Conclude with `hA _ (hC w hw)`. Introduce `D hD w hw`.

Use `Submodule.span_induction (p := fun w _ => Φ D *ᵥ w ∈ Sle Φ lam) ?_ ?_ ?_ ?_ hw` and prove the remaining obligations. Introduce and unpack `u ⟨ν, hν, hu⟩`. Rewrite using `[hu D hD]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨ν, hν, hu⟩)`. Simplify using the standard rewrite rules.

Introduce `x y _ _ hx hy`. Rewrite using `[mulVec_add]`. Conclude with `Submodule.add_mem _ hx hy`. Introduce `c x _ hx`. Rewrite using `[mulVec_smul]`.

Conclude with `Submodule.smul_mem _ _ hx`. Introduce `i j s T hji hT w hw`. Use `Submodule.span_induction (p := fun w _ => Φ T *ᵥ w ∈ Sle Φ lam) ?_ ?_ ?_ ?_ hw` and prove the remaining obligations. Introduce and unpack `u ⟨ν, hν, hu⟩`. Conclude with `GlobalTheory.T.lowerTransvection_mulVec_mem_spanWeightVectorsDominatedBy Φ hΦ lam ν hν u hu i j hji s T hT`.

Simplify using the standard rewrite rules. Introduce `x y _ _ hx hy`. Rewrite using `[mulVec_add]`. Conclude with `Submodule.add_mem _ hx hy`. Introduce `c x _ hx`.

Rewrite using `[mulVec_smul]`. Conclude with `Submodule.smul_mem _ _ hx`. Establish `hbig : ∀ C : GL (Fin n) ℂ, (∀ (k : ℕ) (hk : k ≤ n), (C.val.submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0) → Φ C *ᵥ v ∈ Sle Φ lam`. Introduce `C hC`. Take `⟨L, U, hL, hU, rfl⟩` from `GlobalTheory.T.exists_LU_decomposition_of_leading_minors_ne_zero C hC`.

Rewrite using `[hΦ.mul, ← mulVec_mulVec, hv.2 U hU, mulVec_smul]`. Conclude with `Submodule.smul_mem _ _ (hstab L hL v hvS)`. Use `GlobalTheory.T.polyRep_mulVec_mem_of_cofinite_scalar_shift Φ hΦ _ v B _ (GlobalTheory.T.finite_shifts_vanishing_leading_minor B.val) ?_` and prove the remaining obligations. Introduce `s hs C hC`. Apply `hbig` to reduce the goal to its premises.

Rewrite using `[hC]`. Simplify using `using hs`.
-/
theorem mulVec_mem_sle_of_isBEig : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (v : ι → ℂ) (lam : Fin n → ℤ), IsBEig Φ v lam → ∀ B : GL (Fin n) ℂ, Φ B *ᵥ v ∈ Sle Φ lam := by
  intro n ι _ _ Φ hΦ v lam hv B
  have hdom : DomLE lam lam := ⟨rfl, fun _ => le_rfl⟩
  have hvS : v ∈ Sle Φ lam := by
    refine Submodule.subset_span ⟨lam, hdom, fun D hD => hv.2 D ?_⟩
    intro a b hab
    exact hD (ne_of_gt hab)

  have hstab : ∀ L : GL (Fin n) ℂ, L.val.BlockTriangular OrderDual.toDual →
      ∀ w ∈ Sle Φ lam, Φ L *ᵥ w ∈ Sle Φ lam := by
    refine GlobalTheory.T.lowerTriangular_GL_complex_induction _ ?_ ?_ ?_ ?_
    · intro w hw; rw [hΦ.one, one_mulVec]; exact hw
    · intro A C hA hC w hw
      rw [hΦ.mul, ← mulVec_mulVec]
      exact hA _ (hC w hw)
    · intro D hD w hw
      refine Submodule.span_induction (p := fun w _ => Φ D *ᵥ w ∈ Sle Φ lam) ?_ ?_ ?_ ?_ hw
      · rintro u ⟨ν, hν, hu⟩
        rw [hu D hD]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨ν, hν, hu⟩)
      · simp
      · intro x y _ _ hx hy; rw [mulVec_add]; exact Submodule.add_mem _ hx hy
      · intro c x _ hx; rw [mulVec_smul]; exact Submodule.smul_mem _ _ hx
    · intro i j s T hji hT w hw
      refine Submodule.span_induction (p := fun w _ => Φ T *ᵥ w ∈ Sle Φ lam) ?_ ?_ ?_ ?_ hw
      · rintro u ⟨ν, hν, hu⟩
        exact GlobalTheory.T.lowerTransvection_mulVec_mem_spanWeightVectorsDominatedBy Φ hΦ lam ν hν u hu i j hji s T hT
      · simp
      · intro x y _ _ hx hy; rw [mulVec_add]; exact Submodule.add_mem _ hx hy
      · intro c x _ hx; rw [mulVec_smul]; exact Submodule.smul_mem _ _ hx

  have hbig : ∀ C : GL (Fin n) ℂ,
      (∀ (k : ℕ) (hk : k ≤ n), (C.val.submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0) →
      Φ C *ᵥ v ∈ Sle Φ lam := by
    intro C hC
    obtain ⟨L, U, hL, hU, rfl⟩ := GlobalTheory.T.exists_LU_decomposition_of_leading_minors_ne_zero C hC
    rw [hΦ.mul, ← mulVec_mulVec, hv.2 U hU, mulVec_smul]
    exact Submodule.smul_mem _ _ (hstab L hL v hvS)

  refine GlobalTheory.T.polyRep_mulVec_mem_of_cofinite_scalar_shift Φ hΦ _ v B _ (GlobalTheory.T.finite_shifts_vanishing_leading_minor B.val) ?_
  intro s hs C hC
  apply hbig
  rw [hC]
  simpa using hs

end GlobalTheory.AlgWtHW
