import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PPartRealSmul
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F) (R : RiemLat E g Λ)

open Classical in

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem perExt_I_of_pBar {τ : Ψ} {y : Fin (j + j') → ℂ} (h : C.pBar R τ y = 0) :
    C.perExt R (Pi.single τ (Complex.I • y)) = Complex.I • C.perExt R (Pi.single τ y) := by
  ext k
  have hk := congrFun h k
  simp only [LatEmb.pBar, Pi.smul_apply, Pi.add_apply, Pi.zero_apply, smul_eq_mul] at hk ⊢
  linear_combination (-2 * Complex.I) * hk +
    ((C.perExt R (Pi.single τ (Complex.I • y))) k) * Complex.I_mul_I

open Classical in

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem pPart_of_pBar {τ : Ψ} {y : Fin (j + j') → ℂ} (h : C.pBar R τ y = 0) :
    C.pPart R τ y = C.perExt R (Pi.single τ y) := by
  have h1 := perExt_I_of_pBar C R h
  ext k
  simp only [LatEmb.pPart, h1, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  linear_combination (-(1 / 2 : ℂ) * (C.perExt R (Pi.single τ y)) k) * Complex.I_mul_I

open Classical in

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem Fm_single (τ : Ψ) (y x : Fin (j + j') → ℂ) :
    C.Fm (Pi.single τ y) (Pi.single τ x) =
      2 * (embOf (F.σ τ) C.xi * (star x ⬝ᵥ (C.gr τ *ᵥ y))).re := by
  unfold LatEmb.Fm
  rw [Finset.sum_eq_single τ]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ τ) h

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem xi_block {A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ} (hA : C.IsAdapted R A) (τ : Ψ)
    (x y : Fin j' → ℂ) :
    embOf (F.σ τ) C.xi * (star (A τ *ᵥ Sum.elim 0 x) ⬝ᵥ (C.gr τ *ᵥ (A τ *ᵥ Sum.elim 0 y))) =
      -(Complex.I * (C.c : ℂ) * (star x ⬝ᵥ y)) := by
  have hs : star (A τ *ᵥ Sum.elim 0 x) ⬝ᵥ (C.sgr τ *ᵥ (A τ *ᵥ Sum.elim 0 y)) = -(star x ⬝ᵥ y) := by
    have h1 : star (A τ *ᵥ Sum.elim 0 x) ⬝ᵥ (C.sgr τ *ᵥ (A τ *ᵥ Sum.elim 0 y)) =
        star (Sum.elim 0 x : Sg j j' → ℂ) ⬝ᵥ (((A τ)ᴴ * C.sgr τ * A τ) *ᵥ Sum.elim 0 y) := by
      rw [Matrix.star_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      simp only [Matrix.dotProduct_mulVec]
    rw [h1, hA.unit τ]
    simp only [sgI, Matrix.fromBlocks_mulVec]
    simp [dotProduct, Fintype.sum_sum_type, Matrix.neg_mulVec]
  have hg : C.sgr τ = ((C.eps τ : ℝ) : ℂ) • C.gr τ := rfl
  rw [hg, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at hs
  rw [C.xi_eq τ]
  push_cast
  linear_combination (Complex.I * (C.c : ℂ)) * hs

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem gram_last_block : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R : RiemLat E g Λ) (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ), (∀ y y', (C.perExt R y ⬝ᵥ R.Hm *ᵥ star (C.perExt R y')).im = C.Fm y y') → C.IsAdapted R A → ∀ (τ : Ψ) (x y : Fin j' → ℂ), R.ip (C.pPart R τ (A τ *ᵥ Sum.elim 0 x)) (C.pPart R τ (A τ *ᵥ Sum.elim 0 y)) = ((2 * C.c : ℝ) : ℂ) * (star x ⬝ᵥ y) := by
  classical
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C R A hF hA τ x y
  have hx := pPart_of_pBar C R (hA.kerBar τ x)
  have hy := pPart_of_pBar C R (hA.kerBar τ y)
  have hiy := perExt_I_of_pBar C R (hA.kerBar τ y)
  have h1 := hF (Pi.single τ (A τ *ᵥ Sum.elim 0 y)) (Pi.single τ (A τ *ᵥ Sum.elim 0 x))
  have h2 := hF (Pi.single τ (Complex.I • (A τ *ᵥ Sum.elim 0 y))) (Pi.single τ (A τ *ᵥ Sum.elim 0 x))
  rw [Fm_single, xi_block C R hA] at h1
  rw [Fm_single, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, mul_left_comm, xi_block C R hA, hiy,
    smul_dotProduct, smul_eq_mul] at h2
  rw [RiemLat.ip, hx, hy]
  set H := C.perExt R (Pi.single τ (A τ *ᵥ Sum.elim 0 y)) ⬝ᵥ
    R.Hm *ᵥ star (C.perExt R (Pi.single τ (A τ *ᵥ Sum.elim 0 x))) with hH
  set w := star x ⬝ᵥ y with hw
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im] at h1 h2 ⊢
    linarith
  · simp [Complex.mul_re, Complex.mul_im] at h1 h2 ⊢
    linarith

end

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart
