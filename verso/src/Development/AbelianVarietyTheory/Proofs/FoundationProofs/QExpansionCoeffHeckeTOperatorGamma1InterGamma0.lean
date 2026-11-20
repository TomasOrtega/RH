import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionCoeffPeriodOneEqOfHasSumStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixModularFormGamma1InterGamStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Gamma1InterGamma0ModularFormHasSumQExpansionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumHeckeUOperatorExplicitStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumHeckeVOperatorExplicitStatement

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

/- English proof (translation)
Introduce `N l q k σ hN hq _ hσ f n`. Establish `hq0 : 0 < q` using `hq.pos`. Take `⟨g, hg⟩` from `GlobalTheory.T.diamondOperatorOfMatrix_modularForm_gamma1InterGamma0 N l k (q : ℤ) σ hN hσ f`. Establish `hf` using `GlobalTheory.T.gamma1InterGamma0_modularForm_hasSum_qExpansion N l k hN f`. Establish `hgs` using `GlobalTheory.T.gamma1InterGamma0_modularForm_hasSum_qExpansion N l k hN g`.

Establish `hU` using `GlobalTheory.T.hasSum_heckeUOperatorExplicit q (⇑f) (fun m => GlobalTheory.Hk.coef ⇑f m) hq0 hf`. Establish `hV` using `GlobalTheory.T.hasSum_heckeVOperatorExplicit q (⇑g) (fun m => GlobalTheory.Hk.coef ⇑g m) hq0 hgs`. Establish `hsum : ∀ τ : ℍ, HasSum (fun m => (GlobalTheory.Hk.coef ⇑f (q * m) + (q : ℂ) ^ (k - 1) * (if q ∣ m then GlobalTheory.Hk.coef ⇑g (m / q) else 0)) • Function.Periodic.qParam 1 τ ^ m) (GlobalTheory.Hk.heckeT k q σ ⇑f τ)`. Introduce `τ`. Establish `h2` using `(hU τ).add ((hV τ).mul_left ((q : ℂ) ^ (k - 1)))`.

Establish `e : GlobalTheory.Hk.heckeT k q σ ⇑f τ = GlobalTheory.Hk.uOp q ⇑f τ + (q : ℂ) ^ (k - 1) * GlobalTheory.Hk.vOp q ⇑g τ`. Rewrite using `[hg]`. Both sides reduce to the same expression. Rewrite using `[e]`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `m`. Simplify using `only [smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[GlobalTheory.T.qExpansionCoeffPeriodOne_eq_of_hasSum _ _ hsum n, ← hg]`.
-/
theorem coef_heckeT : ∀ (N l q : ℕ) (k : ℤ) (σ : SL(2, ℤ)), 0 < N → q.Prime → ¬ q ∣ N * l →
    GlobalTheory.Hk.IsDia N l q σ → ∀ (f : ModularForm (GlobalTheory.Hk.lev N l) k) (n : ℕ),
    GlobalTheory.Hk.coef (GlobalTheory.Hk.heckeT k q σ ⇑f) n = GlobalTheory.Hk.coef ⇑f (q * n) +
      (q : ℂ) ^ (k - 1) * (if q ∣ n then GlobalTheory.Hk.coef (GlobalTheory.Hk.dia k σ ⇑f) (n / q) else 0) := by
  intro N l q k σ hN hq _ hσ f n
  have hq0 : 0 < q := hq.pos
  obtain ⟨g, hg⟩ := GlobalTheory.T.diamondOperatorOfMatrix_modularForm_gamma1InterGamma0 N l k (q : ℤ) σ hN hσ f
  have hf := GlobalTheory.T.gamma1InterGamma0_modularForm_hasSum_qExpansion N l k hN f
  have hgs := GlobalTheory.T.gamma1InterGamma0_modularForm_hasSum_qExpansion N l k hN g
  have hU := GlobalTheory.T.hasSum_heckeUOperatorExplicit q (⇑f) (fun m => GlobalTheory.Hk.coef ⇑f m) hq0 hf
  have hV := GlobalTheory.T.hasSum_heckeVOperatorExplicit q (⇑g) (fun m => GlobalTheory.Hk.coef ⇑g m) hq0 hgs
  have hsum : ∀ τ : ℍ, HasSum (fun m => (GlobalTheory.Hk.coef ⇑f (q * m) +
      (q : ℂ) ^ (k - 1) * (if q ∣ m then GlobalTheory.Hk.coef ⇑g (m / q) else 0)) •
        Function.Periodic.qParam 1 τ ^ m) (GlobalTheory.Hk.heckeT k q σ ⇑f τ) := by
    intro τ
    have h2 := (hU τ).add ((hV τ).mul_left ((q : ℂ) ^ (k - 1)))
    have e : GlobalTheory.Hk.heckeT k q σ ⇑f τ =
        GlobalTheory.Hk.uOp q ⇑f τ + (q : ℂ) ^ (k - 1) * GlobalTheory.Hk.vOp q ⇑g τ := by
      rw [hg]; rfl
    rw [e]
    convert h2 using 1
    funext m
    simp only [smul_eq_mul]
    ring
  rw [GlobalTheory.T.qExpansionCoeffPeriodOne_eq_of_hasSum _ _ hsum n, ← hg]

end GlobalTheory.Hk
