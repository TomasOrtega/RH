import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.PurePer

open ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `[FD.Data.emb]`.
-/
theorem emb_smul' (τ : E →+* ℂ) (a : E) (v : Fin r → E) :
    FD.Data.emb τ (a • v) = τ a • FD.Data.emb τ v := by
  funext k
  simp [FD.Data.emb]

/- English proof (translation)
Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem u hu`. Take `⟨a, rfl⟩` from `hu`. Establish `h1 : (M⁻¹.mulVec (FD.col M (Fin.castLE hp a))) k = (M⁻¹ * M) k (Fin.castLE hp a)`. Simplify using `[Matrix.mulVec, dotProduct, Matrix.mul_apply, FD.col]`.

Establish `hne : k ≠ Fin.castLE hp a`. Introduce `h`. Establish `h2` using `congrArg Fin.val h`. Establish `h3` using `a.isLt`. Simplify using `at h2`.

Use linear arithmetic over natural numbers and integers. Use `show (M⁻¹.mulVec (FD.col M (Fin.castLE hp a))) k = 0`. Rewrite using `[h1, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hM), Matrix.one_apply_ne hne]`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [Matrix.mulVec_add, Pi.add_apply, ha, hb, add_zero]`.

Consider the case `smul c a _ ha => rw [Matrix.mulVec_smul, Pi.smul_apply, ha, smul_zero]`.
-/
theorem inv_mulVec_eq_zero {p : ℕ} (hp : p ≤ r) (M : Matrix (Fin r) (Fin r) ℂ) (hM : M.det ≠ 0)
    {u : Fin r → ℂ}
    (hu : u ∈ Submodule.span ℂ (Set.range fun a : Fin p => FD.col M (Fin.castLE hp a)))
    (k : Fin r) (hk : p ≤ (k : ℕ)) : (M⁻¹.mulVec u) k = 0 := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, rfl⟩ := hu
    have h1 : (M⁻¹.mulVec (FD.col M (Fin.castLE hp a))) k = (M⁻¹ * M) k (Fin.castLE hp a) := by
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, FD.col]
    have hne : k ≠ Fin.castLE hp a := by
      intro h
      have h2 := congrArg Fin.val h
      have h3 := a.isLt
      simp at h2
      omega
    show (M⁻¹.mulVec (FD.col M (Fin.castLE hp a))) k = 0
    rw [h1, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hM), Matrix.one_apply_ne hne]
  | zero => simp
  | add a b _ _ ha hb => rw [Matrix.mulVec_add, Pi.add_apply, ha, hb, add_zero]
  | smul c a _ ha => rw [Matrix.mulVec_smul, Pi.smul_apply, ha, smul_zero]

/- English proof (translation)
Introduce `E _ _ _ r X La x lam hx hb a j τ i`. Take `⟨-, -, ho, -, -, -, hsp⟩` from `hb`. Use `⟨fun hj hτ => ?_, fun hj hτ hi => ?_⟩` and prove the remaining obligations. Unfold `perFr`. Rewrite using `[dif_pos hτ]`.

Use `split_ifs with h`. Use `inv_mulVec_eq_zero X.p0_le _ (hx ⟨τ, hτ⟩).1 ?_ _ (by simp)` and prove the remaining obligations. Rewrite using `[hsp ⟨τ, hτ⟩, emb_smul']`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)`. Both sides reduce to the same expression.

Unfold `perFr`. Rewrite using `[dif_neg hτ]`. Use `split_ifs with h' h`. Establish `hm : FD.col (FD.mat x ⟨conjEmb τ, h'⟩) ⟨X.p0 - 1 - i, h⟩ ∈ Submodule.span ℂ (Set.range fun a : Fin X.p0 => FD.Data.emb (conjEmb τ) (lam (Fin.castLE X.p0_le a)))`. Use `hsp ⟨conjEmb τ, h'⟩` as an intermediate fact.

Simplify using `only at this`. Rewrite using `[← this]`. Conclude with `Submodule.subset_span ⟨⟨X.p0 - 1 - i, by omega⟩, rfl⟩`. Rewrite using `[emb_smul', FD.hermC_smul_right]`. Use `mul_eq_zero_of_right _ ?_` and prove the remaining obligations.

Generalize the expression as in `FD.col (FD.mat x ⟨conjEmb τ, h'⟩) ⟨X.p0 - 1 - i, h⟩ = w at hm`. Proceed by induction on `hm using Submodule.span_induction with`. Consider the case `mem w hw`. Take `⟨k, rfl⟩` from `hw`. Rewrite using `[FD.hermC_emb, ho _ j (by simpa using k.isLt) hj, map_zero]`.

Consider the case `zero => exact FD.hermC_zero_left _ _ _`. Consider the case `add a b _ _ ha hb => rw [FD.hermC_add_left, ha, hb, add_zero]`. Consider the case `smul c a _ ha => rw [FD.hermC_smul_left, ha, mul_zero]`. Both sides reduce to the same expression. Both sides reduce to the same expression.
-/
theorem perFr_pure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : FD.DataX E r) (La : ℝ) (x : FD.Frame X.Ψ r) (lam : Fin r → Fin r → E), x ∈ X.toData.dom → FD.LamBasis X La x lam → ∀ (a : E) (j : Fin r) (τ : E →+* ℂ) (i : ℕ), ((j : ℕ) < X.p0 → τ ∈ X.Ψ → perFr X.toData x (a • lam j) τ i = 0) ∧ (X.p0 ≤ (j : ℕ) → τ ∉ X.Ψ → i < X.p0 → perFr X.toData x (a • lam j) τ i = 0) := by
  intro E _ _ _ r X La x lam hx hb a j τ i
  obtain ⟨-, -, ho, -, -, -, hsp⟩ := hb
  refine ⟨fun hj hτ => ?_, fun hj hτ hi => ?_⟩
  · unfold perFr
    rw [dif_pos hτ]
    split_ifs with h
    · refine inv_mulVec_eq_zero X.p0_le _ (hx ⟨τ, hτ⟩).1 ?_ _ (by simp)
      rw [hsp ⟨τ, hτ⟩, emb_smul']
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
    · rfl
  · unfold perFr
    rw [dif_neg hτ]
    split_ifs with h' h
    · have hm : FD.col (FD.mat x ⟨conjEmb τ, h'⟩) ⟨X.p0 - 1 - i, h⟩ ∈
          Submodule.span ℂ (Set.range fun a : Fin X.p0 =>
            FD.Data.emb (conjEmb τ) (lam (Fin.castLE X.p0_le a))) := by
        have := hsp ⟨conjEmb τ, h'⟩
        simp only at this
        rw [← this]
        exact Submodule.subset_span ⟨⟨X.p0 - 1 - i, by omega⟩, rfl⟩
      rw [emb_smul', FD.hermC_smul_right]
      refine mul_eq_zero_of_right _ ?_
      generalize FD.col (FD.mat x ⟨conjEmb τ, h'⟩) ⟨X.p0 - 1 - i, h⟩ = w at hm
      induction hm using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨k, rfl⟩ := hw
        rw [FD.hermC_emb, ho _ j (by simpa using k.isLt) hj, map_zero]
      | zero => exact FD.hermC_zero_left _ _ _
      | add a b _ _ ha hb => rw [FD.hermC_add_left, ha, hb, add_zero]
      | smul c a _ ha => rw [FD.hermC_smul_left, ha, mul_zero]
    · rfl
    · rfl

end GlobalTheory.PurePer
