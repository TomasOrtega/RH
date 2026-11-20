import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosOkId
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCofactorTwistHighestWeightStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorTwistRelationRowDivSwapStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowDivRowWeightStatement

open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

namespace GlobalTheory.ValCmp

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact ⟨⟨_, hwRowWeight R _ _ le_rfl ν hν⟩, GlobalTheory.T.exists_cofactorTwist_highestWeight R m ν hν h0⟩`. Consider the case `cons x w ih`. Take `⟨a, b, k⟩` from `x`. Take `⟨⟨μ, hμ⟩, g, hg, hrel⟩` from `ih`.

Establish `hstep : applyWord R ((a, b, k) :: w) (hw R le_rfl ν) = rowDiv R a b k (applyWord R w (hw R le_rfl ν))` using `rfl`. Rewrite using `[hstep]`. Take `⟨h1, h2⟩` from `GlobalTheory.T.isWeightedHomogeneous_div_and_diag_eq_choose_smul R _ _ μ _ hμ`. Use `⟨h1 a b k, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hab : a = b`.

Substitute `hab` using the available equality. Use `⟨((μ a).choose k) • g, nsmul_mem hg _, ?_⟩` and prove the remaining obligations. Rewrite using `[h2 a k]`. Unfold `CofRel at hrel ⊢`. Rewrite using `[map_nsmul, ← hrel, mul_smul_comm]`.

Conclude with `⟨_, zsmul_mem (weylRowDivStable R _ _ le_rfl _ b a k g hg) _, GlobalTheory.T.cofactorTwistRelation_rowDiv_swap R m ν a b k _ g hab hrel⟩`.
-/
theorem applyWord_hw_cofRel (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ) (hν : Antitone ν)
    (h0 : ν (Fin.last m) = 0) (w : List (Fin (m + 1) × Fin (m + 1) × ℕ)) :
    (∃ μ : Fin (m + 1) → ℕ, IsWeightedHomogeneous (rowW (m + 1) (m + 1)) (applyWord R w (hw R le_rfl ν)) μ) ∧
      ∃ g ∈ weyl R (m + 1) (m + 1) le_rfl (nuDual ν), CofRel R m ν (applyWord R w (hw R le_rfl ν)) g := by
  induction w with
  | nil => exact ⟨⟨_, hwRowWeight R _ _ le_rfl ν hν⟩, GlobalTheory.T.exists_cofactorTwist_highestWeight R m ν hν h0⟩
  | cons x w ih =>
    obtain ⟨a, b, k⟩ := x
    obtain ⟨⟨μ, hμ⟩, g, hg, hrel⟩ := ih
    have hstep : applyWord R ((a, b, k) :: w) (hw R le_rfl ν) =
        rowDiv R a b k (applyWord R w (hw R le_rfl ν)) := rfl
    rw [hstep]
    obtain ⟨h1, h2⟩ := GlobalTheory.T.isWeightedHomogeneous_div_and_diag_eq_choose_smul R _ _ μ _ hμ
    refine ⟨h1 a b k, ?_⟩
    by_cases hab : a = b
    · subst hab
      refine ⟨((μ a).choose k) • g, nsmul_mem hg _, ?_⟩
      rw [h2 a k]
      unfold CofRel at hrel ⊢
      rw [map_nsmul, ← hrel, mul_smul_comm]
    · exact ⟨_, zsmul_mem (weylRowDivStable R _ _ le_rfl _ b a k g hg) _, GlobalTheory.T.cofactorTwistRelation_rowDiv_swap R m ν a b k _ g hab hrel⟩

/- English proof (translation)
Introduce `R _ _ m ν hν h0 f hf`. Unfold `weyl at hf`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨w, rfl⟩` from `hx`.

Conclude with `(applyWord_hw_cofRel R m ν hν h0 w).2`. Consider the case `zero => exact ⟨0, zero_mem _, by simp [CofRel]⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨g, hg, hr⟩` from `hx`. Take `⟨g', hg', hr'⟩` from `hy`.

Use `⟨g + g', add_mem hg hg', ?_⟩` and prove the remaining obligations. Unfold `CofRel at hr hr' ⊢`. Rewrite using `[map_add, ← hr, ← hr', mul_add]`. Consider the case `smul c x _ hx`. Take `⟨g, hg, hr⟩` from `hx`.

Use `⟨c • g, Submodule.smul_mem _ c hg, ?_⟩` and prove the remaining obligations. Unfold `CofRel at hr ⊢`. Rewrite using `[map_smul, ← hr, mul_smul_comm]`.
-/
theorem weyl_exists_cofRel : ∀ (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν →
    ν (Fin.last m) = 0 → ∀ f ∈ weyl R (m + 1) (m + 1) le_rfl ν,
      ∃ g ∈ weyl R (m + 1) (m + 1) le_rfl (nuDual ν), CofRel R m ν f g := by
  intro R _ _ m ν hν h0 f hf
  unfold weyl at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact (applyWord_hw_cofRel R m ν hν h0 w).2
  | zero => exact ⟨0, zero_mem _, by simp [CofRel]⟩
  | add x y _ _ hx hy =>
    obtain ⟨g, hg, hr⟩ := hx
    obtain ⟨g', hg', hr'⟩ := hy
    refine ⟨g + g', add_mem hg hg', ?_⟩
    unfold CofRel at hr hr' ⊢
    rw [map_add, ← hr, ← hr', mul_add]
  | smul c x _ hx =>
    obtain ⟨g, hg, hr⟩ := hx
    refine ⟨c • g, Submodule.smul_mem _ c hg, ?_⟩
    unfold CofRel at hr ⊢
    rw [map_smul, ← hr, mul_smul_comm]

end GlobalTheory.ValCmp
