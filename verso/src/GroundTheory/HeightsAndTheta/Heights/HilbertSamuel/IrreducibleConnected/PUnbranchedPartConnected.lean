import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.StatementsUnbranched
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.StClopenPieceSheetCount
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.StPrimeCoverPieceSheets
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PManifoldZerosComplementConnected
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Matrix

/- English proof (translation)
Establish `h` using `IndefiniteRowSideFullHecke.ComplexSets.ManifoldZerosComplementConnected.isPreconnected_convex_inter_ne_zero isOpen_univ convex_univ (AnalyticOnNhd.eval_continuousLinearMap (ContinuousLinearMap.id ℂ (Fin d → ℂ)) Q)`. Simplify using `using h`.
-/
theorem UnbranchedPartConnected.isPreconnected_ne_zero {d : ℕ} (Q : MvPolynomial (Fin d) ℂ) :
    IsPreconnected {y : Fin d → ℂ | eval y Q ≠ 0} := by
  have h := IndefiniteRowSideFullHecke.ComplexSets.ManifoldZerosComplementConnected.isPreconnected_convex_inter_ne_zero
    isOpen_univ convex_univ (AnalyticOnNhd.eval_continuousLinearMap (ContinuousLinearMap.id ℂ (Fin d → ℂ)) Q)
  simpa using h

/- English proof (translation)
Introduce `n d W A hW hd hA`. Take `⟨P₀, hP₀, hdc⟩` from `ComplexSets.DiscriminantCover.full n d W A hW hd hA`. Take `⟨P₁, hP₁, hpc⟩` from `hsheets n d W A hW hd hA`. Use `⟨P₁ * P₀, mul_ne_zero hP₁ hP₀, fun R hR => ?_⟩` and prove the remaining obligations. Establish `hQ' : P₁ * P₀ * R = P₁ * (P₀ * R)` using `mul_assoc _ _ _`.

Establish `hP₀y : ∀ y, eval y (P₁ * P₀ * R) ≠ 0 → eval y P₀ ≠ 0` using `fun y hy h => hy (by simp [h])`. Establish `hfin : ∀ y, eval y (P₁ * P₀ * R) ≠ 0 → (ComplexSets.fibre W A y).Finite ∧ (ComplexSets.fibre W A y).ncard = ComplexSets.projDegree W A` using `fun y hy => ⟨(hdc y (hP₀y y hy)).1, (hdc y (hP₀y y hy)).2.1⟩`. Introduce `u v hu hv hsub ⟨x₀, hx₀S, hx₀u⟩ ⟨x₁, hx₁S, hx₁v⟩`. Assume the negation of the conclusion as `hne`. Establish `hx₁u : x₁ ∉ u` using `fun h => hne ⟨x₁, hx₁S, h, hx₁v⟩`.

Establish `hclo : {x | x ∈ ComplexSets.zeroSet W ∧ eval (A *ᵥ x) (P₁ * P₀ * R) ≠ 0} ∩ u = {x | x ∈ ComplexSets.zeroSet W ∧ eval (A *ᵥ x) (P₁ * P₀ * R) ≠ 0} ∩ vᶜ`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hxS, hxu⟩`. Conclude with `⟨hxS, fun hxv => hne ⟨x, hxS, hxu, hxv⟩⟩`.

Introduce and unpack `⟨hxS, hxv⟩`. Conclude with `⟨hxS, (hsub hxS).resolve_right hxv⟩`. Take `⟨k, hk⟩` from `hcount n d (ComplexSets.projDegree W A) A (ComplexSets.zeroSet W) {y | eval y (P₁ * P₀ * R) ≠ 0} u vᶜ (isOpen_ne_fun (MvPolynomial.continuous_eval _) continuous_const) (UnbranchedPartConnected.isPreconnected_ne_zero _) (fun y hy => by`. Take `⟨h1, h2, h3⟩` from `hdc y (hP₀y y hy)`. Use `⟨h1, h2, fun x hx hxy => ?_⟩` and prove the remaining obligations.

Take `⟨U, V, g, hU, hyU, hV, hxV, hg, hgy, hAg, hZ⟩` from `h3 x ⟨hx, hxy⟩`. Conclude with `⟨U, V, g, hU, hyU, hV, hxV, hg.continuousOn, hgy, hAg, hZ⟩)`. Use `hu hv.isClosed_compl hclo`. Establish `hk'` using `hpc (P₀ * R) (mul_ne_zero hP₀ hR) u vᶜ k hu hv.isClosed_compl (by rw [← hQ']; exact hclo) (fun y hy => hk y (by rw [hQ']; exact hy))`. Establish `hsubf : ∀ y, {x | x ∈ ComplexSets.zeroSet W ∧ x ∈ u ∧ A *ᵥ x = y} ⊆ ComplexSets.fibre W A y` using `fun y x hx => ⟨hx.1, hx.2.2⟩`.

Establish `hpos : 0 < k`. Rewrite using `[← hk _ hx₀S.2]`. Conclude with `(Set.ncard_pos ((hfin _ hx₀S.2).1.subset (hsubf _))).2 ⟨x₀, hx₀S.1, hx₀u, rfl⟩`. Establish `hlt : k < ComplexSets.projDegree W A`. Rewrite using `[← hk _ hx₁S.2, ← (hfin _ hx₁S.2).2]`.

Conclude with `Set.ncard_lt_ncard ⟨hsubf _, fun h => hx₁u (h ⟨hx₁S.1, rfl⟩).2.1⟩ (hfin _ hx₁S.2).1`. Apply the tactic sequence `rcases hk' with h | h <;> omega`.
-/
theorem UnbranchedPartConnected.proof (hcount : ClopenPieceSheetCount.Statement)
    (hsheets : PrimeCoverPieceSheets.Statement) : UnbranchedPartConnected.Statement := by
  intro n d W A hW hd hA
  obtain ⟨P₀, hP₀, hdc⟩ := ComplexSets.DiscriminantCover.full n d W A hW hd hA
  obtain ⟨P₁, hP₁, hpc⟩ := hsheets n d W A hW hd hA
  refine ⟨P₁ * P₀, mul_ne_zero hP₁ hP₀, fun R hR => ?_⟩
  have hQ' : P₁ * P₀ * R = P₁ * (P₀ * R) := mul_assoc _ _ _
  have hP₀y : ∀ y, eval y (P₁ * P₀ * R) ≠ 0 → eval y P₀ ≠ 0 := fun y hy h => hy (by simp [h])
  have hfin : ∀ y, eval y (P₁ * P₀ * R) ≠ 0 → (ComplexSets.fibre W A y).Finite ∧
      (ComplexSets.fibre W A y).ncard = ComplexSets.projDegree W A :=
    fun y hy => ⟨(hdc y (hP₀y y hy)).1, (hdc y (hP₀y y hy)).2.1⟩
  intro u v hu hv hsub ⟨x₀, hx₀S, hx₀u⟩ ⟨x₁, hx₁S, hx₁v⟩
  by_contra hne
  have hx₁u : x₁ ∉ u := fun h => hne ⟨x₁, hx₁S, h, hx₁v⟩
  have hclo : {x | x ∈ ComplexSets.zeroSet W ∧ eval (A *ᵥ x) (P₁ * P₀ * R) ≠ 0} ∩ u =
      {x | x ∈ ComplexSets.zeroSet W ∧ eval (A *ᵥ x) (P₁ * P₀ * R) ≠ 0} ∩ vᶜ := by
    ext x
    constructor
    · rintro ⟨hxS, hxu⟩
      exact ⟨hxS, fun hxv => hne ⟨x, hxS, hxu, hxv⟩⟩
    · rintro ⟨hxS, hxv⟩
      exact ⟨hxS, (hsub hxS).resolve_right hxv⟩
  obtain ⟨k, hk⟩ := hcount n d (ComplexSets.projDegree W A) A (ComplexSets.zeroSet W)
    {y | eval y (P₁ * P₀ * R) ≠ 0} u vᶜ
    (isOpen_ne_fun (MvPolynomial.continuous_eval _) continuous_const)
    (UnbranchedPartConnected.isPreconnected_ne_zero _)
    (fun y hy => by
      obtain ⟨h1, h2, h3⟩ := hdc y (hP₀y y hy)
      refine ⟨h1, h2, fun x hx hxy => ?_⟩
      obtain ⟨U, V, g, hU, hyU, hV, hxV, hg, hgy, hAg, hZ⟩ := h3 x ⟨hx, hxy⟩
      exact ⟨U, V, g, hU, hyU, hV, hxV, hg.continuousOn, hgy, hAg, hZ⟩)
    hu hv.isClosed_compl hclo
  have hk' := hpc (P₀ * R) (mul_ne_zero hP₀ hR) u vᶜ k hu hv.isClosed_compl
    (by rw [← hQ']; exact hclo) (fun y hy => hk y (by rw [hQ']; exact hy))
  have hsubf : ∀ y, {x | x ∈ ComplexSets.zeroSet W ∧ x ∈ u ∧ A *ᵥ x = y} ⊆ ComplexSets.fibre W A y :=
    fun y x hx => ⟨hx.1, hx.2.2⟩
  have hpos : 0 < k := by
    rw [← hk _ hx₀S.2]
    exact (Set.ncard_pos ((hfin _ hx₀S.2).1.subset (hsubf _))).2 ⟨x₀, hx₀S.1, hx₀u, rfl⟩
  have hlt : k < ComplexSets.projDegree W A := by
    rw [← hk _ hx₁S.2, ← (hfin _ hx₁S.2).2]
    exact Set.ncard_lt_ncard ⟨hsubf _, fun h => hx₁u (h ⟨hx₁S.1, rfl⟩).2.1⟩ (hfin _ hx₁S.2).1
  rcases hk' with h | h <;> omega

end GroundTheory.Heights₂.Heights.HilbertSamuel
