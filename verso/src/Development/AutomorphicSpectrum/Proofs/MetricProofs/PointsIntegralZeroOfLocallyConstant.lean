import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPieceDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwistIntersection

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

/- English proof (translation)
Establish `pair : ∀ T : Finset (Fin D), j ∉ T → (-1 : ℂ) ^ (D - T.card) * (∑ k ∈ T, A k).det + (-1 : ℂ) ^ (D - (insert j T).card) * (∑ k ∈ insert j T, A k).det = 0`. Introduce `T hj`. Rewrite using `[Finset.sum_insert hj, hA, zero_add, Finset.card_insert_of_notMem hj]`. Establish `hlt : T.card < D` using `by simpa using Finset.card_lt_univ_of_notMem hj`. Take `⟨m, hm⟩ : ∃ m, D - T.card = m + 1` from `⟨D - T.card - 1, by omega⟩`.

Establish `hm' : D - (T.card + 1) = m` using `by omega`. Rewrite using `[hm, hm', pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Unfold `mixedDisc`. Rewrite using `[Finset.sum_involution (fun S _ => if j ∈ S then S.erase j else insert j S), mul_zero]`.

Introduce `S _ split_ifs with h`. Use `pair (S.erase j) (Finset.notMem_erase j S)` as an intermediate fact. Rewrite `this` using `[Finset.insert_erase h]`. Rewrite using `[add_comm]`. Conclude with `this`.

Conclude with `pair S h`. Introduce `S _ _ split_ifs with h`. Introduce `e`. Establish `hmem : j ∈ S.erase j`. Rewrite using `[e]`.

Conclude with `h`. Conclude with `Finset.notMem_erase j S hmem`. Conclude with `fun e => h (e ▸ Finset.mem_insert_self j S)`. Introduce `S _`. Conclude with `Finset.mem_univ _`.

Introduce `S _`. Distinguish the cases in `h : j ∈ S`. Simplify using `[h, Finset.insert_erase]`. Simplify using `[h, Finset.erase_insert]`.
-/
theorem mixedDisc_eq_zero_of_eq_zero {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (j : Fin D)
    (hA : A j = 0) : mixedDisc A = 0 := by
  classical
  have pair : ∀ T : Finset (Fin D), j ∉ T →
      (-1 : ℂ) ^ (D - T.card) * (∑ k ∈ T, A k).det +
        (-1 : ℂ) ^ (D - (insert j T).card) * (∑ k ∈ insert j T, A k).det = 0 := by
    intro T hj
    rw [Finset.sum_insert hj, hA, zero_add, Finset.card_insert_of_notMem hj]
    have hlt : T.card < D := by simpa using Finset.card_lt_univ_of_notMem hj
    obtain ⟨m, hm⟩ : ∃ m, D - T.card = m + 1 := ⟨D - T.card - 1, by omega⟩
    have hm' : D - (T.card + 1) = m := by omega
    rw [hm, hm', pow_succ]
    ring
  unfold mixedDisc
  rw [Finset.sum_involution (fun S _ => if j ∈ S then S.erase j else insert j S), mul_zero]
  · intro S _
    split_ifs with h
    · have := pair (S.erase j) (Finset.notMem_erase j S)
      rw [Finset.insert_erase h] at this
      rw [add_comm]
      exact this
    · exact pair S h
  · intro S _ _
    split_ifs with h
    · intro e
      have hmem : j ∈ S.erase j := by
        rw [e]
        exact h
      exact Finset.notMem_erase j S hmem
    · exact fun e => h (e ▸ Finset.mem_insert_self j S)
  · intro S _
    exact Finset.mem_univ _
  · intro S _
    by_cases h : j ∈ S
    · simp [h, Finset.insert_erase]
    · simp [h, Finset.erase_insert]

/- English proof (translation)
Establish `h : fderiv ℝ (fderiv ℝ (fun _ : Fin D → ℂ => (0 : ℝ))) z = 0`. Establish `h1 : fderiv ℝ (fun _ : Fin D → ℂ => (0 : ℝ)) = fun _ => 0`. Use function extensionality and compare the values at `x`. Conclude with `fderiv_const_apply 0`. Rewrite using `[h1]`.

Conclude with `fderiv_const_apply 0`. Use extensionality with `a b`. Simplify using `[cxHessian, h]`.
-/
theorem cxHessian_zero {D : ℕ} (z : Fin D → ℂ) : cxHessian (fun _ => (0 : ℝ)) z = 0 := by
  have h : fderiv ℝ (fderiv ℝ (fun _ : Fin D → ℂ => (0 : ℝ))) z = 0 := by
    have h1 : fderiv ℝ (fun _ : Fin D → ℂ => (0 : ℝ)) = fun _ => 0 := by
      funext x
      exact fderiv_const_apply 0
    rw [h1]
    exact fderiv_const_apply 0
  ext a b
  simp [cxHessian, h]

/- English proof (translation)
Unfold `sheetDensity`. Use `split_ifs with hγ`. Establish `hm : mixedDisc (fun k => cxHessian (fun y' => Function.update φ j 0 k (hγ.choose y')) y) = 0`. Use `mixedDisc_eq_zero_of_eq_zero _ j ?_` and prove the remaining obligations. Simplify using `using cxHessian_zero y`.

Simplify using `[maDensity, hm]`. Both sides reduce to the same expression.
-/
theorem sheetDensity_update_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (j : Fin e)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ (Function.update φ j 0) g y w = 0 := by
  unfold sheetDensity
  split_ifs with hγ
  · have hm : mixedDisc (fun k => cxHessian
        (fun y' => Function.update φ j 0 k (hγ.choose y')) y) = 0 := by
      refine mixedDisc_eq_zero_of_eq_zero _ j ?_
      simpa using cxHessian_zero y
    simp [maDensity, hm]
  · rfl

/- English proof (translation)
Introduce `K _ ι _ P e φ g j hj`. Establish `hshift : ∀ i, ∀ z ∈ mcPts P, ∃ c : ℝ, ∀ᶠ u in 𝓝 z, φ i u = Function.update φ j 0 i u + c`. Introduce `i z hz`. Distinguish the cases in `hi : i = j`. Substitute `hi` using the available equality.

Take `⟨c, hc⟩` from `hj z hz`. Use `⟨c, hc.mono fun u hu => ?_⟩` and prove the remaining obligations. Simplify using `using hu`. Conclude with `⟨0, Eventually.of_forall fun u => by simp [Function.update_of_ne hi]⟩`. Rewrite using `[GroundTheory.Heights₂.Heights.HilbertSamuel.TwistIntersection.ptsIntegral_add_locConst P hshift g]`.

Unfold `ptsIntegral`. Use `split_ifs`. Simplify using `[ptsIntegralAt, sheetDensity_update_zero]`. Both sides reduce to the same expression.
-/
theorem ptsIntegral_eq_zero_of_locConst :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
      (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (j : Fin e),
      (∀ z ∈ mcPts P, ∃ c : ℝ, φ j =ᶠ[𝓝 z] fun _ => c) → ptsIntegral P φ g = 0 := by
  intro K _ ι _ P e φ g j hj
  have hshift : ∀ i, ∀ z ∈ mcPts P, ∃ c : ℝ,
      ∀ᶠ u in 𝓝 z, φ i u = Function.update φ j 0 i u + c := by
    intro i z hz
    by_cases hi : i = j
    · subst hi
      obtain ⟨c, hc⟩ := hj z hz
      refine ⟨c, hc.mono fun u hu => ?_⟩
      simpa using hu
    · exact ⟨0, Eventually.of_forall fun u => by simp [Function.update_of_ne hi]⟩
  rw [GroundTheory.Heights₂.Heights.HilbertSamuel.TwistIntersection.ptsIntegral_add_locConst P hshift g]
  unfold ptsIntegral
  split_ifs
  · simp [ptsIntegralAt, sheetDensity_update_zero]
  · rfl

end GlobalTheory.CompanionTheory.Ar.Giv
