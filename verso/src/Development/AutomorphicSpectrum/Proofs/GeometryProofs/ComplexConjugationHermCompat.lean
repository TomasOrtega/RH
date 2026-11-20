import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

section Basic

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem conjPt_conjPt (z : (Σ k, ι k) → ℂ) : conjPt (conjPt z) = z := by
  funext p
  simp [conjPt]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Treat this case separately. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem evC_conjPt (z : (Σ k, ι k) → ℂ) (f : MRing ι) :
    evC (conjPt z) f = starRingEnd ℂ (evC z f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [evC]
  | add p q hp hq =>
    simp only [evC, map_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p i hp =>
    simp only [evC, map_mul, map_X, eval_X] at hp ⊢
    rw [hp]
    simp [conjPt]

def conjCLM : ((Σ k, ι k) → ℂ) →L[ℝ] ((Σ k, ι k) → ℂ) :=
  ContinuousLinearMap.pi fun p =>
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : (Σ k, ι k) => ℂ) p)

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem conjCLM_apply (z : (Σ k, ι k) → ℂ) : conjCLM z = conjPt z := by
  funext p
  simp [conjCLM, conjPt]

/- English proof (translation)
Establish an intermediate fact. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts.
-/
theorem conjPt_mem_mcPts_iff (P : Ideal (MRing ι)) (z : (Σ k, ι k) → ℂ) :
    conjPt z ∈ mcPts P ↔ z ∈ mcPts P := by
  have key : ∀ w : (Σ k, ι k) → ℂ, w ∈ mcPts P → conjPt w ∈ mcPts P := by
    rintro w ⟨h1, h2⟩
    refine ⟨fun k => ?_, fun f hf => ?_⟩
    · obtain ⟨i, hi⟩ := h1 k
      exact ⟨i, by simpa [conjPt] using hi⟩
    · have := evC_conjPt w f
      simp only [evC] at this
      rw [this, h2 f hf, map_zero]
  refine ⟨fun h => ?_, key z⟩
  simpa [conjPt_conjPt] using key _ h

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem conjLine_smooth (A : HermLine ι) (hA : IsSmoothHerm A) : IsSmoothHerm (conjLine A) := by
  have hc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => conjCLM z)
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := (conjCLM (ι := ι)).contDiff.contDiffOn
  have := ContDiffOn.comp (g := A.h) (f := fun z : (Σ k, ι k) → ℂ => conjCLM z)
    (s := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) (t := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) hA hc (fun z hz k => by
      obtain ⟨i, hi⟩ := hz k
      refine ⟨i, ?_⟩
      show conjCLM z ⟨k, i⟩ ≠ 0
      rw [conjCLM_apply]
      simpa [conjPt] using hi)
  unfold IsSmoothHerm
  refine this.congr fun z _ => ?_
  simp [conjLine, conjCLM_apply]

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem logNorm_conjLine (A : HermLine ι) (s : MRing ι) (z : (Σ k, ι k) → ℂ) :
    logNorm (conjLine A) s z = logNorm A s (conjPt z) := by
  have h := evC_conjPt z s
  simp only [evC] at h
  simp only [logNorm, conjLine]
  rw [h, RCLike.norm_conj]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conjLine_tensor (A B : HermLine ι) :
    conjLine (A.tensor B) = (conjLine A).tensor (conjLine B) := rfl

/- English proof (translation)
Split into cases according to the possible forms of the given data. Treat this case separately. Simplify using the standard rewrite rules. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.
-/
theorem conjLine_conjLine (A : HermLine ι) : conjLine (conjLine A) = A := by
  cases A with
  | mk a h pos smul =>
    simp only [conjLine, HermLine.mk.injEq, heq_eq_eq, true_and]
    funext z
    rw [conjPt_conjPt]

end Basic

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem conj_basic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], (∀ (P : Ideal (MRing ι)) z, conjPt z ∈ mcPts P ↔ z ∈ mcPts P) ∧ (∀ (z : (Σ k, ι k) → ℂ) f, evC (conjPt z) f = starRingEnd ℂ (evC z f)) ∧ (∀ A : HermLine ι, IsSmoothHerm A → IsSmoothHerm (conjLine A)) ∧ (∀ (A : HermLine ι) s z, logNorm (conjLine A) s z = logNorm A s (conjPt z)) ∧ (∀ A B : HermLine ι, conjLine (A.tensor B) = (conjLine A).tensor (conjLine B)) ∧ ∀ A : HermLine ι, conjLine (conjLine A) = A :=
  fun _ _ _ _ => ⟨conjPt_mem_mcPts_iff, evC_conjPt, conjLine_smooth, logNorm_conjLine, conjLine_tensor, conjLine_conjLine⟩

end GlobalTheory.CompanionTheory.Ar.Cmp
