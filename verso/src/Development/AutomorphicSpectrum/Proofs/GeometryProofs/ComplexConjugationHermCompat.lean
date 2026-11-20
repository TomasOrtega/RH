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
Use function extensionality and compare the values at `p`. Simplify using `[conjPt]`.
-/
theorem conjPt_conjPt (z : (Σ k, ι k) → ℂ) : conjPt (conjPt z) = z := by
  funext p
  simp [conjPt]

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp [evC]`. Consider the case `add p q hp hq`. Simplify using `only [evC, map_add] at hp hq ⊢`. Rewrite using `[hp, hq]`.

Consider the case `mul_X p i hp`. Simplify using `only [evC, map_mul, map_X, eval_X] at hp ⊢`. Rewrite using `[hp]`. Simplify using `[conjPt]`.
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
Use function extensionality and compare the values at `p`. Simplify using `[conjCLM, conjPt]`.
-/
theorem conjCLM_apply (z : (Σ k, ι k) → ℂ) : conjCLM z = conjPt z := by
  funext p
  simp [conjCLM, conjPt]

/- English proof (translation)
Establish `key : ∀ w : (Σ k, ι k) → ℂ, w ∈ mcPts P → conjPt w ∈ mcPts P`. Introduce and unpack `w ⟨h1, h2⟩`. Use `⟨fun k => ?_, fun f hf => ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `h1 k`. Conclude with `⟨i, by simpa [conjPt] using hi⟩`.

Use `evC_conjPt w f` as an intermediate fact. Simplify using `only [evC] at this`. Rewrite using `[this, h2 f hf, map_zero]`. Use `⟨fun h => ?_, key z⟩` and prove the remaining obligations. Simplify `key _ h` using `[conjPt_conjPt]`.
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
Establish `hc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => conjCLM z) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}` using `(conjCLM (ι := ι)).contDiff.contDiffOn`. Use `ContDiffOn.comp (g := A.h) (f := fun z : (Σ k, ι k) → ℂ => conjCLM z) (s := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) (t := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) hA hc (fun z hz k => by` as an intermediate fact. Take `⟨i, hi⟩` from `hz k`. Use `⟨i, ?_⟩` and prove the remaining obligations. Use `show conjCLM z ⟨k, i⟩ ≠ 0`.

Rewrite using `[conjCLM_apply]`. Simplify `hi)` using `[conjPt]`. Unfold `IsSmoothHerm`. Use `this.congr fun z _ => ?_` and prove the remaining obligations. Simplify using `[conjLine, conjCLM_apply]`.
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
Establish `h` using `evC_conjPt z s`. Simplify using `only [evC] at h`. Simplify using `only [logNorm, conjLine]`. Rewrite using `[h, RCLike.norm_conj]`.
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
Consider the cases of `A with`. Consider the case `mk a h pos smul`. Simplify using `only [conjLine, HermLine.mk.injEq, heq_eq_eq, true_and]`. Use function extensionality and compare the values at `z`. Rewrite using `[conjPt_conjPt]`.
-/
theorem conjLine_conjLine (A : HermLine ι) : conjLine (conjLine A) = A := by
  cases A with
  | mk a h pos smul =>
    simp only [conjLine, HermLine.mk.injEq, heq_eq_eq, true_and]
    funext z
    rw [conjPt_conjPt]

end Basic

/- English proof (translation)
Introduce `_ _ _ _` and use `⟨conjPt_mem_mcPts_iff, evC_conjPt, conjLine_smooth, logNorm_conjLine, conjLine_tensor, conjLine_conjLine⟩`.
-/
theorem conj_basic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], (∀ (P : Ideal (MRing ι)) z, conjPt z ∈ mcPts P ↔ z ∈ mcPts P) ∧ (∀ (z : (Σ k, ι k) → ℂ) f, evC (conjPt z) f = starRingEnd ℂ (evC z f)) ∧ (∀ A : HermLine ι, IsSmoothHerm A → IsSmoothHerm (conjLine A)) ∧ (∀ (A : HermLine ι) s z, logNorm (conjLine A) s z = logNorm A s (conjPt z)) ∧ (∀ A B : HermLine ι, conjLine (A.tensor B) = (conjLine A).tensor (conjLine B)) ∧ ∀ A : HermLine ι, conjLine (conjLine A) = A :=
  fun _ _ _ _ => ⟨conjPt_mem_mcPts_iff, evC_conjPt, conjLine_smooth, logNorm_conjLine, conjLine_tensor, conjLine_conjLine⟩

end GlobalTheory.CompanionTheory.Ar.Cmp
