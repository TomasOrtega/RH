import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SiegelOfRiemann
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SymplecticPolydiscPeriodBasis

open Matrix Metric GroundTheory.Heights₂.Heights.Regular GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
Introduce `n a g Λ _ L`. Take `⟨bas, Q, A, T0, hsym, hAd, hdet, -, -, hAP, hQP⟩` from `exists_markedPeriods_frame n a g Λ L`. Use `⟨Q, A, hAd, hdet, fun w hw => ?_⟩` and prove the remaining obligations. Set `Am : Matrix (Fin g) (Fin g) ℂ` to `Matrix.of fun i => L.P w (bas (.inl i))`. Set `Bm : Matrix (Fin g) (Fin g) ℂ` to `Matrix.of fun i => L.P w (bas (.inr i))`.

Establish `hAm : Am = A (expCover a w)`. Use extensionality with `i k`. Conclude with `hAP w hw i k`. Take `⟨h1, -, -, h4⟩` from `siegel_of_riemann g Am Bm (L.H (expCover a w)) (L.herm w hw) (L.pos w hw) (fun i j => ⟨(L.im w hw (bas (.inl i)) (bas (.inl j))).trans (by simp [(hsym i j).1]), (L.im w hw (bas (.inr i)) (bas (.inr j))).trans (by simp [(hsym i j).2.1]), (L.im w hw (bas (.inl i)) (bas (.inr j))).t …`. Apply the tactic sequence `rw [(hsym i j).2.2]; split_ifs <;> simp)⟩)`.

Establish `hB : Bm = Q.τ w * Am`. Use extensionality with `j k`. Establish `h` using `congrFun (hQP w hw j) k`. Rewrite `h` using `[Finset.sum_apply]`. Simplify `h` using `[Am, Bm, Matrix.mul_apply]`.

Establish `hτ : Bm * Am⁻¹ = Q.τ w`. Rewrite using `[hB, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h1), Matrix.mul_one]`. Rewrite using `[← hAm, h4, hτ]`.
-/
theorem exists_periodPolydisc_frame : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : LogPeriods n a g Λ), ∃ (Q : PeriodPolydisc n a g) (A : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ i j, DifferentiableOn ℂ (fun z => A z i j) (ball 0 1)) ∧ (A 0).det ≠ 0 ∧ ∀ w ∈ logCover L.a_le, A (expCover a w) * L.H (expCover a w) * (A (expCover a w))ᴴ = (((Q.τ w).map Complex.im)⁻¹).map Complex.ofReal := by
  intro n a g Λ _ L
  obtain ⟨bas, Q, A, T0, hsym, hAd, hdet, -, -, hAP, hQP⟩ := exists_markedPeriods_frame n a g Λ L
  refine ⟨Q, A, hAd, hdet, fun w hw => ?_⟩
  let Am : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i => L.P w (bas (.inl i))
  let Bm : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i => L.P w (bas (.inr i))
  have hAm : Am = A (expCover a w) := by
    ext i k
    exact hAP w hw i k
  obtain ⟨h1, -, -, h4⟩ := siegel_of_riemann g Am Bm (L.H (expCover a w)) (L.herm w hw)
    (L.pos w hw) (fun i j => ⟨(L.im w hw (bas (.inl i)) (bas (.inl j))).trans (by simp [(hsym i j).1]),
      (L.im w hw (bas (.inr i)) (bas (.inr j))).trans (by simp [(hsym i j).2.1]),
      (L.im w hw (bas (.inl i)) (bas (.inr j))).trans (by
        rw [(hsym i j).2.2]; split_ifs <;> simp)⟩)
  have hB : Bm = Q.τ w * Am := by
    ext j k
    have h := congrFun (hQP w hw j) k
    rw [Finset.sum_apply] at h
    simpa [Am, Bm, Matrix.mul_apply] using h
  have hτ : Bm * Am⁻¹ = Q.τ w := by
    rw [hB, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h1), Matrix.mul_one]
  rw [← hAm, h4, hτ]

end GlobalTheory.CompanionTheory.Ar.Flat
