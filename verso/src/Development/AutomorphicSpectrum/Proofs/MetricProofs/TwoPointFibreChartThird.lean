import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseChartFlagAnalyticMapStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothMinorOfSmoothMatrix
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJEqSubmatrix
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.GramPlane

/- English proof (translation)
Establish `hA' : ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => A w r s) Un` using `fun r s => ((hA r s).contDiffOn hUn.uniqueDiffOn).restrict_scalars ℝ`. Establish `hAc : ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => star (A w r s)) Un` using `fun r s => by first`. Consider the case `exact ContDiffOn.star (hA' r s)`. Consider the case `exact (Complex.conjCLE.contDiff.comp_contDiffOn (hA' r s))`. Consider the case `(have h := Complex.conjCLE.contDiff.comp_contDiffOn (hA' r s)`.

Simplify `h)` using `[Function.comp_def]`. Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply]`. Use `ContDiffOn.sum fun k _ => ?_` and prove the remaining obligations. Use `ContDiffOn.mul ?_ (hA' k s)` and prove the remaining obligations. Use `ContDiffOn.sum fun i _ => ?_` and prove the remaining obligations.

Conclude with `(hAc i r).mul (hG i k)`.
-/
theorem contDiffOn_conj_mul_mul {e N : ℕ} {Un : Set (Fin e → ℂ)} (hUn : IsOpen Un) (A G : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (hA : ∀ r s, AnalyticOnNhd ℂ (fun w => A w r s) Un)
    (hG : ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => G w r s) Un) (r s : Fin N) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => ((A w)ᴴ * G w * A w) r s) Un := by
  have hA' : ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => A w r s) Un := fun r s =>
    ((hA r s).contDiffOn hUn.uniqueDiffOn).restrict_scalars ℝ
  have hAc : ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => star (A w r s)) Un := fun r s => by
    first
      | exact ContDiffOn.star (hA' r s)
      | exact (Complex.conjCLE.contDiff.comp_contDiffOn (hA' r s))
      | (have h := Complex.conjCLE.contDiff.comp_contDiffOn (hA' r s)
         simpa [Function.comp_def] using h)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  refine ContDiffOn.sum fun k _ => ?_
  refine ContDiffOn.mul ?_ (hA' k s)
  refine ContDiffOn.sum fun i _ => ?_
  exact (hAc i r).mul (hG i k)

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.GramPlane

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

/- English proof (translation)
Introduce `K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b ca cb _ _ _ _ X q Un Gn ΦYn ΦWn l H bp hUn hF r s`. Take `⟨hH, hbp, hch, hO, hGn, -, -⟩` from `hF`. Establish `hGs : ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => BM.G l τ (bp w) r s) Un` using `GlobalTheory.T.base_chart_flag_analytic_map K ι Φ y Ψ N j M n d BM l τ Un bp hUn hbp hch (fun w hw => (hO w hw).1)`. Establish `hMs : ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => ((H τ w)ᴴ * BM.G l τ (bp w) * H τ w) r s) Un` using `GramPlane.contDiffOn_conj_mul_mul hUn (H τ) (fun w => BM.G l τ (bp w)) (hH τ) hGs`. Establish `hnum` using `MinorSmooth.contDiffOn_minorIJ N d Un (fun w => (H τ w)ᴴ * BM.G l τ (bp w) * H τ w) (insert (![ca, cb] r) ((stepCols N j a).erase ca)) (insert (![ca, cb] s) ((stepCols N j a).erase ca)) hMs`.

Establish `hden` using `MinorSmooth.contDiffOn_minorIJ N d Un (fun w => (H τ w)ᴴ * BM.G l τ (bp w) * H τ w) ((stepCols N j a).erase ca) ((stepCols N j a).erase ca) hMs`. Establish `hne : ∀ w ∈ Un, minorIJ ((H τ w)ᴴ * BM.G l τ (bp w) * H τ w) ((stepCols N j a).erase ca) ((stepCols N j a).erase ca) ≠ 0`. Introduce `w hw`. Establish `hGp` using `(BM.G_pos l τ (bp w) (hO w hw).1).2`. Establish `hdet` using `((hO w hw).2 τ).2`.

Establish `hinj : Function.Injective (H τ w).mulVec`. Rewrite using `[Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det]`. Conclude with `isUnit_iff_ne_zero.mpr hdet`. Conclude with `(SchurCalc.minor_pos (hGp.conjTranspose_mul_mul_same hinj) _).ne'`. Establish `hq` using `hnum.mul (hden.inv hne)`.

Use `hq.congr fun w hw => ?_` and prove the remaining obligations. Establish `e` using `hGn w hw r s`. Use `clear * - e`. Simplify using `only [e, div_eq_mul_inv, Pi.inv_apply]`.
-/
theorem contDiffOn_gram_plane : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => Gn w r s) Un := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b ca cb _ _ _ _ X q Un Gn ΦYn ΦWn l H bp hUn hF r s
  obtain ⟨hH, hbp, hch, hO, hGn, -, -⟩ := hF
  have hGs : ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => BM.G l τ (bp w) r s) Un :=
    GlobalTheory.T.base_chart_flag_analytic_map K ι Φ y Ψ N j M n d BM l τ Un bp hUn hbp hch (fun w hw => (hO w hw).1)
  have hMs : ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => ((H τ w)ᴴ * BM.G l τ (bp w) * H τ w) r s) Un :=
    GramPlane.contDiffOn_conj_mul_mul hUn (H τ) (fun w => BM.G l τ (bp w)) (hH τ) hGs
  have hnum := MinorSmooth.contDiffOn_minorIJ N d Un (fun w => (H τ w)ᴴ * BM.G l τ (bp w) * H τ w)
    (insert (![ca, cb] r) ((stepCols N j a).erase ca)) (insert (![ca, cb] s) ((stepCols N j a).erase ca)) hMs
  have hden := MinorSmooth.contDiffOn_minorIJ N d Un (fun w => (H τ w)ᴴ * BM.G l τ (bp w) * H τ w)
    ((stepCols N j a).erase ca) ((stepCols N j a).erase ca) hMs
  have hne : ∀ w ∈ Un, minorIJ ((H τ w)ᴴ * BM.G l τ (bp w) * H τ w)
      ((stepCols N j a).erase ca) ((stepCols N j a).erase ca) ≠ 0 := by
    intro w hw
    have hGp := (BM.G_pos l τ (bp w) (hO w hw).1).2
    have hdet := ((hO w hw).2 τ).2
    have hinj : Function.Injective (H τ w).mulVec := by
      rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det]
      exact isUnit_iff_ne_zero.mpr hdet
    exact (SchurCalc.minor_pos (hGp.conjTranspose_mul_mul_same hinj) _).ne'
  have hq := hnum.mul (hden.inv hne)
  refine hq.congr fun w hw => ?_
  have e := hGn w hw r s
  clear * - e
  simp only [e, div_eq_mul_inv, Pi.inv_apply]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
