import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.CellPotSmooth

/- English proof (translation)
Introduce `a b`. Simplify using `only [upM, upU, Matrix.of_apply, fb]`. Use `split_ifs with h1 h2`. Conclude with `((EuclideanSpace.proj (𝕜 := ℂ) (ε.symm (.inr ⟨τ, ⟨(b, a), h1⟩⟩))).contDiff.restrict_scalars ℝ).contDiffAt`. Conclude with `contDiffAt_const`.

Conclude with `contDiffAt_const`.
-/
theorem upM_fb_contDiffAt_two {ι : Type} {m : ι → ℕ} {n d : ℕ} (ε : Fin n ≃ Fin d ⊕ Cell m) (τ : ι) (w : V n) :
    MContDiffAt 2 (fun w => upM (fb ε w) τ) w := by
  intro a b
  simp only [upM, upU, Matrix.of_apply, fb]
  split_ifs with h1 h2
  · exact ((EuclideanSpace.proj (𝕜 := ℂ) (ε.symm (.inr ⟨τ, ⟨(b, a), h1⟩⟩))).contDiff.restrict_scalars ℝ).contDiffAt
  · exact contDiffAt_const
  · exact contDiffAt_const

/- English proof (translation)
Introduce `a b`. Conclude with `(hG a b).comp w (((bsL ε).contDiff.restrict_scalars ℝ).contDiffAt)`.
-/
theorem G_bsL_smooth {ι : Type} {m : ι → ℕ} {n d : ℕ} (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (w : V n) (τ : ι)
    (hG : MContDiffAt 2 (fun v => G v τ) (bsL ε w)) : MContDiffAt 2 (fun w => G (bsL ε w) τ) w := by
  intro a b
  exact (hG a b).comp w (((bsL ε).contDiff.restrict_scalars ℝ).contDiffAt)

/- English proof (translation)
Rewrite using `[Matrix.isUnit_iff_isUnit_det, upU_eq, Matrix.det_transpose, GlobalTheory.FlagFibre.det_uni]`. Conclude with `isUnit_one`.
-/
theorem upU_isUnit {s : ℕ} (y : Low s → ℂ) : IsUnit (upU y) := by
  rw [Matrix.isUnit_iff_isUnit_det, upU_eq, Matrix.det_transpose, GlobalTheory.FlagFibre.det_uni]
  exact isUnit_one

/- English proof (translation)
Establish `h` using `(hA.submatrix (Subtype.val_injective (p := fun a : Fin s => (a : ℕ) < j))).det_pos`. Conclude with `(Complex.pos_iff.1 h).1`.
-/
theorem leadMinor_re_pos {s : ℕ} {A : Matrix (Fin s) (Fin s) ℂ} (hA : A.PosDef) (j : ℕ) : 0 < (leadMinor A j).re := by
  have h := (hA.submatrix (Subtype.val_injective (p := fun a : Fin s => (a : ℕ) < j))).det_pos
  exact (Complex.pos_iff.1 h).1

/- English proof (translation)
Introduce `ι m n d ε G w x hP hG`. Use `set A : V n → Matrix (Fin (m x.1)) (Fin (m x.1)) ℂ := fun w => upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ with hAdef`. Establish `hA : MContDiffAt 2 A w` using `((upM_fb_contDiffAt_two ε x.1 w).mul (G_bsL_smooth ε G w x.1 hG)).mul (upM_fb_contDiffAt_two ε x.1 w).conjTranspose`. Establish `hPA : (A w).PosDef`. Use `hP.mul_mul_conjTranspose_same ?_` and prove the remaining obligations.

Conclude with `Matrix.vecMul_injective_iff_isUnit.2 (upU_isUnit _)`. Establish `hm : ∀ j : ℕ, ContDiffAt ℝ 2 (fun w => (leadMinor (A w) j).re) w` using `fun j => Complex.reCLM.contDiff.contDiffAt.comp w (hA.submatrix _ _).det`. Establish `h1` using `leadMinor_re_pos hPA (x.2 + 1)`. Establish `h0` using `leadMinor_re_pos hPA x.2`. Establish `hpos : 0 < grD (A w) x.2` using `div_pos h1 h0`.

Use `⟨?_, hpos⟩` and prove the remaining obligations. Establish `hd : ContDiffAt ℝ 2 (fun w => grD (A w) x.2) w` using `(hm _).div (hm _) h0.ne'`. Conclude with `(hd.log hpos.ne').neg`.
-/
theorem cellPot_contDiffAt : ∀ (ι : Type) (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (w : V n) (x : Root m), (G (bsL ε w) x.1).PosDef → MContDiffAt 2 (fun v => G v x.1) (bsL ε w) → ContDiffAt ℝ 2 (cellPot ε G x) w ∧ 0 < grD (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2 := by
  intro ι m n d ε G w x hP hG
  set A : V n → Matrix (Fin (m x.1)) (Fin (m x.1)) ℂ :=
    fun w => upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ with hAdef
  have hA : MContDiffAt 2 A w :=
    ((upM_fb_contDiffAt_two ε x.1 w).mul (G_bsL_smooth ε G w x.1 hG)).mul (upM_fb_contDiffAt_two ε x.1 w).conjTranspose
  have hPA : (A w).PosDef := by
    refine hP.mul_mul_conjTranspose_same ?_
    exact Matrix.vecMul_injective_iff_isUnit.2 (upU_isUnit _)
  have hm : ∀ j : ℕ, ContDiffAt ℝ 2 (fun w => (leadMinor (A w) j).re) w := fun j =>
    Complex.reCLM.contDiff.contDiffAt.comp w (hA.submatrix _ _).det
  have h1 := leadMinor_re_pos hPA (x.2 + 1)
  have h0 := leadMinor_re_pos hPA x.2
  have hpos : 0 < grD (A w) x.2 := div_pos h1 h0
  refine ⟨?_, hpos⟩
  have hd : ContDiffAt ℝ 2 (fun w => grD (A w) x.2) w := (hm _).div (hm _) h0.ne'
  exact (hd.log hpos.ne').neg

end GlobalTheory.CellPotSmooth
