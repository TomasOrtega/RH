import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SmoothTranslationMeasure.Development

open Matrix
open scoped ContDiff

noncomputable section

namespace PI.PhMeasCore.UnitaryGroupMassFormula

open PI.PhMeasCore

/- English proof (translation)
Establish `ha' : aᴴ * Hm * a = Hm` using `ha`. Establish `hb' : bᴴ * Hm * b = Hm` using `hb`. Use `show (a * b)ᴴ * Hm * (a * b) = Hm`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`.

Use `_ = Hm := by rw [ha', hb']`.
-/
theorem mul_mem_UH {n : ℕ} {Hm a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ UH Hm) (hb : b ∈ UH Hm) :
    a * b ∈ UH Hm := by
  have ha' : aᴴ * Hm * a = Hm := ha
  have hb' : bᴴ * Hm * b = Hm := hb
  show (a * b)ᴴ * Hm * (a * b) = Hm
  calc (a * b)ᴴ * Hm * (a * b) = bᴴ * (aᴴ * Hm * a) * b := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Hm := by rw [ha', hb']

section Smooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Set `L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ` to `LinearMap.toContinuousLinearMap { toFun := fun a => LinearMap.toContinuousLinearMap { toFun := fun b => a * b map_add' := fun b c => Matrix.mul_add a b c map_smul' := fun r b => by simp } map_add' := fun a b => by`. Use extensionality with `c : 1`. Simplify using `[Matrix.add_mul]`. Use the proof step `map_smul' := fun r a => by`. Use extensionality with `c : 1`.

Simplify using `}`. Establish `h : ContDiff ℝ ∞ (fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => L p.1 p.2)` using `L.isBoundedBilinearMap.contDiff`. Conclude with `h`.
-/
theorem contDiff_matMul {n : ℕ} :
    ContDiff ℝ ∞ (fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => p.1 * p.2) := by
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun a => LinearMap.toContinuousLinearMap
          { toFun := fun b => a * b
            map_add' := fun b c => Matrix.mul_add a b c
            map_smul' := fun r b => by simp }
        map_add' := fun a b => by
          ext c : 1
          simp [Matrix.add_mul]
        map_smul' := fun r a => by
          ext c : 1
          simp }
  have h : ContDiff ℝ ∞ (fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => L p.1 p.2) :=
    L.isBoundedBilinearMap.contDiff
  exact h

/- English proof (translation)
The claim follows from `(@contDiff_matMul n).comp (contDiff_id.prodMk contDiff_const)`.
-/
theorem contDiff_mulRight {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ (fun x : Matrix (Fin n) (Fin n) ℂ => x * g) :=
  (@contDiff_matMul n).comp (contDiff_id.prodMk contDiff_const)

end Smooth

end PI.PhMeasCore.UnitaryGroupMassFormula

end
