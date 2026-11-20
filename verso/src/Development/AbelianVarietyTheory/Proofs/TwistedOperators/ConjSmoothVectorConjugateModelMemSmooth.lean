import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Adapted
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbLEqEmbOptL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjSmooth

open GlobalTheory.ConjDS

/- English proof (translation)
Establish `h1 : A * A⁻¹ = 1` using `Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).1 hA)`. Establish `h2 : A⁻¹ * A = 1` using `Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).1 hA)`. Proceed by induction on `l with`. Consider the case `nil => simp [h1]`. Consider the case `cons x l ih`.

Rewrite using `[List.map_cons, List.prod_cons, List.prod_cons, ← ih]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem conj_list_prod {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsUnit A) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    A * l.prod * A⁻¹ = (l.map fun x => A * x * A⁻¹).prod := by
  have h1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).1 hA)
  have h2 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).1 hA)
  induction l with
  | nil => simp [h1]
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ← ih]
    calc A * (x * l.prod) * A⁻¹ = A * x * (A⁻¹ * A) * l.prod * A⁻¹ := by rw [h2]; noncomm_ring
      _ = A * x * A⁻¹ * (A * l.prod * A⁻¹) := by noncomm_ring

/- English proof (translation)
Introduce `D Y S M τ w hw`. Apply `Submodule.subset_span` to reduce the goal to its premises. Introduce `k Xs hXs`. Use `set A := (conjModel M).fr τ with hAdef`. Establish `hA : IsUnit A` using `(conjModel M).fr_unit τ`.

Establish `hdet : IsUnit A.det` using `(Matrix.isUnit_iff_isUnit_det A).1 hA`. Establish `h1 : A * A⁻¹ = 1` using `Matrix.mul_nonsing_inv A hdet`. Establish `hrep : ∀ g, M.rep τ g (cj (M.H τ) w) = cj (M.H τ) ((conjModel M).σ τ (A * g * A⁻¹) w)`. Introduce `g`. Establish `e : rv ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g * ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _))⁻¹) = M.fr τ * g * (M.fr τ)⁻¹`.

Rewrite using `[inv_submatrix_equiv]`. Establish `: (M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g * (M.fr τ)⁻¹.submatrix (Equiv.refl _) Fin.revPerm = rv (M.fr τ * g * (M.fr τ)⁻¹)`. Use extensionality with `i j`. Simplify using `[rv, Matrix.mul_apply]`. Rewrite using `[this, rv_rv]`.

Use `show M.σ τ (M.fr τ * g * (M.fr τ)⁻¹) (cj (M.H τ) w) = M.σ τ (rv ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g * ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _))⁻¹)) (cj (M.H τ) w)`. Rewrite using `[e]`. Establish `hX' : ∀ i, A * Xs i * A⁻¹ ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((conjModel M).ε τ))`. Introduce `i`. Establish `hg : Aᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) * A = gramAt D Y τ` using `(conjModel M).fr_gram τ`.

Establish `hi : (Xs i)ᴴ * gramAt D Y τ + gramAt D Y τ * Xs i = 0` using `hXs i`. Establish `h3 : (A⁻¹)ᴴ * Aᴴ = 1` using `by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]`. Use `show (A * Xs i * A⁻¹)ᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) + Formalism.REAL.Jm ((conjModel M).ε τ) * (A * Xs i * A⁻¹) = 0`. Rewrite `hi` using `[← hg]`. Establish `: (A * Xs i * A⁻¹)ᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) + Formalism.REAL.Jm ((conjModel M).ε τ) * (A * Xs i * A⁻¹) = (A⁻¹)ᴴ * ((Xs i)ᴴ * (Aᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) * A) + (Aᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) * A) * Xs i) * A⁻¹`.

Simplify using `only [Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.one_mul]`. Use `noncomm_ring`. Use `_ = _ := by rw [← h3]; simp only [Matrix.mul_assoc, h1, Matrix.mul_one, Matrix.mul_add, Matrix.add_mul]`.

Rewrite using `[this, hi, Matrix.mul_zero, Matrix.zero_mul]`. Establish `hprod : ∀ t : Fin k → ℝ, A * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * A⁻¹ = (List.ofFn fun i => NormedSpace.exp (t i • (A * Xs i * A⁻¹))).prod`. Introduce `t`. Rewrite using `[conj_list_prod hA, List.map_ofFn]`. Use `congr 1`.

Use `List.ofFn_inj.2 (funext fun i => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp]`. Rewrite using `[← Matrix.exp_conj A _ hA, Matrix.mul_smul, Matrix.smul_mul]`. Establish `hc` using `hw k (fun i => A * Xs i * A⁻¹) hX'`. Set `L : Cj (M.H τ) →L[ℝ] M.H τ` to `{ toFun := cj (M.H τ) map_add' := map_add (cj (M.H τ)) map_smul' := fun r x => by`.

Rewrite using `[← Complex.coe_smul, ← Complex.coe_smul, LinearIsometryEquiv.map_smulₛₗ, Complex.conj_ofReal]`. Both sides reduce to the same expression. Use `cont := (cj (M.H τ)).continuous }`. Establish `hL` using `L.contDiff.comp hc`. Use `hL using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `t`. Simplify using `only [Function.comp]`. Rewrite using `[hrep, hprod]`. Both sides reduce to the same expression.
-/
theorem cj_mem_sm : ∀ (D : D7) (Y : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel Y S) (τ : D.what₂.Tau)
  (w : (GlobalTheory.ConjDS.conjModel M).H τ),
  GlobalTheory.Ell.SmV (GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((GlobalTheory.ConjDS.conjModel M).ε τ))) ((GlobalTheory.ConjDS.conjModel M).σ τ) w →
  GlobalTheory.ConjDS.cj (M.H τ) w ∈ M.sm τ := by
  intro D Y S M τ w hw
  apply Submodule.subset_span
  intro k Xs hXs
  set A := (conjModel M).fr τ with hAdef
  have hA : IsUnit A := (conjModel M).fr_unit τ
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA
  have h1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdet

  have hrep : ∀ g, M.rep τ g (cj (M.H τ) w) = cj (M.H τ) ((conjModel M).σ τ (A * g * A⁻¹) w) := by
    intro g
    have e : rv ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g *
        ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _))⁻¹) = M.fr τ * g * (M.fr τ)⁻¹ := by
      rw [inv_submatrix_equiv]
      have : (M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g * (M.fr τ)⁻¹.submatrix (Equiv.refl _) Fin.revPerm =
          rv (M.fr τ * g * (M.fr τ)⁻¹) := by
        ext i j
        simp [rv, Matrix.mul_apply]
      rw [this, rv_rv]
    show M.σ τ (M.fr τ * g * (M.fr τ)⁻¹) (cj (M.H τ) w) = M.σ τ (rv ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g *
        ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _))⁻¹)) (cj (M.H τ) w)
    rw [e]

  have hX' : ∀ i, A * Xs i * A⁻¹ ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((conjModel M).ε τ)) := by
    intro i
    have hg : Aᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) * A = gramAt D Y τ := (conjModel M).fr_gram τ
    have hi : (Xs i)ᴴ * gramAt D Y τ + gramAt D Y τ * Xs i = 0 := hXs i
    have h3 : (A⁻¹)ᴴ * Aᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    show (A * Xs i * A⁻¹)ᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) + Formalism.REAL.Jm ((conjModel M).ε τ) * (A * Xs i * A⁻¹) = 0
    rw [← hg] at hi
    have : (A * Xs i * A⁻¹)ᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) + Formalism.REAL.Jm ((conjModel M).ε τ) * (A * Xs i * A⁻¹) =
        (A⁻¹)ᴴ * ((Xs i)ᴴ * (Aᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) * A) + (Aᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) * A) * Xs i) * A⁻¹ := by
      simp only [Matrix.conjTranspose_mul]
      calc _ = (A⁻¹)ᴴ * (Xs i)ᴴ * Aᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) + 1 * Formalism.REAL.Jm ((conjModel M).ε τ) * (A * Xs i * A⁻¹) := by
              rw [Matrix.one_mul]; noncomm_ring
        _ = _ := by rw [← h3]; simp only [Matrix.mul_assoc, h1, Matrix.mul_one, Matrix.mul_add, Matrix.add_mul]
    rw [this, hi, Matrix.mul_zero, Matrix.zero_mul]
  have hprod : ∀ t : Fin k → ℝ, A * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * A⁻¹ =
      (List.ofFn fun i => NormedSpace.exp (t i • (A * Xs i * A⁻¹))).prod := by
    intro t
    rw [conj_list_prod hA, List.map_ofFn]
    congr 1
    refine List.ofFn_inj.2 (funext fun i => ?_)
    simp only [Function.comp]
    rw [← Matrix.exp_conj A _ hA, Matrix.mul_smul, Matrix.smul_mul]
  have hc := hw k (fun i => A * Xs i * A⁻¹) hX'
  let L : Cj (M.H τ) →L[ℝ] M.H τ :=
    { toFun := cj (M.H τ)
      map_add' := map_add (cj (M.H τ))
      map_smul' := fun r x => by
        rw [← Complex.coe_smul, ← Complex.coe_smul, LinearIsometryEquiv.map_smulₛₗ, Complex.conj_ofReal]
        rfl
      cont := (cj (M.H τ)).continuous }
  have hL := L.contDiff.comp hc
  convert hL using 1
  funext t
  simp only [Function.comp]
  rw [hrep, hprod]
  rfl

end GlobalTheory.ConjSmooth

end
