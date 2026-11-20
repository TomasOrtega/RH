import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.CuspFinDeriv

variable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)

def cExp (t : ℝ) : GL (Fin a) (Cinf E) :=
  Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (t : ℂ))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem splitCentre_eq_infGL (t : ℝ) : GlobalTheory.UnitaryBC.splitCentre E a t = infGL E a (cExp E a t) := rfl

/- English proof (translation)
Establish `h1 : (GlobalTheory.CuspRep.expU fun _ : InfinitePlace E => ((0 : ℝ) : ℂ)) = 1`. Apply `Units.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `v`. Simplify using `[GlobalTheory.CuspRep.expU]`. Unfold `cExp`.

Rewrite using `[h1, map_one]`.
-/
theorem cExp_zero : cExp E a 0 = 1 := by
  have h1 : (GlobalTheory.CuspRep.expU fun _ : InfinitePlace E => ((0 : ℝ) : ℂ)) = 1 := by
    apply Units.ext
    funext v
    simp [GlobalTheory.CuspRep.expU]
  unfold cExp
  rw [h1, map_one]

/- English proof (translation)
Unfold `cExp GlobalTheory.CuspRep.toL GlobalTheory.CuspRep.oneL`. Rewrite using `[hasDerivAt_pi]`. Introduce `i`. Rewrite using `[hasDerivAt_pi]`. Introduce `j`.

Rewrite using `[hasDerivAt_pi]`. Introduce `v`. Simplify using `[GlobalTheory.CuspRep.expU, Matrix.scalar_apply, Matrix.diagonal_apply]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Establish `h` using `(Complex.hasDerivAt_exp ((0 : ℝ) : ℂ)).comp_ofReal`. Simplify using `only [Complex.ofReal_zero, Complex.exp_zero] at h`. Simplify using `using h`. Simplify `hasDerivAt_const (0 : ℝ) (0 : ℂ)` using `[hij]`.
-/
theorem hasDerivAt_cExp : HasDerivAt (fun t => toL (cExp E a t).val) (oneL E a) 0 := by
  unfold cExp GlobalTheory.CuspRep.toL GlobalTheory.CuspRep.oneL
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  rw [hasDerivAt_pi]
  intro v
  simp [GlobalTheory.CuspRep.expU, Matrix.scalar_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    have h := (Complex.hasDerivAt_exp ((0 : ℝ) : ℂ)).comp_ofReal
    simp only [Complex.ofReal_zero, Complex.exp_zero] at h
    simpa using h
  · simpa [hij] using hasDerivAt_const (0 : ℝ) (0 : ℂ)

/- English proof (translation)
Introduce `E _ _ _ a φ g s`. Establish `hφ` using `φ.2`. Unfold `GlobalTheory.CuspRep.Sm at hφ`. Establish `hc` using `hφ (g * GlobalTheory.UnitaryBC.splitCentre E a s)`. Establish `hopen : IsOpen (GlobalTheory.CuspRep.invSet E a)`.

Unfold `GlobalTheory.CuspRep.invSet`. Establish `hdet : Continuous fun x : GlobalTheory.CuspRep.Lie E a => (Matrix.of x).det` using `(continuous_id.comp continuous_id).matrix_det`. Establish `h3` using `Units.isOpen.preimage hdet`. Simplify `h3` using `[Matrix.isUnit_iff_isUnit_det]`. Establish `hmem : GlobalTheory.CuspRep.oneL E a ∈ GlobalTheory.CuspRep.invSet E a`.

Unfold `GlobalTheory.CuspRep.invSet GlobalTheory.CuspRep.oneL GlobalTheory.CuspRep.toL`. Simplify using the standard rewrite rules. Establish `hdiff : DifferentiableAt ℝ (GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s)) (GlobalTheory.CuspRep.oneL E a)` using `(hc.differentiableOn (by simp)).differentiableAt (hopen.mem_nhds hmem)`. Establish `hγ0 : GlobalTheory.CuspRep.toL (cExp E a 0).val = GlobalTheory.CuspRep.oneL E a`. Rewrite using `[cExp_zero]`.

Both sides reduce to the same expression. Establish `hl : HasFDerivAt (GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s)) (fderiv ℝ (GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s)) (GlobalTheory.CuspRep.oneL E a)) (GlobalTheory.CuspRep.toL (cExp E a 0).val)`. Rewrite using `[hγ0]`. Conclude with `hdiff.hasFDerivAt`. Establish `hcomp` using `hl.comp_hasDerivAt (0 : ℝ) (hasDerivAt_cExp E a)`.

Establish `hadd : ∀ s t : ℝ, GlobalTheory.UnitaryBC.splitCentre E a (s + t) = GlobalTheory.UnitaryBC.splitCentre E a s * GlobalTheory.UnitaryBC.splitCentre E a t`. Introduce `s t`. Rewrite using `[splitCentre_eq_infGL, splitCentre_eq_infGL, splitCentre_eq_infGL, ← map_mul]`. Use `congr 1`. Unfold `cExp`.

Rewrite using `[← map_mul]`. Use `congr 1`. Apply `Units.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `v`. Simplify using `[GlobalTheory.CuspRep.expU, Complex.exp_add]`.

Establish `hval : ∀ t : ℝ, GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s) (GlobalTheory.CuspRep.toL (cExp E a t).val) = (φ : GlobalTheory.CuspRep.GA E a → ℂ) (g * GlobalTheory.UnitaryBC.splitCentre E a (s + t))`. Introduce `t`. Unfold `GlobalTheory.CuspRep.chart GlobalTheory.CuspRep.toL`. Establish `hu : IsUnit (Matrix.of (Matrix.of.symm (cExp E a t).val))` using `by simp`. Rewrite using `[dif_pos hu]`.

Establish `hunit : hu.unit = cExp E a t` using `Units.ext (by simp)`. Rewrite using `[hunit, ← splitCentre_eq_infGL, hadd, mul_assoc]`. Establish `hF : HasDerivAt (fun t : ℝ => (φ : GlobalTheory.CuspRep.GA E a → ℂ) (g * GlobalTheory.UnitaryBC.splitCentre E a (s + t))) (fderiv ℝ (GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s)) (GlobalTheory.CuspRep.oneL E a) (GlobalTheory.CuspRep.oneL E a)) (s …`. Rewrite using `[sub_self]`. Establish `h5 : (GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s) ∘ fun t => GlobalTheory.CuspRep.toL (cExp E a t).val) = fun t : ℝ => (φ : GlobalTheory.CuspRep.GA E a → ℂ) (g * GlobalTheory.UnitaryBC.splitCentre E a (s + t))` using `funext hval`.

Rewrite using `[← h5]`. Conclude with `hcomp`. Establish `hF2` using `HasDerivAt.comp_sub_const s s hF`. Establish `h6 : (fun x : ℝ => (φ : GlobalTheory.CuspRep.GA E a → ℂ) (g * GlobalTheory.UnitaryBC.splitCentre E a (s + (x - s)))) = fun x : ℝ => (φ : GlobalTheory.CuspRep.GA E a → ℂ) (g * GlobalTheory.UnitaryBC.splitCentre E a x)`. Use function extensionality and compare the values at `x`.

Rewrite using `[show s + (x - s) = x by ring]`. Rewrite `hF2` using `[h6]`. Conclude with `hF2`.
-/
theorem hasDerivAt_splitCentre : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (g : GA E a) (s : ℝ),
    HasDerivAt (fun s : ℝ => φ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a s))
      ((lie E a (oneL E a) φ).1 (g * GlobalTheory.UnitaryBC.splitCentre E a s)) s := by
  intro E _ _ _ a φ g s
  have hφ := φ.2
  unfold GlobalTheory.CuspRep.Sm at hφ
  have hc := hφ (g * GlobalTheory.UnitaryBC.splitCentre E a s)
  have hopen : IsOpen (GlobalTheory.CuspRep.invSet E a) := by
    unfold GlobalTheory.CuspRep.invSet
    have hdet : Continuous fun x : GlobalTheory.CuspRep.Lie E a => (Matrix.of x).det :=
      (continuous_id.comp continuous_id).matrix_det
    have h3 := Units.isOpen.preimage hdet
    simpa [Matrix.isUnit_iff_isUnit_det] using h3
  have hmem : GlobalTheory.CuspRep.oneL E a ∈ GlobalTheory.CuspRep.invSet E a := by
    unfold GlobalTheory.CuspRep.invSet GlobalTheory.CuspRep.oneL GlobalTheory.CuspRep.toL
    simp
  have hdiff : DifferentiableAt ℝ (GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s))
      (GlobalTheory.CuspRep.oneL E a) :=
    (hc.differentiableOn (by simp)).differentiableAt (hopen.mem_nhds hmem)
  have hγ0 : GlobalTheory.CuspRep.toL (cExp E a 0).val = GlobalTheory.CuspRep.oneL E a := by
    rw [cExp_zero]
    rfl
  have hl : HasFDerivAt (GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s))
      (fderiv ℝ (GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s)) (GlobalTheory.CuspRep.oneL E a))
      (GlobalTheory.CuspRep.toL (cExp E a 0).val) := by
    rw [hγ0]
    exact hdiff.hasFDerivAt
  have hcomp := hl.comp_hasDerivAt (0 : ℝ) (hasDerivAt_cExp E a)
  have hadd : ∀ s t : ℝ, GlobalTheory.UnitaryBC.splitCentre E a (s + t) =
      GlobalTheory.UnitaryBC.splitCentre E a s * GlobalTheory.UnitaryBC.splitCentre E a t := by
    intro s t
    rw [splitCentre_eq_infGL, splitCentre_eq_infGL, splitCentre_eq_infGL, ← map_mul]
    congr 1
    unfold cExp
    rw [← map_mul]
    congr 1
    apply Units.ext
    funext v
    simp [GlobalTheory.CuspRep.expU, Complex.exp_add]
  have hval : ∀ t : ℝ, GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s)
      (GlobalTheory.CuspRep.toL (cExp E a t).val) = (φ : GlobalTheory.CuspRep.GA E a → ℂ) (g * GlobalTheory.UnitaryBC.splitCentre E a (s + t)) := by
    intro t
    unfold GlobalTheory.CuspRep.chart GlobalTheory.CuspRep.toL
    have hu : IsUnit (Matrix.of (Matrix.of.symm (cExp E a t).val)) := by simp
    rw [dif_pos hu]
    have hunit : hu.unit = cExp E a t := Units.ext (by simp)
    rw [hunit, ← splitCentre_eq_infGL, hadd, mul_assoc]
  have hF : HasDerivAt (fun t : ℝ => (φ : GlobalTheory.CuspRep.GA E a → ℂ) (g * GlobalTheory.UnitaryBC.splitCentre E a (s + t)))
      (fderiv ℝ (GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s)) (GlobalTheory.CuspRep.oneL E a)
        (GlobalTheory.CuspRep.oneL E a)) (s - s) := by
    rw [sub_self]
    have h5 : (GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s) ∘ fun t => GlobalTheory.CuspRep.toL (cExp E a t).val) =
        fun t : ℝ => (φ : GlobalTheory.CuspRep.GA E a → ℂ) (g * GlobalTheory.UnitaryBC.splitCentre E a (s + t)) := funext hval
    rw [← h5]
    exact hcomp
  have hF2 := HasDerivAt.comp_sub_const s s hF
  have h6 : (fun x : ℝ => (φ : GlobalTheory.CuspRep.GA E a → ℂ) (g * GlobalTheory.UnitaryBC.splitCentre E a (s + (x - s)))) =
      fun x : ℝ => (φ : GlobalTheory.CuspRep.GA E a → ℂ) (g * GlobalTheory.UnitaryBC.splitCentre E a x) := by
    funext x
    rw [show s + (x - s) = x by ring]
  rw [h6] at hF2
  exact hF2

end GlobalTheory.CompanionTheory.CuspFinDeriv

end
