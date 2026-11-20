import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableRisingS
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory.HoloWirt

open Classical in
/- English proof (translation)
Rewrite using `[← smul_eq_mul, ← map_smul]`. Use `congr 1`. Use extensionality with `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hj]`.
-/
theorem clm_single_I {I : Type} (f : (I → ℂ) →L[ℂ] ℂ) (i : I) :
    f (Pi.single i Complex.I) = Complex.I * f (Pi.single i 1) := by
  rw [← smul_eq_mul, ← map_smul]
  congr 1
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_apply, hj]

/- English proof (translation)
Rewrite using `[hd.lineDeriv_eq_fderiv]`. Unfold `wirt`. Rewrite using `[hd.fderiv_restrictScalars ℝ]`. Simplify using `only [ContinuousLinearMap.coe_restrictScalars', Bool.false_eq_true, if_false]`. Rewrite using `[clm_single_I]`.

Establish `e : ∀ a b : ℂ, a = b → (a + -Complex.I * (Complex.I * a)) / 2 = b`. Introduce and unpack `a b rfl`. Put the polynomial expressions in normal form. Rewrite using `[Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree.

Apply `e` to reduce the goal to its premises. Reduce the equality to equality of the corresponding arguments. Conclude with `Subsingleton.elim _ _`.
-/
theorem wirt_false_eq_lineDeriv {I : Type} [Fintype I] [DecidableEq I] (i : I) (h : (I → ℂ) → ℂ) (z : I → ℂ)
    (hd : DifferentiableAt ℂ h z) : wirt i false h z = lineDeriv ℂ h z (Pi.single i 1) := by
  rw [hd.lineDeriv_eq_fderiv]
  unfold wirt
  rw [hd.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.coe_restrictScalars', Bool.false_eq_true, if_false]
  rw [clm_single_I]
  have e : ∀ a b : ℂ, a = b → (a + -Complex.I * (Complex.I * a)) / 2 = b := by
    rintro a b rfl
    ring_nf
    rw [Complex.I_sq]
    ring
  apply e
  congr
  exact Subsingleton.elim _ _

end GlobalTheory.HoloWirt

namespace GlobalTheory.HoloWirt

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact ⟨hg, fun _ _ => rfl⟩`. Consider the case `cons i l ih`. Take `⟨hd, heq⟩` from `ih`. Establish `hat : ∀ z ∈ U, DifferentiableAt ℂ (iterD l g) z` using `fun z hz => hd.differentiableAt (hU.mem_nhds hz)`.

Establish `hpart : Set.EqOn (iterD (i :: l) g) (fun z => fderiv ℂ (iterD l g) z (Pi.single i 1)) U`. Introduce `z hz`. Use `show lineDeriv ℂ (iterD l g) z (Pi.single i 1) = _`. Conclude with `(hat z hz).lineDeriv_eq_fderiv`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Establish `hf : DifferentiableOn ℂ (fun z => fderiv ℂ (iterD l g) z (Pi.single i 1)) U` using `((GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hU hd).fderiv.differentiableOn).clm_apply (differentiableOn_const _)`. Conclude with `hf.congr hpart`. Introduce `z hz`. Establish `hev : wirtWord (l.map fun i => (i, false)) g =ᶠ[nhds z] iterD l g` using `Filter.eventually_of_mem (hU.mem_nhds hz) (fun y hy => (heq hy).symm)`. Use `show partialD i (iterD l g) z = wirt i false (wirtWord (l.map fun i => (i, false)) g) z`.

Establish `hw : wirt i false (wirtWord (l.map fun i => (i, false)) g) z = wirt i false (iterD l g) z`. Unfold `wirt`. Rewrite using `[hev.fderiv_eq]`. Rewrite using `[hw, wirt_false_eq_lineDeriv i _ z (hat z hz)]`. Both sides reduce to the same expression.
-/
theorem iterD_holo_and_eq {I : Type} [Fintype I] [DecidableEq I] (U : Set (I → ℂ)) (g : (I → ℂ) → ℂ)
    (hU : IsOpen U) (hg : DifferentiableOn ℂ g U) (l : List I) :
    DifferentiableOn ℂ (iterD l g) U ∧ Set.EqOn (iterD l g) (wirtWord (l.map fun i => (i, false)) g) U := by
  induction l with
  | nil => exact ⟨hg, fun _ _ => rfl⟩
  | cons i l ih =>
    obtain ⟨hd, heq⟩ := ih
    have hat : ∀ z ∈ U, DifferentiableAt ℂ (iterD l g) z := fun z hz => hd.differentiableAt (hU.mem_nhds hz)
    have hpart : Set.EqOn (iterD (i :: l) g) (fun z => fderiv ℂ (iterD l g) z (Pi.single i 1)) U := by
      intro z hz
      show lineDeriv ℂ (iterD l g) z (Pi.single i 1) = _
      exact (hat z hz).lineDeriv_eq_fderiv
    refine ⟨?_, ?_⟩
    · have hf : DifferentiableOn ℂ (fun z => fderiv ℂ (iterD l g) z (Pi.single i 1)) U :=
        ((GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hU hd).fderiv.differentiableOn).clm_apply
          (differentiableOn_const _)
      exact hf.congr hpart
    · intro z hz
      have hev : wirtWord (l.map fun i => (i, false)) g =ᶠ[nhds z] iterD l g :=
        Filter.eventually_of_mem (hU.mem_nhds hz) (fun y hy => (heq hy).symm)
      show partialD i (iterD l g) z = wirt i false (wirtWord (l.map fun i => (i, false)) g) z
      have hw : wirt i false (wirtWord (l.map fun i => (i, false)) g) z = wirt i false (iterD l g) z := by
        unfold wirt
        rw [hev.fderiv_eq]
      rw [hw, wirt_false_eq_lineDeriv i _ z (hat z hz)]
      rfl

/- English proof (translation)
Introduce `I _ _ U g hU hg l z hz`. Conclude with `(iterD_holo_and_eq U g hU hg l).2 hz`.
-/
theorem iterD_eq_wirtWord : ∀ (I : Type) [Fintype I] [DecidableEq I] (U : Set (I → ℂ)) (g : (I → ℂ) → ℂ),
    IsOpen U → DifferentiableOn ℂ g U → ∀ (l : List I), ∀ z ∈ U,
      iterD l g z = wirtWord (l.map fun i => (i, false)) g z := by
  intro I _ _ U g hU hg l z hz
  exact (iterD_holo_and_eq U g hU hg l).2 hz

end GlobalTheory.HoloWirt
