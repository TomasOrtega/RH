import Formalism.FormalDegreeBessel.StatementWR

open scoped ContDiff

noncomputable section

namespace Formalism.QuantumDeterminants

namespace WRPres

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Unfold `OmX`. Rewrite using `[Set.setOf_forall]`. Conclude with `isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const`.
-/
theorem isOpen_omX (m : ℕ) : IsOpen (OmX m) := by
  unfold OmX
  rw [Set.setOf_forall]
  exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const

/- English proof (translation)
The claim follows from `contDiff_apply ℝ ℂ l`.
-/
theorem coord_contDiff (l : Fin m) : ContDiff ℝ ∞ (fun x : Fin m → ℂ => x l) := contDiff_apply ℝ ℂ l

/- English proof (translation)
Use `first`. Consider the case `exact ContDiff.star (contDiff_apply ℝ ℂ l)`. Consider the case `exact (Complex.conjCLE.contDiff).comp (contDiff_apply ℝ ℂ l)`.
-/
theorem conjCoord_contDiff (l : Fin m) : ContDiff ℝ ∞ (fun x : Fin m → ℂ => star (x l)) := by
  first
  | exact ContDiff.star (contDiff_apply ℝ ℂ l)
  | exact (Complex.conjCLE.contDiff).comp (contDiff_apply ℝ ℂ l)

/- English proof (translation)
Conclude with `((contDiffOn_infty_iff_fderiv_of_isOpen (isOpen_omX m)).1 hf).2.clm_apply contDiffOn_const`.
-/
theorem fderiv_apply_contDiffOn {f : (Fin m → ℂ) → E} (hf : ContDiffOn ℝ ∞ f (OmX m))
    (v : Fin m → ℂ) : ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x v) (OmX m) := by
  exact ((contDiffOn_infty_iff_fderiv_of_isOpen (isOpen_omX m)).1 hf).2.clm_apply contDiffOn_const

/- English proof (translation)
Unfold `wirt`. Conclude with `((fderiv_apply_contDiffOn hf _).sub ((fderiv_apply_contDiffOn hf _).const_smul _)).const_smul _`.
-/
theorem wirt_contDiffOn {f : (Fin m → ℂ) → E} (hf : ContDiffOn ℝ ∞ f (OmX m)) (l : Fin m) :
    ContDiffOn ℝ ∞ (wirt l f) (OmX m) := by
  unfold wirt
  exact ((fderiv_apply_contDiffOn hf _).sub ((fderiv_apply_contDiffOn hf _).const_smul _)).const_smul _

/- English proof (translation)
Unfold `wirtBar`. Use `first`. Consider the case `exact ((fderiv_apply_contDiffOn hf _).add ((fderiv_apply_contDiffOn hf _).const_smul _)).const_smul _`. Consider the case `exact ((fderiv_apply_contDiffOn hf _).sub ((fderiv_apply_contDiffOn hf _).const_smul _)).const_smul _`.
-/
theorem wirtBar_contDiffOn {f : (Fin m → ℂ) → E} (hf : ContDiffOn ℝ ∞ f (OmX m)) (l : Fin m) :
    ContDiffOn ℝ ∞ (wirtBar l f) (OmX m) := by
  unfold wirtBar
  first
  | exact ((fderiv_apply_contDiffOn hf _).add ((fderiv_apply_contDiffOn hf _).const_smul _)).const_smul _
  | exact ((fderiv_apply_contDiffOn hf _).sub ((fderiv_apply_contDiffOn hf _).const_smul _)).const_smul _

/- English proof (translation)
Establish `h1 : ContDiffOn ℝ ∞ f (OmX m)` using `hf.1`. Conclude with `(h1.differentiableOn (by simp)).differentiableAt ((isOpen_omX m).mem_nhds hx)`.
-/
theorem differentiableAt_of_mem {f : (Fin m → ℂ) → E} (hf : f ∈ WSm m E) {x : Fin m → ℂ}
    (hx : x ∈ OmX m) : DifferentiableAt ℝ f x := by
  have h1 : ContDiffOn ℝ ∞ f (OmX m) := hf.1
  exact (h1.differentiableOn (by simp)).differentiableAt ((isOpen_omX m).mem_nhds hx)

end WRPres

open WRPres

/- English proof (translation)
Introduce `m E _ _ l i f hf`. Establish `hc : ContDiffOn ℝ ∞ f (OmX m)` using `hf.1`. Establish `hz : ∀ x ∉ OmX m, f x = 0` using `hf.2`. Establish `hcoord : ContDiffOn ℝ ∞ (fun x : Fin m → ℂ => x l) (OmX m)` using `(coord_contDiff l).contDiffOn`. Establish `hconj : ContDiffOn ℝ ∞ (fun x : Fin m → ℂ => star (x l)) (OmX m)` using `(conjCoord_contDiff l).contDiffOn`.

Establish `hne : ∀ x ∈ OmX m, x l ≠ 0` using `fun x hx => hx l`. Establish `hinv : ContDiffOn ℝ ∞ (fun x : Fin m → ℂ => (x l)⁻¹) (OmX m)` using `hcoord.inv hne`. Establish `hinvc : ContDiffOn ℝ ∞ (fun x : Fin m → ℂ => (star (x l))⁻¹) (OmX m)` using `hconj.inv fun x hx => by simpa using hne x hx`. Use `show ContDiffOn ℝ ∞ (opL l i f) (OmX m) ∧ ∀ x ∉ OmX m, opL l i f x = 0`. Use `fin_cases i`.

Conclude with `⟨(hcoord.smul (wirt_contDiffOn hc l)).congr fun x hx => by simp [opL, pOp, hx], fun x hx => by simp [opL, pOp, hx]⟩`. Conclude with `⟨(hcoord.smul hc).congr fun x hx => by simp [opL, cOp], fun x hx => by simp [opL, cOp, hz x hx]⟩`. Conclude with `⟨(hinv.smul hc).congr fun x hx => by simp [opL, ciOp], fun x hx => by simp [opL, ciOp, hz x hx]⟩`. Conclude with `⟨(hconj.smul (wirtBar_contDiffOn hc l)).congr fun x hx => by simp [opL, pbOp, hx], fun x hx => by simp [opL, pbOp, hx]⟩`. Conclude with `⟨(hconj.smul hc).congr fun x hx => by simp [opL, cbOp], fun x hx => by simp [opL, cbOp, hz x hx]⟩`.

Conclude with `⟨(hinvc.smul hc).congr fun x hx => by simp [opL, cbiOp], fun x hx => by simp [opL, cbiOp, hz x hx]⟩`.
-/
theorem preserved_operators_holds : PresOps := by
  intro m E _ _ l i f hf
  have hc : ContDiffOn ℝ ∞ f (OmX m) := hf.1
  have hz : ∀ x ∉ OmX m, f x = 0 := hf.2
  have hcoord : ContDiffOn ℝ ∞ (fun x : Fin m → ℂ => x l) (OmX m) := (coord_contDiff l).contDiffOn
  have hconj : ContDiffOn ℝ ∞ (fun x : Fin m → ℂ => star (x l)) (OmX m) :=
    (conjCoord_contDiff l).contDiffOn
  have hne : ∀ x ∈ OmX m, x l ≠ 0 := fun x hx => hx l
  have hinv : ContDiffOn ℝ ∞ (fun x : Fin m → ℂ => (x l)⁻¹) (OmX m) := hcoord.inv hne
  have hinvc : ContDiffOn ℝ ∞ (fun x : Fin m → ℂ => (star (x l))⁻¹) (OmX m) :=
    hconj.inv fun x hx => by simpa using hne x hx
  show ContDiffOn ℝ ∞ (opL l i f) (OmX m) ∧ ∀ x ∉ OmX m, opL l i f x = 0
  fin_cases i
  · exact ⟨(hcoord.smul (wirt_contDiffOn hc l)).congr fun x hx => by simp [opL, pOp, hx],
      fun x hx => by simp [opL, pOp, hx]⟩
  · exact ⟨(hcoord.smul hc).congr fun x hx => by simp [opL, cOp],
      fun x hx => by simp [opL, cOp, hz x hx]⟩
  · exact ⟨(hinv.smul hc).congr fun x hx => by simp [opL, ciOp],
      fun x hx => by simp [opL, ciOp, hz x hx]⟩
  · exact ⟨(hconj.smul (wirtBar_contDiffOn hc l)).congr fun x hx => by simp [opL, pbOp, hx],
      fun x hx => by simp [opL, pbOp, hx]⟩
  · exact ⟨(hconj.smul hc).congr fun x hx => by simp [opL, cbOp],
      fun x hx => by simp [opL, cbOp, hz x hx]⟩
  · exact ⟨(hinvc.smul hc).congr fun x hx => by simp [opL, cbiOp],
      fun x hx => by simp [opL, cbiOp, hz x hx]⟩

/- English proof (translation)
Introduce `m E _ _ l i f g a hf hg`. Establish `hd : ∀ x ∈ OmX m, DifferentiableAt ℝ f x ∧ DifferentiableAt ℝ g x` using `fun x hx => ⟨differentiableAt_of_mem hf hx, differentiableAt_of_mem hg hx⟩`. Apply the tactic sequence `fin_cases i <;> refine ⟨funext fun x => ?_, funext fun x => ?_⟩ <;>`. Apply the tactic sequence `simp only [opL, pOp, cOp, ciOp, pbOp, cbOp, cbiOp, wirt, wirtBar, Pi.add_apply, Pi.smul_apply, Fin.isValue] <;>`. Apply the tactic sequence `(try split_ifs with hx) <;>`.

Apply the tactic sequence `(try (have e1 : fderiv ℝ (f + g) x = fderiv ℝ f x + fderiv ℝ g x := fderiv_add (hd x hx).1 (hd x hx).2`. Apply the tactic sequence `rw [e1])) <;>`. Apply the tactic sequence `(try (have e2 : fderiv ℝ (a • f) x = a • fderiv ℝ f x := by first`. Consider the case `exact fderiv_const_smul (hd x hx).1 a`. Consider the case `exact fderiv_const_smul a (hd x hx).1`.

Apply the tactic sequence `rw [e2])) <;>`. Apply the tactic sequence `(try simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_zero, add_zero]) <;>`. Use `module`.
-/
theorem linear_operators_holds : LinOps := by
  intro m E _ _ l i f g a hf hg
  have hd : ∀ x ∈ OmX m, DifferentiableAt ℝ f x ∧ DifferentiableAt ℝ g x :=
    fun x hx => ⟨differentiableAt_of_mem hf hx, differentiableAt_of_mem hg hx⟩
  fin_cases i <;> refine ⟨funext fun x => ?_, funext fun x => ?_⟩ <;>
    simp only [opL, pOp, cOp, ciOp, pbOp, cbOp, cbiOp, wirt, wirtBar, Pi.add_apply, Pi.smul_apply,
      Fin.isValue] <;>
    (try split_ifs with hx) <;>
    (try (have e1 : fderiv ℝ (f + g) x = fderiv ℝ f x + fderiv ℝ g x :=
            fderiv_add (hd x hx).1 (hd x hx).2
          rw [e1])) <;>
    (try (have e2 : fderiv ℝ (a • f) x = a • fderiv ℝ f x := by
            first
            | exact fderiv_const_smul (hd x hx).1 a
            | exact fderiv_const_smul a (hd x hx).1
          rw [e2])) <;>
    (try simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_zero, add_zero]) <;>
    module

end Formalism.QuantumDeterminants
