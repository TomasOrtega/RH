import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option linter.unusedSectionVars false

namespace PositivityTheory.Xgp.c_bm_exists_period

section Hol
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {I J K : Type} [Fintype I] [Fintype J] [Fintype K]

def HolM (s : Set X) (A : X → Matrix I J ℂ) : Prop := ∀ a b, DifferentiableOn ℂ (fun x => A x a b) s

/- English proof (translation)
Introduce `_ _` and use `differentiableOn_const _`.
-/
theorem HolM.const (s : Set X) (A : Matrix I J ℂ) : HolM s fun _ => A := fun _ _ => differentiableOn_const _

/- English proof (translation)
Introduce `a b` and use `(h a b).mono ht`.
-/
theorem HolM.mono {s t : Set X} {A : X → Matrix I J ℂ} (h : HolM s A) (ht : t ⊆ s) : HolM t A :=
  fun a b => (h a b).mono ht

/- English proof (translation)
Introduce `a b` and use `by simp only [Matrix.mul_apply] exact DifferentiableOn.fun_sum fun k _ => (hA a k).mul (hB k b)`.
-/
theorem HolM.mul {s : Set X} {A : X → Matrix I J ℂ} {B : X → Matrix J K ℂ} (hA : HolM s A) (hB : HolM s B) :
    HolM s fun x => A x * B x := fun a b => by
  simp only [Matrix.mul_apply]
  exact DifferentiableOn.fun_sum fun k _ => (hA a k).mul (hB k b)

/- English proof (translation)
Simplify using `only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]`. Apply `DifferentiableOn.fun_sum` to reduce the goal to its premises. Introduce `σ _`. Use `(differentiableOn_const _).mul ?_` and prove the remaining obligations. Establish `key : ∀ t : Finset I, DifferentiableOn ℂ (fun x => ∏ i ∈ t, A x (σ i) i) s`.

Introduce `t`. Use `Finset.induction_on t ?_ ?_` and prove the remaining obligations. Simplify using `only [Finset.prod_empty]`. Conclude with `differentiableOn_const _`. Introduce `j t hj ih`.

Simplify using `only [Finset.prod_insert hj]`. Conclude with `(hA (σ j) j).mul ih`. Conclude with `key Finset.univ`.
-/
theorem HolM.det [DecidableEq I] {s : Set X} {A : X → Matrix I I ℂ} (hA : HolM s A) :
    DifferentiableOn ℂ (fun x => (A x).det) s := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  apply DifferentiableOn.fun_sum
  intro σ _
  refine (differentiableOn_const _).mul ?_
  have key : ∀ t : Finset I, DifferentiableOn ℂ (fun x => ∏ i ∈ t, A x (σ i) i) s := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · simp only [Finset.prod_empty]
      exact differentiableOn_const _
    · intro j t hj ih
      simp only [Finset.prod_insert hj]
      exact (hA (σ j) j).mul ih
  exact key Finset.univ

/- English proof (translation)
Introduce `a b`. Establish `hu : HolM s fun x => (A x).updateRow b (Pi.single a 1)`. Introduce `i k`. Simplify using `only [Matrix.updateRow_apply]`. Use `split_ifs`.

Conclude with `differentiableOn_const _`. Conclude with `hA i k`. Simplify using `only [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, smul_eq_mul, Ring.inverse_eq_inv']`. Conclude with `(hA.det.inv hd).mul hu.det`.
-/
theorem HolM.inv [DecidableEq I] {s : Set X} {A : X → Matrix I I ℂ} (hA : HolM s A) (hd : ∀ x ∈ s, (A x).det ≠ 0) :
    HolM s fun x => (A x)⁻¹ := by
  intro a b
  have hu : HolM s fun x => (A x).updateRow b (Pi.single a 1) := by
    intro i k
    simp only [Matrix.updateRow_apply]
    split_ifs
    · exact differentiableOn_const _
    · exact hA i k
  simp only [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact (hA.det.inv hd).mul hu.det

/- English proof (translation)
The claim follows from `hA.det.continuousOn.isOpen_inter_preimage hs isOpen_ne`.
-/
theorem HolM.isOpen_det [DecidableEq I] {s : Set X} {A : X → Matrix I I ℂ} (hA : HolM s A) (hs : IsOpen s) :
    IsOpen {x ∈ s | (A x).det ≠ 0} :=
  hA.det.continuousOn.isOpen_inter_preimage hs isOpen_ne

noncomputable def dM (A : X → Matrix I J ℂ) (u v : X) : Matrix I J ℂ :=
  Matrix.of fun a b => fderiv ℂ (fun x => A x a b) u v

/- English proof (translation)
Establish `hd : ∀ a b, DifferentiableAt ℂ (fun x => A x a b) u` using `fun a b => (hA a b).differentiableAt hu`. Establish `he : ∀ a b, DifferentiableAt ℂ (fun x => B x a b) u` using `fun a b => (hB a b).differentiableAt hu`. Use extensionality with `a c`. Simplify using `only [dM, Matrix.of_apply, Matrix.mul_apply, Matrix.add_apply]`. Establish `key : HasFDerivAt (fun x => ∑ j, A x a j * B x j c) (∑ j, (A u a j • fderiv ℂ (fun x => B x j c) u + B u j c • fderiv ℂ (fun x => A x a j) u)) u` using `HasFDerivAt.fun_sum fun j _ => (hd a j).hasFDerivAt.mul (he j c).hasFDerivAt`.

Rewrite using `[key.fderiv]`. Simplify using `only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.sum_add_distrib]`. Rewrite using `[add_comm]`. Apply the tactic sequence `congr 1 <;> refine Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem dM_mul {s : Set X} {A : X → Matrix I J ℂ} {B : X → Matrix J K ℂ} (hA : HolM s A) (hB : HolM s B) {u : X}
    (hu : s ∈ nhds u) (v : X) : dM (fun x => A x * B x) u v = dM A u v * B u + A u * dM B u v := by
  have hd : ∀ a b, DifferentiableAt ℂ (fun x => A x a b) u := fun a b => (hA a b).differentiableAt hu
  have he : ∀ a b, DifferentiableAt ℂ (fun x => B x a b) u := fun a b => (hB a b).differentiableAt hu
  ext a c
  simp only [dM, Matrix.of_apply, Matrix.mul_apply, Matrix.add_apply]
  have key : HasFDerivAt (fun x => ∑ j, A x a j * B x j c)
      (∑ j, (A u a j • fderiv ℂ (fun x => B x j c) u + B u j c • fderiv ℂ (fun x => A x a j) u)) u :=
    HasFDerivAt.fun_sum fun j _ => (hd a j).hasFDerivAt.mul (he j c).hasFDerivAt
  rw [key.fderiv]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1 <;> refine Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [dM, Matrix.of_apply, Matrix.zero_apply]`. Establish `he : (fun x => A x a b) =ᶠ[nhds u] fun _ => C a b` using `h.mono fun x hx => by simp [hx]`. Rewrite using `[he.fderiv_eq]`. Simplify using the standard rewrite rules.
-/
theorem dM_const {A : X → Matrix I J ℂ} {C : Matrix I J ℂ} {u : X} (h : ∀ᶠ x in nhds u, A x = C) (v : X) :
    dM A u v = 0 := by
  ext a b
  simp only [dM, Matrix.of_apply, Matrix.zero_apply]
  have he : (fun x => A x a b) =ᶠ[nhds u] fun _ => C a b := h.mono fun x hx => by simp [hx]
  rw [he.fderiv_eq]
  simp

end Hol

end PositivityTheory.Xgp.c_bm_exists_period
