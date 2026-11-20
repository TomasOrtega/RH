import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.LcLaws

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

/- English proof (translation)
Establish `h` using `(sgLaws K v).1 0 0`. Simplify using `using h`.
-/
private theorem sg_zero' {K : Type} [Field K] [NumberField K] (v : P K) : sg v 0 = 0 := by
  have h := (sgLaws K v).1 0 0
  simpa using h

/- English proof (translation)
Establish `h` using `(sgLaws K v).2.1 (sg v x) y`. Rewrite `h` using `[(sgLaws K v).2.2.1]`. Conclude with `h`.
-/
private theorem sg_mul' {K : Type} [Field K] [NumberField K] (v : P K) (x y : Kv v) :
    sg v x * sg v y = sg v (x * y) := by
  have h := (sgLaws K v).2.1 (sg v x) y
  rw [(sgLaws K v).2.2.1] at h
  exact h

/- English proof (translation)
The claim follows from `(sgLaws K v).2.2.2.2.1 _ i k`.
-/
private theorem lc_entry {K : Type} [Field K] [NumberField K] (v : P K)
    (x : Matrix.SpecialLinearGroup (Fin 2) (Kv v)) (i k : Fin 2) :
    (lc v (Matrix.SpecialLinearGroup.toGL x)).val i k =
      (1 : Matrix (Fin 2) (Fin 2) (A K)) i k + sg v (x i k - (1 : Matrix (Fin 2) (Fin 2) (Kv v)) i k) :=
  (sgLaws K v).2.2.2.2.1 _ i k

/- English proof (translation)
Establish `hadd` using `(sgLaws K v).1`. Establish `hd` using `x.det_coe`. Rewrite `hd` using `[Matrix.det_fin_two]`. Rewrite using `[Matrix.det_fin_two]`. Simplify using `only [lc_entry]`.

Simplify using `only [Matrix.one_apply_eq, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true, Matrix.one_apply_ne, zero_add, sub_zero]`. Establish `e : ∀ a b : Kv v, sg v (a - b) = sg v a - sg v b` using `fun a b => by`. Use `hadd (a - b) b` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree. Establish `key : sg v (x 0 0 - 1) + sg v (x 1 1 - 1) + sg v (x 0 0 - 1) * sg v (x 1 1 - 1) - sg v (x 0 1) * sg v (x 1 0) = 0`. Simplify using `only [sg_mul', ← hadd, ← e]`. Establish `: x 0 0 - 1 + (x 1 1 - 1) + (x 0 0 - 1) * (x 1 1 - 1) - x 0 1 * x 1 0 = 0`. Establish `hd' : x 0 0 * x 1 1 - x 0 1 * x 1 0 = 1` using `hd`.

Take the linear combination `hd'`. Rewrite using `[this, sg_zero']`. Take the linear combination `key`.
-/
private theorem lc_det {K : Type} [Field K] [NumberField K] (v : P K)
    (x : Matrix.SpecialLinearGroup (Fin 2) (Kv v)) :
    ((lc v (Matrix.SpecialLinearGroup.toGL x)).val).det = 1 := by
  have hadd := (sgLaws K v).1
  have hd := x.det_coe
  rw [Matrix.det_fin_two] at hd
  rw [Matrix.det_fin_two]
  simp only [lc_entry]
  simp only [Matrix.one_apply_eq, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true, Matrix.one_apply_ne, zero_add, sub_zero]
  have e : ∀ a b : Kv v, sg v (a - b) = sg v a - sg v b := fun a b => by
    have := hadd (a - b) b
    rw [sub_add_cancel] at this
    rw [this]; ring
  have key : sg v (x 0 0 - 1) + sg v (x 1 1 - 1) + sg v (x 0 0 - 1) * sg v (x 1 1 - 1) - sg v (x 0 1) * sg v (x 1 0) = 0 := by
    simp only [sg_mul', ← hadd, ← e]
    have : x 0 0 - 1 + (x 1 1 - 1) + (x 0 0 - 1) * (x 1 1 - 1) - x 0 1 * x 1 0 = 0 := by
      have hd' : x 0 0 * x 1 1 - x 0 1 * x 1 0 = 1 := hd
      linear_combination hd'
    rw [this, sg_zero']
  linear_combination key

/- English proof (translation)
Use `⟨{ toFun := fun x => ⟨(lc v (Matrix.SpecialLinearGroup.toGL x)).val, lc_det v x⟩, map_one' := ?_, map_mul' := ?_ }, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Introduce `x y`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using the standard rewrite rules. Both sides reduce to the same expression. Introduce `x`. Apply `Units.ext` to reduce the goal to its premises. Both sides reduce to the same expression.
-/
private theorem jEx_exists {K : Type} [Field K] [NumberField K] (v : P K) : ∃ j, IsJ v j := by
  refine ⟨{ toFun := fun x => ⟨(lc v (Matrix.SpecialLinearGroup.toGL x)).val, lc_det v x⟩, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · apply Subtype.ext
    simp
  · intro x y
    apply Subtype.ext
    simp
    rfl
  · intro x
    apply Units.ext
    rfl

/- English proof (translation)
Introduce `K _ _ v`. Use `⟨jEx_exists v, fun j hj => ?_⟩` and prove the remaining obligations. Establish `hent : ∀ x i k, (j x) i k = (1 : Matrix (Fin 2) (Fin 2) (A K)) i k + sg v (x i k - (1 : Matrix (Fin 2) (Fin 2) (Kv v)) i k)`. Introduce `x i k`. Establish `h` using `congrArg (fun g : GL (Fin 2) (A K) => g.val i k) (hj x)`.

Apply the tactic sequence `exact h.trans (lc_entry v x i k)`. Establish `hsg` using `(sgLaws K v).2.2.2.2.2.2.2.1`. Establish `hcsg` using `(sgLaws K v).2.2.2.2.2.2.2.2.2`. Use `⟨?_, ?_, ?_, hent⟩` and prove the remaining obligations. Establish `hv : Continuous fun x : Matrix.SpecialLinearGroup (Fin 2) (Kv v) => (j x).1`.

Use `continuous_matrix fun i k => ?_` and prove the remaining obligations. Establish `he : (fun x : Matrix.SpecialLinearGroup (Fin 2) (Kv v) => (j x).1 i k) = fun x => (1 : Matrix (Fin 2) (Fin 2) (A K)) i k + sg v (x i k - (1 : Matrix (Fin 2) (Fin 2) (Kv v)) i k)`. Use function extensionality and compare the values at `fun x => hent x i k`. Rewrite using `[he]`. Establish `hx : Continuous fun x : Matrix.SpecialLinearGroup (Fin 2) (Kv v) => x i k` using `continuous_subtype_val.matrix_elem i k`.

Conclude with `continuous_const.add (hcsg.comp (hx.sub continuous_const))`. Conclude with `Continuous.subtype_mk hv fun x => (j x).2`. Introduce `x`. Use `⟨fun i k => ?_, fun v' hv' i k => ?_⟩` and prove the remaining obligations. Rewrite using `[hent] show _ + (sg v _).1 = _`.

Rewrite using `[(hsg _).1, add_zero]`. Rewrite using `[hent] show _ + (sg v _).2 v' = _`. Rewrite using `[(hsg _).2 v' hv', add_zero]`. Both sides reduce to the same expression. Introduce `x hx i k`.

Establish `: (j x i k).2 v = x i k`. Establish `h1 : cp v (j x i k) = x i k`. Rewrite using `[hent, map_add, (sgLaws K v).2.2.1]`. Apply the tactic sequence `fin_cases i <;> fin_cases k <;> simp`. Conclude with `h1`.

Rewrite using `[this]`. Conclude with `hx i k`.
-/
theorem UpperTheory.ConvolutionTheory.R2.H.jEx :
    ∀ (K : Type) [Field K] [NumberField K] (v : P K), (∃ j, IsJ v j) ∧ ∀ j, IsJ v j → Continuous j ∧ (∀ x, At v (j x)) ∧ (∀ x, (∀ i k, IsInt (x i k)) → IntAt v (j x)) ∧
      (∀ x i k, (j x) i k = (1 : Matrix (Fin 2) (Fin 2) (A K)) i k + sg v (x i k - (1 : Matrix (Fin 2) (Fin 2) (Kv v)) i k)) := by
  intro K _ _ v
  refine ⟨jEx_exists v, fun j hj => ?_⟩
  have hent : ∀ x i k, (j x) i k = (1 : Matrix (Fin 2) (Fin 2) (A K)) i k + sg v (x i k - (1 : Matrix (Fin 2) (Fin 2) (Kv v)) i k) := by
    intro x i k
    have h := congrArg (fun g : GL (Fin 2) (A K) => g.val i k) (hj x)
    exact h.trans (lc_entry v x i k)
  have hsg := (sgLaws K v).2.2.2.2.2.2.2.1
  have hcsg := (sgLaws K v).2.2.2.2.2.2.2.2.2
  refine ⟨?_, ?_, ?_, hent⟩
  · have hv : Continuous fun x : Matrix.SpecialLinearGroup (Fin 2) (Kv v) => (j x).1 := by
      refine continuous_matrix fun i k => ?_
      have he : (fun x : Matrix.SpecialLinearGroup (Fin 2) (Kv v) => (j x).1 i k) = fun x =>
          (1 : Matrix (Fin 2) (Fin 2) (A K)) i k + sg v (x i k - (1 : Matrix (Fin 2) (Fin 2) (Kv v)) i k) :=
        funext fun x => hent x i k
      rw [he]
      have hx : Continuous fun x : Matrix.SpecialLinearGroup (Fin 2) (Kv v) => x i k :=
        continuous_subtype_val.matrix_elem i k
      exact continuous_const.add (hcsg.comp (hx.sub continuous_const))
    exact Continuous.subtype_mk hv fun x => (j x).2
  · intro x
    refine ⟨fun i k => ?_, fun v' hv' i k => ?_⟩
    · rw [hent]
      show _ + (sg v _).1 = _
      rw [(hsg _).1, add_zero]
    · rw [hent]
      show _ + (sg v _).2 v' = _
      rw [(hsg _).2 v' hv', add_zero]
      rfl
  · intro x hx i k
    have : (j x i k).2 v = x i k := by
      have h1 : cp v (j x i k) = x i k := by
        rw [hent, map_add, (sgLaws K v).2.2.1]
        fin_cases i <;> fin_cases k <;> simp
      exact h1
    rw [this]
    exact hx i k
