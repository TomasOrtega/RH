import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.ThInf
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

/- English proof (translation)
Introduce `E _ _ _ k hk f X hf g`. Establish `hfst : ∀ i j, ((em E k).val i j).1 = ((1 : Matrix (Fin 2) (Fin 2) (A E)) i j).1`. Introduce `i j`. Establish `e : (em E k).val i j = AdeleBaseChange.adeleMap ℚ E (k.val i j)` using `rfl`. Establish `e1 : (1 : Matrix (Fin 2) (Fin 2) (A E)) i j = AdeleBaseChange.adeleMap ℚ E ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j)`.

Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne h]`. Rewrite using `[e, e1, AdeleBaseChange.adeleMap_apply, AdeleBaseChange.adeleMap_apply, hk i j]`.

Establish `h1 : Matrix.GeneralLinearGroup.map (pInf E) (em E k) = 1`. Establish `h2 : Matrix.GeneralLinearGroup.map (pInf E) (em E k) = Matrix.GeneralLinearGroup.map (pInf E) (1 : GL (Fin 2) (A E))`. Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Conclude with `congrArg (fun x => (infEq E).symm x) (hfst i j)`. Rewrite using `[h2, map_one]`.

Establish `hm : finGL E 2 (Matrix.GeneralLinearGroup.map (pFin E) (em E k)) = em E k`. Establish `h3` using `infGL_mul_finGL (em E k)`. Rewrite `h3` using `[h1, map_one, one_mul]`. Then use the resulting hypothesis. Establish `hr : GlobalTheory.CuspRep.rt E 2 (em E k) f = f` using `Subtype.ext (funext hf)`. Establish `h4` using `LinearMap.congr_fun (lie_rt_fin X (Matrix.GeneralLinearGroup.map (pFin E) (em E k))) f`.

Rewrite `h4` using `[hm, Module.End.mul_apply, Module.End.mul_apply, hr]`. Conclude with `(congrArg (fun φ : Sm E 2 => φ.1 g) h4).symm`.
-/
theorem UpperTheory.lie_action_preserves_right_invariance_finite_adelic :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (k : GL (Fin 2) (A ℚ)), (∀ i j, (k.val i j).1 = ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j).1) → ∀ (f : Sm E 2) (X : Lie E 2), (∀ g, f.1 (g * em E k) = f.1 g) → ∀ g, (lie E 2 X f).1 (g * em E k) = (lie E 2 X f).1 g := by
  intro E _ _ _ k hk f X hf g
  have hfst : ∀ i j, ((em E k).val i j).1 = ((1 : Matrix (Fin 2) (Fin 2) (A E)) i j).1 := by
    intro i j
    have e : (em E k).val i j = AdeleBaseChange.adeleMap ℚ E (k.val i j) := rfl
    have e1 : (1 : Matrix (Fin 2) (Fin 2) (A E)) i j =
        AdeleBaseChange.adeleMap ℚ E ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j) := by
      by_cases h : i = j
      · subst h; simp
      · simp [Matrix.one_apply_ne h]
    rw [e, e1, AdeleBaseChange.adeleMap_apply, AdeleBaseChange.adeleMap_apply, hk i j]
  have h1 : Matrix.GeneralLinearGroup.map (pInf E) (em E k) = 1 := by
    have h2 : Matrix.GeneralLinearGroup.map (pInf E) (em E k) =
        Matrix.GeneralLinearGroup.map (pInf E) (1 : GL (Fin 2) (A E)) := by
      refine Units.ext (Matrix.ext fun i j => ?_)
      exact congrArg (fun x => (infEq E).symm x) (hfst i j)
    rw [h2, map_one]
  have hm : finGL E 2 (Matrix.GeneralLinearGroup.map (pFin E) (em E k)) = em E k := by
    have h3 := infGL_mul_finGL (em E k)
    rwa [h1, map_one, one_mul] at h3
  have hr : GlobalTheory.CuspRep.rt E 2 (em E k) f = f := Subtype.ext (funext hf)
  have h4 := LinearMap.congr_fun (lie_rt_fin X (Matrix.GeneralLinearGroup.map (pFin E) (em E k))) f
  rw [hm, Module.End.mul_apply, Module.End.mul_apply, hr] at h4
  exact (congrArg (fun φ : Sm E 2 => φ.1 g) h4).symm
