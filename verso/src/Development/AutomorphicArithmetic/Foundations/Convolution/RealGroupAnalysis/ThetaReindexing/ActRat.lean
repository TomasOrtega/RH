import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.ActMat

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.D

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Simplify using `only [Dat.mkE, rt, AdeleBaseChange.adeleMap_algebraMap, map_add, map_mul]`.
-/
private theorem mkE_rt (D : Dat F E) (u t : F) :
    D.mkE (rt u) (rt t) = rt (algebraMap F E u + algebraMap F E t * D.θ) := by
  simp only [Dat.mkE, rt, AdeleBaseChange.adeleMap_algebraMap, map_add, map_mul]

/- English proof (translation)
The claim follows from `AdeleBaseChange.smul_algebraMap D.σ z`.
-/
private theorem bar_rt (D : Dat F E) (z : E) : D.bar (rt z) = rt (D.σ z) :=
  AdeleBaseChange.smul_algebraMap D.σ z

/- English proof (translation)
The claim follows from `AdeleBaseChange.adeleBasis_repr_algebraMap D.b z i`.
-/
private theorem co_rt (D : Dat F E) (z : E) (i : Fin 2) : D.co (rt z) i = rt (D.b.repr z i) :=
  AdeleBaseChange.adeleBasis_repr_algebraMap D.b z i

/- English proof (translation)
Establish `e0 : ∀ u : F, D.mkE (rt u) 0 = rt (algebraMap F E u + algebraMap F E 0 * D.θ)` using `fun u => by`. Rewrite using `[← mkE_rt, show (rt (0 : F) : A F) = 0 from map_zero _]`. Establish `e3 : D.mkE (rt (ξ 2)) (-rt (ξ 3)) = rt (algebraMap F E (ξ 2) + algebraMap F E (-ξ 3) * D.θ)`. Rewrite using `[← mkE_rt, show (rt (-ξ 3) : A F) = -rt (ξ 3) from map_neg _ _]`. Use extensionality with `i j`.

Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `e0 _`. Conclude with `mkE_rt D _ _`. Conclude with `e3`. Conclude with `e0 _`.
-/
private theorem herm_rt (D : Dat F E) (ξ : Fin 4 → F) :
    D.herm (fun i => rt (ξ i)) =
      (!![algebraMap F E (ξ 1) + algebraMap F E 0 * D.θ, algebraMap F E (ξ 2) + algebraMap F E (ξ 3) * D.θ;
        algebraMap F E (ξ 2) + algebraMap F E (-ξ 3) * D.θ, algebraMap F E (ξ 0) + algebraMap F E 0 * D.θ]).map
        (algebraMap E (A E)) := by
  have e0 : ∀ u : F, D.mkE (rt u) 0 = rt (algebraMap F E u + algebraMap F E 0 * D.θ) := fun u => by
    rw [← mkE_rt, show (rt (0 : F) : A F) = 0 from map_zero _]
  have e3 : D.mkE (rt (ξ 2)) (-rt (ξ 3)) = rt (algebraMap F E (ξ 2) + algebraMap F E (-ξ 3) * D.θ) := by
    rw [← mkE_rt, show (rt (-ξ 3) : A F) = -rt (ξ 3) from map_neg _ _]
  ext i j
  fin_cases i <;> fin_cases j
  · exact e0 _
  · exact mkE_rt D _ _
  · exact e3
  · exact e0 _

variable [IsTotallyComplex E]

/- English proof (translation)
Establish `hd : Matrix.GeneralLinearGroup.det (ratGL E 2 γ) = IdeleGroup.diagonal E (Matrix.GeneralLinearGroup.det γ)` using `Units.ext (by`. Express the relevant statement in the definitionally equal form `(ratGL E 2 γ).val.det = algebraMap E (A E) γ.val.det`. Rewrite using `[RingHom.map_det]`. Use the proof step `rfl)`. Rewrite using `[nu, hd, ideleNorm_diagonal, ab, IdeleGroup.ideleModule_diagonal]`.

Both sides reduce to the same expression.
-/
private theorem ab_nu (γ : GL (Fin 2) E) : ab (nu F (ratGL E 2 γ)) = 1 := by
  have hd : Matrix.GeneralLinearGroup.det (ratGL E 2 γ) =
      IdeleGroup.diagonal E (Matrix.GeneralLinearGroup.det γ) := Units.ext (by
    change (ratGL E 2 γ).val.det = algebraMap E (A E) γ.val.det
    rw [RingHom.map_det]
    rfl)
  rw [nu, hd, ideleNorm_diagonal, ab, IdeleGroup.ideleModule_diagonal]
  rfl

/- English proof (translation)
Take `⟨X, hX⟩ : ∃ X : Matrix (Fin 2) (Fin 2) E, D.herm (fun i => rt (ξ i)) = X.map (algebraMap E (A E))` from `⟨_, herm_rt D ξ⟩`. Establish `hh : (ratGL E 2 γ).val = γ.val.map (algebraMap E (A E))` using `rfl`. Establish `hb : (ratGL E 2 γ).val.map D.bar = (γ.val.map D.σ).map (algebraMap E (A E))`. Use extensionality with `i j`. Conclude with `bar_rt D (γ.val i j)`.

Use `set P : Matrix (Fin 2) (Fin 2) E := γ.val * X * (γ.val.map D.σ)ᵀ with hP`. Establish `hm : (ratGL E 2 γ).val * D.herm (fun i => rt (ξ i)) * ((ratGL E 2 γ).val.map D.bar)ᵀ = P.map (algebraMap E (A E))`. Rewrite using `[hX, hb, hh, hP, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]`. Use `⟨![D.b.repr (P 1 1) 0, D.b.repr (P 0 0) 0, D.b.repr (P 0 1) 0, D.b.repr (P 0 1) 1], ?_⟩` and prove the remaining obligations. Rewrite using `[Dat.act, hm]`.

Use function extensionality and compare the values at `i`. Use `fin_cases i`. Conclude with `co_rt D _ _`. Conclude with `co_rt D _ _`. Conclude with `co_rt D _ _`.

Conclude with `co_rt D _ _`.
-/
private theorem act_rat (D : Dat F E) (γ : GL (Fin 2) E) (ξ : Fin 4 → F) :
    ∃ ξ' : Fin 4 → F, D.act (ratGL E 2 γ) (fun i => rt (ξ i)) = fun i => rt (ξ' i) := by
  obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin 2) (Fin 2) E, D.herm (fun i => rt (ξ i)) = X.map (algebraMap E (A E)) := ⟨_, herm_rt D ξ⟩
  have hh : (ratGL E 2 γ).val = γ.val.map (algebraMap E (A E)) := rfl
  have hb : (ratGL E 2 γ).val.map D.bar = (γ.val.map D.σ).map (algebraMap E (A E)) := by
    ext i j
    exact bar_rt D (γ.val i j)
  set P : Matrix (Fin 2) (Fin 2) E := γ.val * X * (γ.val.map D.σ)ᵀ with hP
  have hm : (ratGL E 2 γ).val * D.herm (fun i => rt (ξ i)) * ((ratGL E 2 γ).val.map D.bar)ᵀ =
      P.map (algebraMap E (A E)) := by
    rw [hX, hb, hh, hP, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  refine ⟨![D.b.repr (P 1 1) 0, D.b.repr (P 0 0) 0, D.b.repr (P 0 1) 0, D.b.repr (P 0 1) 1], ?_⟩
  rw [Dat.act, hm]
  funext i
  fin_cases i
  · exact co_rt D _ _
  · exact co_rt D _ _
  · exact co_rt D _ _
  · exact co_rt D _ _

end

end UpperTheory.ConvolutionTheory.R2.D

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ D γ φ`. Take `⟨ρ, hρ, -, -⟩` from `UpperTheory.ConvolutionTheory.R2.D.actMat F E D`. Establish `hmul : ∀ h h' v, D.act (h * h') v = D.act h (D.act h' v)`. Introduce `h h' v`. Rewrite using `[hρ, hρ, hρ, map_mul, Units.val_mul, Matrix.mulVec_mulVec]`.

Establish `hone : ∀ v, D.act 1 v = v`. Introduce `v`. Rewrite using `[hρ, map_one, Units.val_one, Matrix.one_mulVec]`. Establish `hinj : Function.Injective (fun (ξ : Fin 4 → F) (i : Fin 4) => (rt (ξ i) : A F))`. Introduce `a b hab`.

Use function extensionality and compare the values at `i`. Conclude with `AdeleRing.algebraMap_injective (𝓞 F) F (congrFun hab i)`. Use `choose f hf using fun (g : GL (Fin 2) E) (ξ : Fin 4 → F) => UpperTheory.ConvolutionTheory.R2.D.act_rat D g ξ`. Establish `hinv : ∀ (g : GL (Fin 2) E) ξ, f g⁻¹ (f g ξ) = ξ`. Introduce `g ξ`.

Apply `hinj` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(fun i => (rt (f g⁻¹ (f g ξ) i) : A F)) = fun i => rt (ξ i)`. Rewrite using `[← hf g⁻¹ (f g ξ), ← hf g ξ, ← hmul, ← map_mul, inv_mul_cancel, map_one, hone]`. Set `e : (Fin 4 → F) ≃ (Fin 4 → F)` to `⟨f γ⁻¹, f γ, fun ξ => by simpa using hinv γ⁻¹ ξ, hinv γ⟩`. Simplify using `only [Th, UpperTheory.ConvolutionTheory.R2.D.ab_nu, inv_one, Complex.ofReal_one, one_mul, ← map_inv, hf]`.

Conclude with `e.tsum_eq fun ξ => φ fun i => rt (ξ i)`.
-/
theorem UpperTheory.ConvolutionTheory.R2.D.thL :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex E] (D : Dat F E) (γ : GL (Fin 2) E) (φ : V4 F → ℂ),
    Th (fun v => (((ab (nu F (ratGL E 2 γ)))⁻¹ : ℝ) : ℂ) * φ (D.act (ratGL E 2 γ)⁻¹ v)) = Th φ := by
  intro F E _ _ _ _ _ _ D γ φ
  obtain ⟨ρ, hρ, -, -⟩ := UpperTheory.ConvolutionTheory.R2.D.actMat F E D
  have hmul : ∀ h h' v, D.act (h * h') v = D.act h (D.act h' v) := by
    intro h h' v
    rw [hρ, hρ, hρ, map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  have hone : ∀ v, D.act 1 v = v := by
    intro v
    rw [hρ, map_one, Units.val_one, Matrix.one_mulVec]
  have hinj : Function.Injective (fun (ξ : Fin 4 → F) (i : Fin 4) => (rt (ξ i) : A F)) := by
    intro a b hab
    funext i
    exact AdeleRing.algebraMap_injective (𝓞 F) F (congrFun hab i)
  choose f hf using fun (g : GL (Fin 2) E) (ξ : Fin 4 → F) => UpperTheory.ConvolutionTheory.R2.D.act_rat D g ξ
  have hinv : ∀ (g : GL (Fin 2) E) ξ, f g⁻¹ (f g ξ) = ξ := by
    intro g ξ
    apply hinj
    change (fun i => (rt (f g⁻¹ (f g ξ) i) : A F)) = fun i => rt (ξ i)
    rw [← hf g⁻¹ (f g ξ), ← hf g ξ, ← hmul, ← map_mul, inv_mul_cancel, map_one, hone]
  let e : (Fin 4 → F) ≃ (Fin 4 → F) :=
    ⟨f γ⁻¹, f γ, fun ξ => by simpa using hinv γ⁻¹ ξ, hinv γ⟩
  simp only [Th, UpperTheory.ConvolutionTheory.R2.D.ab_nu, inv_one, Complex.ofReal_one, one_mul, ← map_inv, hf]
  exact e.tsum_eq fun ξ => φ fun i => rt (ξ i)
