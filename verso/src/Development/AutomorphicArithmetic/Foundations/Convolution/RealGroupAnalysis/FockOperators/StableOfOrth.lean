import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CapCentral

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

section

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem wW_val : (wW F).1 = !![0, 1; -1, 0] := rfl

/- English proof (translation)
Rewrite using `[Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, wW_val]`. Simplify using the standard rewrite rules.
-/
private theorem wInv_val : ((wW F)⁻¹).1 = !![0, -1; 1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, wW_val]
  simp

/- English proof (translation)
Introduce `i j`. Rewrite using `[wW_val]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]`.
-/
private theorem orth_w : InfOrth (wW F) := by
  intro i j
  rw [wW_val]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Introduce `i j`. Rewrite using `[wInv_val]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]`.
-/
private theorem orth_wInv : InfOrth (wW F)⁻¹ := by
  intro i j
  rw [wInv_val]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Rewrite using `[Matrix.mem_unitaryGroup_iff]`. Use `ext1 i j`. Establish `e : TR.pInf F ((h.1 * h.1ᵀ) i j) = TR.pInf F ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j)` using `congrArg (TR.infEq F).symm (ho i j)`. Establish `e1 : ((GeneralLinearGroup.map (TR.pInf F) (gl h)).val * star (GeneralLinearGroup.map (TR.pInf F) (gl h)).val) i j = TR.pInf F ((h.1 * h.1ᵀ) i j)`. Simplify using `only [Matrix.mul_apply, map_sum, map_mul, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, star_trivial, Matrix.transpose_apply]`.

Both sides reduce to the same expression. Establish `e2 : TR.pInf F ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j) = (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Matrix.one_apply_ne hij]`. Rewrite using `[e1, e, e2]`.
-/
private theorem orth_unitary (h : G1 F) (ho : InfOrth h) :
    (GeneralLinearGroup.map (TR.pInf F) (gl h)).val ∈ Matrix.unitaryGroup (Fin 2) (TR.Rinf F) := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext1 i j
  have e : TR.pInf F ((h.1 * h.1ᵀ) i j) = TR.pInf F ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j) :=
    congrArg (TR.infEq F).symm (ho i j)
  have e1 : ((GeneralLinearGroup.map (TR.pInf F) (gl h)).val * star (GeneralLinearGroup.map (TR.pInf F) (gl h)).val) i j =
      TR.pInf F ((h.1 * h.1ᵀ) i j) := by
    simp only [Matrix.mul_apply, map_sum, map_mul, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, star_trivial,
      Matrix.transpose_apply]
    rfl
  have e2 : TR.pInf F ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j) = (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) i j := by
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  rw [e1, e, e2]

/- English proof (translation)
Rewrite using `[← map_mul, TR.infGL_mul_finGL]`.
-/
private theorem rt_split (g : GL (Fin 2) (A F)) :
    TR.rt F 2 g = TR.rt F 2 (TR.infGL F 2 (GeneralLinearGroup.map (TR.pInf F) g)) *
      TR.rt F 2 (finGL F 2 (GeneralLinearGroup.map (pFin F) g)) := by
  rw [← map_mul, TR.infGL_mul_finGL]

/- English proof (translation)
Rewrite using `[rt_split, Module.End.mul_apply]`. Establish `h1` using `π.stable (.fin (GeneralLinearGroup.map (pFin F) (gl h))) f hf`. Establish `h2` using `π.stable (.cpt ⟨_, orth_unitary h ho⟩) _ h1`. Establish `e : Unitary.toUnits (⟨_, orth_unitary h ho⟩ : TR.Kinf F 2) = GeneralLinearGroup.map (TR.pInf F) (gl h)` using `Units.ext rfl`. Express the relevant statement in the definitionally equal form `TR.rt F 2 (TR.infGL F 2 (Unitary.toUnits (⟨_, orth_unitary h ho⟩ : TR.Kinf F 2))) (TR.rt F 2 (finGL F 2 (GeneralLinearGroup.map (pFin F) (gl h))) f) ∈ π.V at h2`.

Rewrite `h2` using `[e]`. Then use the resulting hypothesis.
-/
private theorem stable_of_orth (π : TR.CuspSub F 2) {h : G1 F} (ho : InfOrth h) {f : TR.Sm F 2} (hf : f ∈ π.V) :
    TR.rt F 2 (gl h) f ∈ π.V := by
  rw [rt_split, Module.End.mul_apply]
  have h1 := π.stable (.fin (GeneralLinearGroup.map (pFin F) (gl h))) f hf
  have h2 := π.stable (.cpt ⟨_, orth_unitary h ho⟩) _ h1
  have e : Unitary.toUnits (⟨_, orth_unitary h ho⟩ : TR.Kinf F 2) = GeneralLinearGroup.map (TR.pInf F) (gl h) :=
    Units.ext rfl
  change TR.rt F 2 (TR.infGL F 2 (Unitary.toUnits (⟨_, orth_unitary h ho⟩ : TR.Kinf F 2)))
    (TR.rt F 2 (finGL F 2 (GeneralLinearGroup.map (pFin F) (gl h))) f) ∈ π.V at h2
  rwa [e] at h2

/- English proof (translation)
Apply the tactic sequence `have hy : (GeneralLinearGroup.map (TR.pInf F) (gl (wW F))).val = !![0, 1; -1, 0] := by ext1 i j fin_cases i <;> fin_cases j <;> simp [wW_val]`. Establish `hyi : ((GeneralLinearGroup.map (TR.pInf F) (gl (wW F)))⁻¹).val = !![0, -1; 1, 0]`. Use `Units.inv_eq_of_mul_eq_one_right ?_` and prove the remaining obligations. Rewrite using `[hy, Matrix.mul_fin_two, Matrix.one_fin_two]`. Simplify using the standard rewrite rules.

Establish `hfin : ∀ k : GL (Fin 2) (Af F), TR.rt F 2 (finGL F 2 k) * TR.Eop v 0 1 = TR.Eop v 0 1 * TR.rt F 2 (finGL F 2 k)` using `fun k => (TR.lie_rt_fin _ k).symm`. Rewrite using `[rt_split (gl (wW F)), mul_assoc, hfin, ← mul_assoc, TR.Cen.rt_Eop, hy, hyi]`. Simplify using `[Fin.sum_univ_two, mul_assoc]`.
-/
private theorem ad_eop (v : InfinitePlace F) :
    TR.rt F 2 (gl (wW F)) * TR.Eop v 0 1 = -(TR.Eop v 1 0 * TR.rt F 2 (gl (wW F))) := by
  have hy : (GeneralLinearGroup.map (TR.pInf F) (gl (wW F))).val = !![0, 1; -1, 0] := by
    ext1 i j
    fin_cases i <;> fin_cases j <;> simp [wW_val]
  have hyi : ((GeneralLinearGroup.map (TR.pInf F) (gl (wW F)))⁻¹).val = !![0, -1; 1, 0] := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hy, Matrix.mul_fin_two, Matrix.one_fin_two]
    simp
  have hfin : ∀ k : GL (Fin 2) (Af F), TR.rt F 2 (finGL F 2 k) * TR.Eop v 0 1 = TR.Eop v 0 1 * TR.rt F 2 (finGL F 2 k) :=
    fun k => (TR.lie_rt_fin _ k).symm
  rw [rt_split (gl (wW F)), mul_assoc, hfin, ← mul_assoc, TR.Cen.rt_Eop, hy, hyi]
  simp [Fin.sum_univ_two, mul_assoc]

end

/- English proof (translation)
Introduce `F _ _ _`. Conclude with `⟨fun π f hf => ⟨stable_of_orth π orth_w hf, stable_of_orth π orth_wInv hf⟩, ad_eop, orth_wInv⟩`.
-/
theorem UpperTheory.ConvolutionTheory.R2.Fo.adW :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], (∀ π : TR.CuspSub F 2, ∀ f ∈ π.V, TR.rt F 2 (gl (wW F)) f ∈ π.V ∧ TR.rt F 2 (gl (wW F)⁻¹) f ∈ π.V) ∧
    (∀ v, TR.rt F 2 (gl (wW F)) * TR.Eop v 0 1 = -(TR.Eop v 1 0 * TR.rt F 2 (gl (wW F)))) ∧ InfOrth (wW F)⁻¹ := by
  intro F _ _ _
  exact ⟨fun π f hf => ⟨stable_of_orth π orth_w hf, stable_of_orth π orth_wInv hf⟩, ad_eop, orth_wInv⟩
