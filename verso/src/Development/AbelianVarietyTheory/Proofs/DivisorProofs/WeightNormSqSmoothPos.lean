import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
open Matrix Complex ComplexConjugate GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram
open scoped ComplexOrder ContDiff

namespace GlobalTheory.WeightSmooth

/- English proof (translation)
Introduce `E _ _ _ _ _ ι _ n U H Y π A hH hA y hy lam`. Establish `hπy : π y ∈ U` using `hA.mapsTo hy`. Establish `hYn : Y ∈ nhds y` using `hA.isOpen.mem_nhds hy`. Establish `hπ : ContDiffAt ℝ ∞ π y` using `((hA.hol_proj.contDiffAt hYn).restrict_scalars ℝ)`. Establish `hHπ : MContDiffAt ∞ (fun x => H (π x)) y` using `fun a b => ((hH.isHermFrame.mContDiffAt hπy) a b).comp y hπ`.

Establish `hAm : MContDiffAt ∞ A y` using `fun a b => ((hA.hol_frame a b).contDiffAt hYn).restrict_scalars ℝ`. Establish `hG : MContDiffAt ∞ (adaptedGram H π A) y` using `(hAm.transpose.mul hHπ).mul hAm.conjTranspose.transpose`. Establish `hpos : (adaptedGram H π A y).PosDef`. Establish `hu : IsUnit (A y)ᵀ` using `(Matrix.isUnit_iff_isUnit_det _).2 (by`. Rewrite using `[det_transpose]`.

Conclude with `hA.isUnit y hy)`. Use `(hH.posDef (π y) hπy).mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hu)` as an intermediate fact. Use `this using 2` and compare the differences between its conclusion and the goal. Use extensionality with `a b`. Both sides reduce to the same expression.

Establish `hi : ∀ i, ContDiffAt ℝ ∞ (fun x => (lineGram H π A i x () ()).re) y ∧ 0 < (lineGram H π A i y () ()).re`. Introduce `i`. Establish `hstep : MContDiffAt ∞ (fun x => stepGram (adaptedGram H π A x) i) y` using `hG.submatrix _ _`. Establish `hsp : (stepGram (adaptedGram H π A y) i).PosDef`. Use `hpos.submatrix ?_` and prove the remaining obligations.

Introduce and unpack `(a | a) (b | b) hab`. Conclude with `congrArg _ (Fin.castLE_injective i.2.le hab)`. Conclude with `absurd (congrArg Fin.val hab) a.2.ne`. Conclude with `absurd (congrArg Fin.val hab) b.2.ne'`. Both sides reduce to the same expression.

Establish `hsub : IsUnit (subGram (stepGram (adaptedGram H π A y) i)).det`. Establish `: (subGram (stepGram (adaptedGram H π A y) i)).PosDef` using `hsp.submatrix Sum.inl_injective`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).1 this.isUnit`. Establish `hq` using `(hstep.quotGram hsub) () ()`. Use `⟨reCLM.contDiff.contDiffAt.comp y hq, ?_⟩` and prove the remaining obligations.

Establish `h1` using `(posDef_gradedGram hpos i)`. Establish `h2 : 0 < gradedGram (adaptedGram H π A y) i () ()` using `h1.diag_pos`. Conclude with `(Complex.pos_iff.1 h2).1`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `weightNormSq`.

Use `contDiffAt_prod fun i _ => ?_` and prove the remaining obligations. Conclude with `(((hi i).1.of_le (by norm_cast)).rpow_const_of_ne (hi i).2.ne')`. Conclude with `Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hi i).2 _`.
-/
theorem weightNormSq_contDiffAt_pos : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [FiniteDimensional ℂ E] (ι : Type) [Fintype ι] (n : ℕ) (U : Set (ι → ℂ))
    (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (Y : Set E) (π : E → ι → ℂ)
    (A : E → Matrix (Fin n) (Fin n) ℂ),
    IsPosFrame U H → IsFlagFamily Y U π A → ∀ y ∈ Y, ∀ lam : Fin n → ℝ,
      ContDiffAt ℝ 2 (weightNormSq H π A lam) y ∧ 0 < weightNormSq H π A lam y := by
  intro E _ _ _ _ _ ι _ n U H Y π A hH hA y hy lam
  have hπy : π y ∈ U := hA.mapsTo hy
  have hYn : Y ∈ nhds y := hA.isOpen.mem_nhds hy

  have hπ : ContDiffAt ℝ ∞ π y := ((hA.hol_proj.contDiffAt hYn).restrict_scalars ℝ)
  have hHπ : MContDiffAt ∞ (fun x => H (π x)) y := fun a b =>
    ((hH.isHermFrame.mContDiffAt hπy) a b).comp y hπ
  have hAm : MContDiffAt ∞ A y := fun a b => ((hA.hol_frame a b).contDiffAt hYn).restrict_scalars ℝ
  have hG : MContDiffAt ∞ (adaptedGram H π A) y :=
    (hAm.transpose.mul hHπ).mul hAm.conjTranspose.transpose

  have hpos : (adaptedGram H π A y).PosDef := by
    have hu : IsUnit (A y)ᵀ := (Matrix.isUnit_iff_isUnit_det _).2 (by
      rw [det_transpose]; exact hA.isUnit y hy)
    have := (hH.posDef (π y) hπy).mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hu)
    convert this using 2
    ext a b; rfl
  have hi : ∀ i, ContDiffAt ℝ ∞ (fun x => (lineGram H π A i x () ()).re) y ∧
      0 < (lineGram H π A i y () ()).re := by
    intro i
    have hstep : MContDiffAt ∞ (fun x => stepGram (adaptedGram H π A x) i) y :=
      hG.submatrix _ _
    have hsp : (stepGram (adaptedGram H π A y) i).PosDef := by
      refine hpos.submatrix ?_
      rintro (a | a) (b | b) hab
      · exact congrArg _ (Fin.castLE_injective i.2.le hab)
      · exact absurd (congrArg Fin.val hab) a.2.ne
      · exact absurd (congrArg Fin.val hab) b.2.ne'
      · rfl
    have hsub : IsUnit (subGram (stepGram (adaptedGram H π A y) i)).det := by
      have : (subGram (stepGram (adaptedGram H π A y) i)).PosDef :=
        hsp.submatrix Sum.inl_injective
      exact (Matrix.isUnit_iff_isUnit_det _).1 this.isUnit
    have hq := (hstep.quotGram hsub) () ()
    refine ⟨reCLM.contDiff.contDiffAt.comp y hq, ?_⟩
    have h1 := (posDef_gradedGram hpos i)
    have h2 : 0 < gradedGram (adaptedGram H π A y) i () () := h1.diag_pos
    exact (Complex.pos_iff.1 h2).1
  refine ⟨?_, ?_⟩
  · unfold weightNormSq
    refine contDiffAt_prod fun i _ => ?_
    exact (((hi i).1.of_le (by norm_cast)).rpow_const_of_ne (hi i).2.ne')
  · exact Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hi i).2 _

end GlobalTheory.WeightSmooth
