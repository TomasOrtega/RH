import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacGlueIndicator
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneCo

namespace GlobalTheory.ThK.PlaneCo.BlockRead

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `hle : Submodule.span E (Y.L : Set (Fin n → E)) ≤ LinearMap.range (Matrix.mulVecLin (planeMat H))`. Use `Submodule.span_le.mpr fun z hz => ?_` and prove the remaining obligations. Take `⟨s, t, u, -, -, -, rfl⟩` from `hA.split z hz`. Use `⟨Sum.elim u ![s, t], ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Simplify using `[Matrix.mulVecLin_apply, planeMat, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hle` using `[hL.span_eq_top]`. Introduce `y`. Take `⟨w, hw⟩` from `hle (Submodule.mem_top : y ∈ ⊤)`.

Conclude with `⟨w, by simpa [Matrix.mulVecLin_apply] using hw⟩`.
-/
theorem planeMat_mulVec_surjective {σ : E →ₐ[F] E} {B : Base F E} {n n₁ i₀ i₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁}
    {H : Plane E n n₁} (hL : Y.L.IsLattice E) (hA : H.IsAdapted σ B Y Y₁ i₀ i₁) :
    Function.Surjective (planeMat H).mulVec := by
  have hle : Submodule.span E (Y.L : Set (Fin n → E)) ≤ LinearMap.range (Matrix.mulVecLin (planeMat H)) := by
    refine Submodule.span_le.mpr fun z hz => ?_
    obtain ⟨s, t, u, -, -, -, rfl⟩ := hA.split z hz
    refine ⟨Sum.elim u ![s, t], ?_⟩
    funext i
    simp [Matrix.mulVecLin_apply, planeMat, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
    ring
  rw [hL.span_eq_top] at hle
  intro y
  obtain ⟨w, hw⟩ := hle (Submodule.mem_top : y ∈ ⊤)
  exact ⟨w, by simpa [Matrix.mulVecLin_apply] using hw⟩

/- English proof (translation)
Unfold `planeCoef`. Rewrite using `[dif_pos hr]`. Use `set e : Fin n₁ ⊕ Fin 2 ≃ Fin n := finSumFinEquiv.trans (finCongr hr) with he`. Use `set P := (planeMat H).submatrix id e.symm with hPdef`. Establish `hP : IsUnit P`.

Use `Matrix.mulVec_surjective_iff_isUnit.mp fun y => ?_` and prove the remaining obligations. Take `⟨w, hw⟩` from `hs y`. Use `⟨w ∘ e.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[hPdef, Matrix.submatrix_mulVec_equiv]`. Simplify using `[Function.comp_def, hw]`.

Establish `hPM : planeMat H = P.submatrix id e`. Use extensionality with `i k`. Simplify using `[P]`. Rewrite using `[hPM, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hP), Matrix.submatrix_one_equiv]`.
-/
theorem planeCoef_mul_planeMat {n n₁ : ℕ} (H : Plane E n n₁) (hr : n₁ + 2 = n)
    (hs : Function.Surjective (planeMat H).mulVec) : planeCoef H * planeMat H = 1 := by
  classical
  unfold planeCoef
  rw [dif_pos hr]
  set e : Fin n₁ ⊕ Fin 2 ≃ Fin n := finSumFinEquiv.trans (finCongr hr) with he
  set P := (planeMat H).submatrix id e.symm with hPdef
  have hP : IsUnit P := by
    refine Matrix.mulVec_surjective_iff_isUnit.mp fun y => ?_
    obtain ⟨w, hw⟩ := hs y
    refine ⟨w ∘ e.symm, ?_⟩
    rw [hPdef, Matrix.submatrix_mulVec_equiv]
    simp [Function.comp_def, hw]
  have hPM : planeMat H = P.submatrix id e := by
    ext i k; simp [P]
  rw [hPM, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hP), Matrix.submatrix_one_equiv]

/- English proof (translation)
Establish `h1 : H.ι = (planeMat H).submatrix id Sum.inl` using `by ext i j; simp [planeMat]`. Rewrite using `[← planeCoef_mul_planeMat H hr hs, Matrix.submatrix_mul _ _ id id Sum.inl Function.bijective_id, ← h1]`. Both sides reduce to the same expression.
-/
theorem planeCoef_mul_ι {n n₁ : ℕ} (H : Plane E n n₁) (hr : n₁ + 2 = n)
    (hs : Function.Surjective (planeMat H).mulVec) :
    planeCoef H * H.ι = (1 : Matrix (Fin n₁ ⊕ Fin 2) (Fin n₁ ⊕ Fin 2) E).submatrix id Sum.inl := by
  have h1 : H.ι = (planeMat H).submatrix id Sum.inl := by ext i j; simp [planeMat]
  rw [← planeCoef_mul_planeMat H hr hs, Matrix.submatrix_mul _ _ id id Sum.inl Function.bijective_id, ← h1]
  rfl

end GlobalTheory.ThK.PlaneCo.BlockRead

namespace GlobalTheory.ThK.PlaneCo.BlockRead

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' _ hX hW hH hH' z`. Establish `q1` using `planeCoef_mul_ι H hH.rank.symm (planeMat_mulVec_surjective hX.lat hH)`. Establish `q2` using `planeCoef_mul_ι H' hH'.rank.symm (planeMat_mulVec_surjective hW.lat hH')`. Establish `hco : coefLin H H' (incM F H.ι * z * (incM F H'.ι)ᵀ) = incM F (planeCoef H * H.ι) * z * (incM F (planeCoef H' * H'.ι))ᵀ`. Simplify using `only [coefLin, LinearMap.coe_mk, AddHom.coe_mk, incM, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]`.

Rewrite `hco` using `[q1, q2]`. Establish `hin : ∀ a b, coefLin H H' (incM F H.ι * z * (incM F H'.ι)ᵀ) (.inl a) (.inl b) = z a b`. Introduce `a b`. Rewrite using `[hco]`. Simplify using `[Matrix.mul_apply, incM, Matrix.one_apply]`.

Establish `hr1 : ∀ t l, coefLin H H' (incM F H.ι * z * (incM F H'.ι)ᵀ) (.inr t) l = 0`. Introduce `t l`. Rewrite using `[hco]`. Simplify using `[Matrix.mul_apply, incM, Matrix.one_apply]`. Establish `hr2 : ∀ k t, coefLin H H' (incM F H.ι * z * (incM F H'.ι)ᵀ) k (.inr t) = 0`.

Introduce `k t`. Rewrite using `[hco]`. Simplify using `[Matrix.mul_apply, incM, Matrix.one_apply]`. Establish `hs : ∀ k, sI H H' (incM F H.ι * z * (incM F H'.ι)ᵀ) k = 0`. Introduce and unpack `(j | a)`.

Conclude with `hr1 _ _`. Conclude with `hr2 _ _`. Establish `ht : ∀ k, tI H H' (incM F H.ι * z * (incM F H'.ι)ᵀ) k = 0`. Introduce and unpack `(j | a)`. Conclude with `hr1 _ _`.

Conclude with `hr2 _ _`. Establish `hp : ∀ k, pairI σ X W H H' (incM F H.ι * z * (incM F H'.ι)ᵀ) k = 0`. Introduce `k`. Simplify using `[pairI, ht]`. Simplify using `only [planeT, LinearMap.coe_mk, AddHom.coe_mk]`.

Use `Prod.ext (Prod.ext ?_ ?_) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `k`. Simplify using `[hs]`. Use function extensionality and compare the values at `k`. Simplify using `[hp]`.

Use extensionality with `a b`. Simplify using `[hin]`.
-/
theorem planeT_block : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (H : Plane E n n₁) (H' : Plane E d d₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ z : Matrix (Fin n₁) (Fin d₁) (AE F E),
    planeT σ X W H H' (incM F H.ι * z * (incM F H'.ι)ᵀ) = ((0, 0), z) := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' _ hX hW hH hH' z
  have q1 := planeCoef_mul_ι H hH.rank.symm (planeMat_mulVec_surjective hX.lat hH)
  have q2 := planeCoef_mul_ι H' hH'.rank.symm (planeMat_mulVec_surjective hW.lat hH')
  have hco : coefLin H H' (incM F H.ι * z * (incM F H'.ι)ᵀ) =
      incM F (planeCoef H * H.ι) * z * (incM F (planeCoef H' * H'.ι))ᵀ := by
    simp only [coefLin, LinearMap.coe_mk, AddHom.coe_mk, incM, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [q1, q2] at hco
  have hin : ∀ a b, coefLin H H' (incM F H.ι * z * (incM F H'.ι)ᵀ) (.inl a) (.inl b) = z a b := by
    intro a b
    rw [hco]
    simp [Matrix.mul_apply, incM, Matrix.one_apply]
  have hr1 : ∀ t l, coefLin H H' (incM F H.ι * z * (incM F H'.ι)ᵀ) (.inr t) l = 0 := by
    intro t l
    rw [hco]
    simp [Matrix.mul_apply, incM, Matrix.one_apply]
  have hr2 : ∀ k t, coefLin H H' (incM F H.ι * z * (incM F H'.ι)ᵀ) k (.inr t) = 0 := by
    intro k t
    rw [hco]
    simp [Matrix.mul_apply, incM, Matrix.one_apply]
  have hs : ∀ k, sI H H' (incM F H.ι * z * (incM F H'.ι)ᵀ) k = 0 := by
    rintro (j | a)
    · exact hr1 _ _
    · exact hr2 _ _
  have ht : ∀ k, tI H H' (incM F H.ι * z * (incM F H'.ι)ᵀ) k = 0 := by
    rintro (j | a)
    · exact hr1 _ _
    · exact hr2 _ _
  have hp : ∀ k, pairI σ X W H H' (incM F H.ι * z * (incM F H'.ι)ᵀ) k = 0 := by
    intro k
    simp [pairI, ht]
  simp only [planeT, LinearMap.coe_mk, AddHom.coe_mk]
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · funext k; simp [hs]
  · funext k; simp [hp]
  · ext a b; simp [hin]

end GlobalTheory.ThK.PlaneCo.BlockRead
