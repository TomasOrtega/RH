import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ThMSymmApply

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Rewrite using `[← th_sigR_eq]`. Conclude with `th_sigR_incl x`.
-/
theorem th_cA_incl (x : E) : cA σ (inclR (F := F) (E := E) (AF F) x) = inclR (F := F) (E := E) (AF F) (σ x) := by
  rw [← th_sigR_eq]; exact th_sigR_incl x

/- English proof (translation)
Establish `h1 : (incM F X).map (cA σ) = incM F (X.map σ)`. Use extensionality with `i j`. Simplify using `only [incM, Matrix.map_apply]`. Conclude with `th_cA_incl _`. Rewrite using `[SD.gram, h1]`.

Simplify using `only [incM, Matrix.transpose_map, Matrix.map_mul]`.
-/
theorem th_gram_incM (d : SD σ) (X : Matrix (Fin d.m) (Fin d.n) E) :
    d.gram (incM F X) (incM F X) = incM F (Xᵀ * d.A.J * X.map σ) := by
  have h1 : (incM F X).map (cA σ) = incM F (X.map σ) := by
    ext i j; simp only [incM, Matrix.map_apply]; exact th_cA_incl _
  rw [SD.gram, h1]
  simp only [incM, Matrix.transpose_map, Matrix.map_mul]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [HeckeCharacterZeroLocus.SiegelWeilU.gramE, HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, Jd, Matrix.transpose_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, RingHom.coe_coe]`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem th_gramE (d : SD σ) (η : E) (X : Matrix (Fin d.m) (Fin d.n) E) :
    HeckeCharacterZeroLocus.SiegelWeilU.gramE σ (Jd d η) Xᵀ = η • (Xᵀ * d.A.J * X.map σ)ᵀ := by
  ext a b
  simp only [HeckeCharacterZeroLocus.SiegelWeilU.gramE, HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, Jd, Matrix.transpose_apply,
    Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, RingHom.coe_coe]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Establish `hs : ((-2 : ℤ) • incM F T₀ : Matrix (Fin d.n) (Fin d.n) (AE F E)) = incM F ((-2 : ℤ) • T₀)`. Use extensionality with `i j`. Simplify using `only [incM, Matrix.map_apply, Matrix.smul_apply, map_zsmul]`. Rewrite using `[th_gram_incM, th_gramE, Td, hs]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Rewrite using `[th_incM_injective h]`. Use extensionality with `i j`. Simplify using `only [Matrix.smul_apply, Matrix.transpose_apply]`. Simplify using `only [zsmul_eq_mul, smul_eq_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `h`. Use `congr 1`. Use extensionality with `i j`.

Use `congrFun (congrFun h j) i` as an intermediate fact. Simplify using `only [Matrix.smul_apply, Matrix.transpose_apply] at this ⊢`. Simplify using `only [zsmul_eq_mul, smul_eq_mul] at this ⊢`. Move the coercions through the operations in `at this ⊢`. Apply `mul_left_cancel₀ hη` to reduce the goal to its premises.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem th_gram_iff (d : SD σ) {η : E} (hη : η ≠ 0) (T₀ : Matrix (Fin d.n) (Fin d.n) E)
    (X : Matrix (Fin d.m) (Fin d.n) E) :
    d.gram (incM F X) (incM F X) = (-2 : ℤ) • incM F T₀ ↔ HeckeCharacterZeroLocus.SiegelWeilU.gramE σ (Jd d η) Xᵀ = Td η T₀ := by
  have hs : ((-2 : ℤ) • incM F T₀ : Matrix (Fin d.n) (Fin d.n) (AE F E)) = incM F ((-2 : ℤ) • T₀) := by
    ext i j; simp only [incM, Matrix.map_apply, Matrix.smul_apply, map_zsmul]
  rw [th_gram_incM, th_gramE, Td, hs]
  constructor
  · intro h
    rw [th_incM_injective h]
    ext i j
    simp only [Matrix.smul_apply, Matrix.transpose_apply]
    simp only [zsmul_eq_mul, smul_eq_mul]; push_cast; ring
  · intro h
    congr 1
    ext i j
    have := congrFun (congrFun h j) i
    simp only [Matrix.smul_apply, Matrix.transpose_apply] at this ⊢
    simp only [zsmul_eq_mul, smul_eq_mul] at this ⊢
    push_cast at this ⊢
    apply mul_left_cancel₀ hη
    rw [this]; ring

/- English proof (translation)
Use extensionality with `a j`. Simplify using `only [toMx, HeckeCharacterZeroLocus.SiegelWeilU.actTup, HeckeCharacterZeroLocus.SiegelWeilU.ratTup, Matrix.of_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply, incM, Matrix.map_apply, Matrix.transpose_apply, th_inclR_eq]`.
-/
theorem th_toMx_act (d : SD σ) (M : GL (Fin d.m) (AE F E)) (X : Matrix (Fin d.m) (Fin d.n) E) :
    toMx (HeckeCharacterZeroLocus.SiegelWeilU.actTup (AF F) M (HeckeCharacterZeroLocus.SiegelWeilU.ratTup (AF F) Xᵀ)) =
      (M : Matrix (Fin d.m) (Fin d.m) (AE F E)) * incM F X := by
  ext a j
  simp only [toMx, HeckeCharacterZeroLocus.SiegelWeilU.actTup, HeckeCharacterZeroLocus.SiegelWeilU.ratTup, Matrix.of_apply, Matrix.mulVec, dotProduct,
    Matrix.mul_apply, incM, Matrix.map_apply, Matrix.transpose_apply, th_inclR_eq]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ d η hη _`. Use `⟨d.μ.map (thM d hη), thM d hη '' d.D, th_haar d hη, th_fd d hη, ?_⟩` and prove the remaining obligations. Introduce `T T₀ hT Φ _`. Rewrite using `[SD.orb, setAverage_eq, HeckeCharacterZeroLocus.SiegelWeilU.meanC, MeasurableEquiv.map_apply, (thM d hη).preimage_image, (thM d hη).restrict_map, (thM d hη).preimage_image, integral_map_equiv, measureReal_def]`. Use `congr 1`.

Use `integral_congr_ae (ae_of_all _ fun g => ?_)` and prove the remaining obligations. Simplify using `only [HeckeCharacterZeroLocus.SiegelWeilU.thetaS]`. Set `e : {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1} ≃ {X : Fin d.n → Fin d.m → E | HeckeCharacterZeroLocus.SiegelWeilU.gramE σ (Jd d η) X = Td η T₀}` to `{ toFun := fun X => ⟨X.1ᵀ, (th_gram_iff d hη T₀ X.1).1 (hT ▸ X.2)⟩ invFun := fun Y => ⟨Matrix.transpose (Y.1 : Matrix (Fin d.n) (Fin d.m) E), by`. Rewrite using `[hT]`. Conclude with `(th_gram_iff d hη T₀ _).2 Y.2⟩`.

Use `left_inv := fun X => Subtype.ext (Matrix.transpose_transpose _)`. Use `right_inv := fun Y => Subtype.ext (Matrix.transpose_transpose (Y.1 : Matrix (Fin d.n) (Fin d.m) E)) }`. Rewrite using `[← e.tsum_eq]`. Use `tsum_congr fun X => ?_` and prove the remaining obligations. Simplify using `only [e, Equiv.coe_fn_mk]`.

Rewrite using `[th_toMx_act]`. Both sides reduce to the same expression.
-/
theorem thetaDict : ThetaDict := by
  intro F E _ _ _ _ _ σ d η hη _
  refine ⟨d.μ.map (thM d hη), thM d hη '' d.D, th_haar d hη, th_fd d hη, ?_⟩
  intro T T₀ hT Φ _
  rw [SD.orb, setAverage_eq, HeckeCharacterZeroLocus.SiegelWeilU.meanC, MeasurableEquiv.map_apply, (thM d hη).preimage_image,
    (thM d hη).restrict_map, (thM d hη).preimage_image, integral_map_equiv, measureReal_def]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  simp only [HeckeCharacterZeroLocus.SiegelWeilU.thetaS]
  let e : {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1} ≃
      {X : Fin d.n → Fin d.m → E | HeckeCharacterZeroLocus.SiegelWeilU.gramE σ (Jd d η) X = Td η T₀} :=
    { toFun := fun X => ⟨X.1ᵀ, (th_gram_iff d hη T₀ X.1).1 (hT ▸ X.2)⟩
      invFun := fun Y => ⟨Matrix.transpose (Y.1 : Matrix (Fin d.n) (Fin d.m) E), by
        rw [hT]; exact (th_gram_iff d hη T₀ _).2 Y.2⟩
      left_inv := fun X => Subtype.ext (Matrix.transpose_transpose _)
      right_inv := fun Y => Subtype.ext (Matrix.transpose_transpose (Y.1 : Matrix (Fin d.n) (Fin d.m) E)) }
  rw [← e.tsum_eq]
  refine tsum_congr fun X => ?_
  simp only [e, Equiv.coe_fn_mk]
  rw [th_toMx_act]
  rfl

end PositivityTheory.SiegelWeilFormula.KWhit

end
