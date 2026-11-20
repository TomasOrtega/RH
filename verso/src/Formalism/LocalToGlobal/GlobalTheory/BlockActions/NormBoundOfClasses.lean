import Formalism.LocalToGlobal.GlobalTheory.BlockActions.NormBoundOfClassesFrames
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ExistsOnOfPosDef

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix
open scoped ComplexOrder

variable {D : D7}

/- English proof (translation)
The claim follows from `D.sp.cm.cmUnram.2.1 ι x`.
-/
theorem sig_at (ι : D.host.E →+* ℂ) (x : D.host.E) : ι (sigD D x) = starRingEnd ℂ (ι x) :=
  D.sp.cm.cmUnram.2.1 ι x

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply, RingHom.coe_coe]`. Rewrite using `[sig_at]`. Both sides reduce to the same expression.
-/
theorem map_cT_at {m n : Type} (ι : D.host.E →+* ℂ) (M : Matrix m n D.host.E) :
    ((M.map (sigD D : D.host.E →+* D.host.E))ᵀ).map ι = (M.map ι)ᴴ := by
  ext i j
  simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply, RingHom.coe_coe]
  rw [sig_at]
  rfl

/- English proof (translation)
Take `⟨C, hC, -, -⟩` from `(Tf.val D.R.m le_rfl (Or.inr rfl)).de`. Establish `hC' : ((C.1.map (sigD D : D.host.E →+* D.host.E))ᵀ * C.1) = gramN D D.R.m le_rfl` using `hC`. Use `set A : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ := C.1.map ι with hA`. Establish `hG : (gramN D D.R.m le_rfl).map ι = Aᴴ * A`. Rewrite using `[← hC', Matrix.map_mul, map_cT_at, hA]`.

Establish `hinj : Function.Injective A.mulVec`. Introduce `x y hxy`. Establish `hCi : IsUnit C.1.det` using `(Matrix.isUnit_iff_isUnit_det _).mp C.isUnit`. Establish `h1 : (C.1⁻¹ * C.1).map ι = 1`. Rewrite using `[Matrix.nonsing_inv_mul _ hCi, Matrix.map_one _ (map_zero _) (map_one _)]`.

Establish `h2` using `congrArg (fun v => ((C.1⁻¹).map ι) *ᵥ v) hxy`. Simplify using `only [Matrix.mulVec_mulVec, hA, ← Matrix.map_mul, h1, Matrix.one_mulVec] at h2`. Conclude with `h2`. Rewrite using `[hG]`. Conclude with `Matrix.PosDef.conjTranspose_mul_self A hinj`.
-/
theorem gramN_posDef_at {Ch : ℕ → Type} {u : D.what₂.Word} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (Tf : FormsTiedSym D u Ch chOf)
    (ι : D.host.E →+* ℂ) : ((gramN D D.R.m le_rfl).map ι).PosDef := by
  obtain ⟨C, hC, -, -⟩ := (Tf.val D.R.m le_rfl (Or.inr rfl)).de
  have hC' : ((C.1.map (sigD D : D.host.E →+* D.host.E))ᵀ * C.1) = gramN D D.R.m le_rfl := hC
  set A : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ := C.1.map ι with hA
  have hG : (gramN D D.R.m le_rfl).map ι = Aᴴ * A := by
    rw [← hC', Matrix.map_mul, map_cT_at, hA]
  have hinj : Function.Injective A.mulVec := by
    intro x y hxy
    have hCi : IsUnit C.1.det := (Matrix.isUnit_iff_isUnit_det _).mp C.isUnit
    have h1 : (C.1⁻¹ * C.1).map ι = 1 := by
      rw [Matrix.nonsing_inv_mul _ hCi, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 := congrArg (fun v => ((C.1⁻¹).map ι) *ᵥ v) hxy
    simp only [Matrix.mulVec_mulVec, hA, ← Matrix.map_mul, h1, Matrix.one_mulVec] at h2
    exact h2
  rw [hG]
  exact Matrix.PosDef.conjTranspose_mul_self A hinj

/- English proof (translation)
Take `⟨C, hC, -, -⟩` from `(Tf.val D.R.m le_rfl (Or.inr rfl)).de`. Establish `hC' : ((C.1.map (sigD D : D.host.E →+* D.host.E))ᵀ * C.1) = gramN D D.R.m le_rfl` using `hC`. Take `⟨L, hL⟩` from `iXm_leftInv D`. Use `set A : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m - 1)) ℂ := (C.1 * iXm D).map ι with hA`. Establish `hG : (gramP D).map ι = Aᴴ * A`.

Establish `e1 : ((iXm D).map (sigD D : D.host.E →+* D.host.E))ᵀ * (((C.1).map (sigD D : D.host.E →+* D.host.E))ᵀ * C.1) * iXm D = ((C.1 * iXm D).map (sigD D : D.host.E →+* D.host.E))ᵀ * (C.1 * iXm D)`. Rewrite using `[Matrix.map_mul, Matrix.transpose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[gramP_eq, ← hC', e1, Matrix.map_mul, map_cT_at, hA]`. Establish `hinj : Function.Injective A.mulVec`.

Introduce `x y hxy`. Establish `hCi : IsUnit C.1.det` using `(Matrix.isUnit_iff_isUnit_det _).mp C.isUnit`. Establish `h1 : ((L * C.1⁻¹) * (C.1 * iXm D)).map ι = 1`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc C.1⁻¹, Matrix.nonsing_inv_mul _ hCi, Matrix.one_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `h2` using `congrArg (fun v => ((L * C.1⁻¹).map ι) *ᵥ v) hxy`.

Simplify using `only [Matrix.mulVec_mulVec, hA, ← Matrix.map_mul, h1, Matrix.one_mulVec] at h2`. Conclude with `h2`. Rewrite using `[hG]`. Conclude with `Matrix.PosDef.conjTranspose_mul_self A hinj`.
-/
theorem gramP_posDef_at {Ch : ℕ → Type} {u : D.what₂.Word} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (Tf : FormsTiedSym D u Ch chOf)
    (ι : D.host.E →+* ℂ) : ((gramP D).map ι).PosDef := by
  obtain ⟨C, hC, -, -⟩ := (Tf.val D.R.m le_rfl (Or.inr rfl)).de
  have hC' : ((C.1.map (sigD D : D.host.E →+* D.host.E))ᵀ * C.1) = gramN D D.R.m le_rfl := hC
  obtain ⟨L, hL⟩ := iXm_leftInv D
  set A : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m - 1)) ℂ := (C.1 * iXm D).map ι with hA
  have hG : (gramP D).map ι = Aᴴ * A := by
    have e1 : ((iXm D).map (sigD D : D.host.E →+* D.host.E))ᵀ * (((C.1).map (sigD D : D.host.E →+* D.host.E))ᵀ * C.1) * iXm D =
        ((C.1 * iXm D).map (sigD D : D.host.E →+* D.host.E))ᵀ * (C.1 * iXm D) := by
      rw [Matrix.map_mul, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    rw [gramP_eq, ← hC', e1, Matrix.map_mul, map_cT_at, hA]
  have hinj : Function.Injective A.mulVec := by
    intro x y hxy
    have hCi : IsUnit C.1.det := (Matrix.isUnit_iff_isUnit_det _).mp C.isUnit
    have h1 : ((L * C.1⁻¹) * (C.1 * iXm D)).map ι = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc C.1⁻¹, Matrix.nonsing_inv_mul _ hCi, Matrix.one_mul, hL,
        Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 := congrArg (fun v => ((L * C.1⁻¹).map ι) *ᵥ v) hxy
    simp only [Matrix.mulVec_mulVec, hA, ← Matrix.map_mul, h1, Matrix.one_mulVec] at h2
    exact h2
  rw [hG]
  exact Matrix.PosDef.conjTranspose_mul_self A hinj

/- English proof (translation)
Introduce `D u Ch chOf Tf s`. Prove the components needed by the constructor for the conclusion. Establish `h` using `fun τ => exists_on_of_posDef (gramC (gramN D D.R.m le_rfl) (embS D s) τ) (gramN_posDef_at Tf (embS D s τ)) choose o ho1 ho2 using h`. Conclude with `⟨⟨o, ho1⟩, fun τ => Or.inl (ho2 τ)⟩`. Establish `h` using `fun τ => exists_on_of_posDef (gramC (gramP D) (embS D s) τ) (gramP_posDef_at Tf (embS D s τ)) choose o ho1 ho2 using h`.

Conclude with `⟨⟨o, ho1⟩, fun τ => Or.inl (ho2 τ)⟩`.
-/
theorem framesAt : FramesAt := by
  intro D u Ch chOf Tf s
  constructor
  · have h := fun τ => exists_on_of_posDef (gramC (gramN D D.R.m le_rfl) (embS D s) τ) (gramN_posDef_at Tf (embS D s τ))
    choose o ho1 ho2 using h
    exact ⟨⟨o, ho1⟩, fun τ => Or.inl (ho2 τ)⟩
  · have h := fun τ => exists_on_of_posDef (gramC (gramP D) (embS D s) τ) (gramP_posDef_at Tf (embS D s τ))
    choose o ho1 ho2 using h
    exact ⟨⟨o, ho1⟩, fun τ => Or.inl (ho2 τ)⟩

/- English proof (translation)
The claim follows from `norm_bound_of_classes_frames h1 h2 framesAt hC`.
-/
theorem norm_bound_of_classes (h1 : ClassMapInjective) (h2 : StabiliserMapBijective) (hC : NormClsAt) : NormBoundAtInfinity :=
  norm_bound_of_classes_frames h1 h2 framesAt hC

end Formalism.L2.GlobalTheoryTheory.Br
