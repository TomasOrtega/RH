import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryGroupSurjectsGeneralLinearRight
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.UnitaryInjAtPlace

open GlobalTheory.EmbChart GlobalTheory.LeviAtPlace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul a x => rfl`.
-/
theorem compFin_cA (σ : E →ₐ[F] E) (v : Pl F) (x : AE F E) :
    compFin F E v (cA σ x) = sigR (Fv F v) σ (compFin F E v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `evFin F v 1 ⊗ₜ[F] x = (1 : Fv F v) ⊗ₜ[F] x`. Rewrite using `[map_one]`.
-/
theorem compFin_inclR (v : Pl F) (x : E) :
    compFin F E v (inclR (F := F) (AF F) x) = inclR (Fv F v) x := by
  change evFin F v 1 ⊗ₜ[F] x = (1 : Fv F v) ⊗ₜ[F] x
  rw [map_one]

/- English proof (translation)
Establish `h0 : evFin F v (1 - atPlace v 1) = 0` using `by rw [map_sub, map_one, evFin_atPlace, sub_self]`. Establish `h1` using `hx _ h0`. Rewrite `h1` using `[sub_smul, one_smul, sub_eq_zero]`. Establish `h2 : tensAt E v 1 = algebraMap (AF F) (AE F E) (atPlace v 1)`. Rewrite using `[Algebra.TensorProduct.one_def, tensAt_tmul, Algebra.TensorProduct.algebraMap_apply]`.

Both sides reduce to the same expression. Rewrite using `[← one_mul (compFin F E v x), ← tensAt_mul_right, h2, ← Algebra.smul_def]`. Conclude with `h1`.
-/
theorem eq_tensAt_of_at (v : Pl F) (x : AE F E) (hx : At (evFin F v) x) :
    x = tensAt E v (compFin F E v x) := by
  have h0 : evFin F v (1 - atPlace v 1) = 0 := by rw [map_sub, map_one, evFin_atPlace, sub_self]
  have h1 := hx _ h0
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  have h2 : tensAt E v 1 = algebraMap (AF F) (AE F E) (atPlace v 1) := by
    rw [Algebra.TensorProduct.one_def, tensAt_tmul, Algebra.TensorProduct.algebraMap_apply]
    rfl
  rw [← one_mul (compFin F E v x), ← tensAt_mul_right, h2, ← Algebra.smul_def]
  exact h1

/- English proof (translation)
Use extensionality with `i j`. Establish `hij : At (evFin F v) (z i j)` using `fun u hu => by`. Use `congrFun (congrFun (hz u hu) i) j` as an intermediate fact. Simplify using `using this`. Rewrite using `[eq_tensAt_of_at v _ hij]`.

Use `congrFun (congrFun h0 i) j` as an intermediate fact. Simplify using `only [Matrix.map_apply, Matrix.zero_apply] at this`. Rewrite using `[this, map_zero, Matrix.zero_apply]`.
-/
theorem mat_eq_zero_of_at {n : ℕ} (v : Pl F) (z : Matrix (Fin n) (Fin n) (AE F E)) (hz : At (evFin F v) z)
    (h0 : z.map (compFin F E v) = 0) : z = 0 := by
  ext i j
  have hij : At (evFin F v) (z i j) := fun u hu => by
    have := congrFun (congrFun (hz u hu) i) j
    simpa using this
  rw [eq_tensAt_of_at v _ hij]
  have := congrFun (congrFun h0 i) j
  simp only [Matrix.map_apply, Matrix.zero_apply] at this
  rw [this, map_zero, Matrix.zero_apply]

/- English proof (translation)
Establish `hm : (mat h)ᵀ * incM F J * (mat h).map (cA σ) = incM F J` using `h.2`. Establish `h1` using `congrArg (fun M => (M.map (compFin F E v)).map (splitProj t)) hm`. Simplify using `only [Matrix.map_mul, Matrix.transpose_map] at h1`. Establish `e1 : ((incM F J).map (compFin F E v)).map (splitProj t) = J.map t`. Use extensionality with `i j`.

Simplify using `only [incM, Matrix.map_apply]`. Rewrite using `[compFin_inclR, splitProj_inclR]`. Establish `e2 : (((mat h).map (cA σ)).map (compFin F E v)).map (splitProj t) = (mat h).map (piW (t.comp σ))`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply]`.

Rewrite using `[compFin_cA, ← splitProj_comp]`. Both sides reduce to the same expression. Establish `e3 : ((mat h)ᵀ.map (compFin F E v)).map (splitProj t) = ((mat h).map (piW t))ᵀ`. Use extensionality with `i j`. Both sides reduce to the same expression.

Rewrite `h1` using `[e1, e2]`. Rewrite using `[← e3]`. Conclude with `h1`.
-/
theorem unitary_at_components {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (v : Pl F)
    (t : E →ₐ[F] Fv F v) (h : UA σ J) :
    ((mat h).map (piW t))ᵀ * J.map t * (mat h).map (piW (t.comp σ)) = J.map t := by
  have hm : (mat h)ᵀ * incM F J * (mat h).map (cA σ) = incM F J := h.2
  have h1 := congrArg (fun M => (M.map (compFin F E v)).map (splitProj t)) hm
  simp only [Matrix.map_mul, Matrix.transpose_map] at h1
  have e1 : ((incM F J).map (compFin F E v)).map (splitProj t) = J.map t := by
    ext i j
    simp only [incM, Matrix.map_apply]
    rw [compFin_inclR, splitProj_inclR]
  have e2 : (((mat h).map (cA σ)).map (compFin F E v)).map (splitProj t) = (mat h).map (piW (t.comp σ)) := by
    ext i j
    simp only [Matrix.map_apply]
    rw [compFin_cA, ← splitProj_comp]
    rfl
  have e3 : ((mat h)ᵀ.map (compFin F E v)).map (splitProj t) = ((mat h).map (piW t))ᵀ := by
    ext i j
    rfl
  rw [e1, e2] at h1
  rw [← e3]
  exact h1

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' hTr v _ t h₁ hh₁ h₂ hh₂ heq`. Establish `hcm` using `hTr.base.cm`. Establish `hJ : IsUnit (G.W.J.map t).det`. Take `⟨φ⟩ : Nonempty (F →+* ℂ)` from `inferInstance`. Establish `h0` using `det_ne_zero_of_sig (hTr.geo.hW.sig (InfinitePlace.mk φ))`.

Establish `h1 : G.W.J.det ≠ 0` using `fun e => h0 (by`. Rewrite using `[Matrix.det_smul, show G.W.J.map _ = RingHom.mapMatrix _ G.W.J from rfl, ← RingHom.map_det, e, map_zero, mul_zero])`. Rewrite using `[show G.W.J.map t = (t : E →+* Fv F v).mapMatrix G.W.J from rfl, ← RingHom.map_det]`. Conclude with `isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)`. Establish `u₁` using `unitary_at_components v t h₁`.

Establish `u₂` using `unitary_at_components v t h₂`. Rewrite `u₁` using `[heq]`. Use `set A := ((mat h₂).map (piW t))ᵀ * G.W.J.map t with hA`. Establish `hAu : IsUnit A.det`. Establish `hd` using `congrArg Matrix.det u₂`.

Rewrite `hd` using `[Matrix.det_mul]`. Conclude with `isUnit_of_mul_isUnit_left (hd ▸ hJ)`. Establish `hQ : (mat h₁).map (piW (t.comp σ)) = (mat h₂).map (piW (t.comp σ))`. Rewrite using `[← Matrix.nonsing_inv_mul_cancel_left _ ((mat h₁).map (piW (t.comp σ))) hAu, ← Matrix.nonsing_inv_mul_cancel_left _ ((mat h₂).map (piW (t.comp σ))) hAu, u₁, u₂]`. Establish `hpi : ∀ (h : UA σ G.W.J) (τ : E →ₐ[F] Fv F v), (mat h).map (piW τ) = ((mat h).map (compFin F E v)).map (splitProj τ)`.

Introduce `h τ`. Rewrite using `[Matrix.map_map]`. Both sides reduce to the same expression. Establish `hY : (mat h₁).map (compFin F E v) = (mat h₂).map (compFin F E v)`. Use `mat_split_ext hcm t ?_ ?_` and prove the remaining obligations.

Rewrite using `[← hpi, ← hpi, heq]`. Rewrite using `[← hpi, ← hpi, hQ]`. Establish `hz : At (evFin F v) (mat h₁ - mat h₂)`. Introduce `u hu`. Establish `e : mat h₁ - mat h₂ = (mat h₁ - 1) - (mat h₂ - 1)` using `by abel`.

Rewrite using `[e, smul_sub, hh₁ u hu, hh₂ u hu, sub_zero]`. Establish `h0 : (mat h₁ - mat h₂).map (compFin F E v) = 0`. Rewrite using `[Matrix.map_sub _ (fun x y => map_sub _ x y), hY, sub_self]`. Establish `hm` using `mat_eq_zero_of_at v _ hz h0`. Conclude with `Subtype.ext (Units.ext (sub_eq_zero.1 hm))`.
-/
theorem eq_of_piW_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v), ∀ h₁ ∈ UAt σ G.W (evFin F v), ∀ h₂ ∈ UAt σ G.W (evFin F v),
      (mat h₁).map (piW t) = (mat h₂).map (piW t) → h₁ = h₂ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v _ t h₁ hh₁ h₂ hh₂ heq
  have hcm := hTr.base.cm
  have hJ : IsUnit (G.W.J.map t).det := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := det_ne_zero_of_sig (hTr.geo.hW.sig (InfinitePlace.mk φ))
    have h1 : G.W.J.det ≠ 0 := fun e => h0 (by
      rw [Matrix.det_smul, show G.W.J.map _ = RingHom.mapMatrix _ G.W.J from rfl, ← RingHom.map_det, e, map_zero,
        mul_zero])
    rw [show G.W.J.map t = (t : E →+* Fv F v).mapMatrix G.W.J from rfl, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)
  have u₁ := unitary_at_components v t h₁
  have u₂ := unitary_at_components v t h₂
  rw [heq] at u₁
  set A := ((mat h₂).map (piW t))ᵀ * G.W.J.map t with hA
  have hAu : IsUnit A.det := by
    have hd := congrArg Matrix.det u₂
    rw [Matrix.det_mul] at hd
    exact isUnit_of_mul_isUnit_left (hd ▸ hJ)
  have hQ : (mat h₁).map (piW (t.comp σ)) = (mat h₂).map (piW (t.comp σ)) := by
    rw [← Matrix.nonsing_inv_mul_cancel_left _ ((mat h₁).map (piW (t.comp σ))) hAu,
      ← Matrix.nonsing_inv_mul_cancel_left _ ((mat h₂).map (piW (t.comp σ))) hAu, u₁, u₂]
  have hpi : ∀ (h : UA σ G.W.J) (τ : E →ₐ[F] Fv F v),
      (mat h).map (piW τ) = ((mat h).map (compFin F E v)).map (splitProj τ) := by
    intro h τ; rw [Matrix.map_map]; rfl
  have hY : (mat h₁).map (compFin F E v) = (mat h₂).map (compFin F E v) := by
    refine mat_split_ext hcm t ?_ ?_
    · rw [← hpi, ← hpi, heq]
    · rw [← hpi, ← hpi, hQ]
  have hz : At (evFin F v) (mat h₁ - mat h₂) := by
    intro u hu
    have e : mat h₁ - mat h₂ = (mat h₁ - 1) - (mat h₂ - 1) := by abel
    rw [e, smul_sub, hh₁ u hu, hh₂ u hu, sub_zero]
  have h0 : (mat h₁ - mat h₂).map (compFin F E v) = 0 := by
    rw [Matrix.map_sub _ (fun x y => map_sub _ x y), hY, sub_self]
  have hm := mat_eq_zero_of_at v _ hz h0
  exact Subtype.ext (Units.ext (sub_eq_zero.1 hm))

end GlobalTheory.UnitaryInjAtPlace
