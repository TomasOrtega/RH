import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksSubOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.DblSurj

open Matrix GlobalTheory.EmbChart

section Lift

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F))
  {ι : Type} [Fintype ι] [DecidableEq ι]

def ext0 (M : Matrix ι ι (Fv F v ⊗[F] E)) : Matrix ι ι (AE F E) := M.map (tensAt E v)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[ext0]`.
-/
theorem matrixExtendByZero_add (M N : Matrix ι ι (Fv F v ⊗[F] E)) : ext0 v (M + N) = ext0 v M + ext0 v N := by
  ext i j; simp [ext0]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[ext0]`.
-/
theorem matrixExtendByZero_zero : ext0 v (0 : Matrix ι ι (Fv F v ⊗[F] E)) = 0 := by
  ext i j; simp [ext0]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [ext0, Matrix.mul_apply, Matrix.map_apply, map_sum, tensAt_mul_right]`.
-/
theorem ext_zero_mul_right (M : Matrix ι ι (Fv F v ⊗[F] E)) (C : Matrix ι ι (AE F E)) :
    ext0 v M * C = ext0 v (M * C.map (compFin F E v)) := by
  ext i j
  simp only [ext0, Matrix.mul_apply, Matrix.map_apply, map_sum, tensAt_mul_right]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [ext0, Matrix.mul_apply, Matrix.map_apply, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm, tensAt_mul_right, mul_comm]`.
-/
theorem ext_zero_mul_left (M : Matrix ι ι (Fv F v ⊗[F] E)) (C : Matrix ι ι (AE F E)) :
    C * ext0 v M = ext0 v (C.map (compFin F E v) * M) := by
  ext i j
  simp only [ext0, Matrix.mul_apply, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, tensAt_mul_right, mul_comm]

/- English proof (translation)
Rewrite using `[ext_zero_mul_right]`. Use `congr 2`. Use extensionality with `i j`. Conclude with `compFin_tensAt v _`.
-/
theorem matrixExtendByZero_mul (M N : Matrix ι ι (Fv F v ⊗[F] E)) : ext0 v M * ext0 v N = ext0 v (M * N) := by
  rw [ext_zero_mul_right]
  congr 2
  ext i j
  exact compFin_tensAt v _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ext_zero_transpose (M : Matrix ι ι (Fv F v ⊗[F] E)) : (ext0 v M)ᵀ = ext0 v Mᵀ := rfl

/- English proof (translation)
Use extensionality with `i j`. Conclude with `sigR_tensAt v σ _`.
-/
theorem ext_zero_map_conj (σ : E →ₐ[F] E) (M : Matrix ι ι (Fv F v ⊗[F] E)) :
    (ext0 v M).map (cA σ) = ext0 v (M.map (sigR (Fv F v) σ)) := by
  ext i j
  exact sigR_tensAt v σ _

/- English proof (translation)
Use extensionality with `i j`. Conclude with `compFin_tensAt v _`.
-/
theorem ext_zero_comp_finite (M : Matrix ι ι (Fv F v ⊗[F] E)) : (ext0 v M).map (compFin F E v) = M := by
  ext i j
  exact compFin_tensAt v _

def lift (Y : Matrix ι ι (Fv F v ⊗[F] E)) : Matrix ι ι (AE F E) := 1 + ext0 v (Y - 1)

/- English proof (translation)
Establish `e : Y * Z - 1 = (Y - 1) + (Z - 1) + (Y - 1) * (Z - 1)` using `by noncomm_ring`. Rewrite using `[lift, lift, lift, e, matrixExtendByZero_add, matrixExtendByZero_add, ← matrixExtendByZero_mul]`. Use `noncomm_ring`.
-/
theorem lift_mul (Y Z : Matrix ι ι (Fv F v ⊗[F] E)) : lift v Y * lift v Z = lift v (Y * Z) := by
  have e : Y * Z - 1 = (Y - 1) + (Z - 1) + (Y - 1) * (Z - 1) := by noncomm_ring
  rw [lift, lift, lift, e, matrixExtendByZero_add, matrixExtendByZero_add, ← matrixExtendByZero_mul]
  noncomm_ring

/- English proof (translation)
Rewrite using `[lift, sub_self, matrixExtendByZero_zero, add_zero]`.
-/
theorem lift_one : lift v (1 : Matrix ι ι (Fv F v ⊗[F] E)) = 1 := by
  rw [lift, sub_self, matrixExtendByZero_zero, add_zero]

/- English proof (translation)
Establish `h2 : (1 : Matrix ι ι (AE F E)).map (compFin F E v) = 1` using `Matrix.map_one _ (map_zero _) (map_one _)`. Establish `h1 : (lift v Y).map (compFin F E v) = (1 : Matrix ι ι (AE F E)).map (compFin F E v) + (ext0 v (Y - 1)).map (compFin F E v)`. Use extensionality with `i j`. Simplify using `only [lift, Matrix.map_apply, Matrix.add_apply, map_add]`. Rewrite using `[h1, ext_zero_comp_finite, h2]`.

Normalize the expressions using the abelian group laws.
-/
theorem compFin_lift (Y : Matrix ι ι (Fv F v ⊗[F] E)) : (lift v Y).map (compFin F E v) = Y := by
  have h2 : (1 : Matrix ι ι (AE F E)).map (compFin F E v) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h1 : (lift v Y).map (compFin F E v) = (1 : Matrix ι ι (AE F E)).map (compFin F E v) +
      (ext0 v (Y - 1)).map (compFin F E v) := by
    ext i j; simp only [lift, Matrix.map_apply, Matrix.add_apply, map_add]
  rw [h1, ext_zero_comp_finite, h2]
  abel

/- English proof (translation)
Introduce `u hu`. Rewrite using `[lift, add_sub_cancel_left]`. Use extensionality with `i j`. Simplify using `only [ext0, Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply]`. Rewrite using `[Algebra.smul_def, mul_comm, tensAt_mul_right]`.

Establish `: compFin F E v (algebraMap (AF F) (AE F E) u) = 0`. Express the relevant statement in the definitionally equal form `(evFin F v u) ⊗ₜ[F] (1 : E) = 0`. Rewrite using `[hu, TensorProduct.zero_tmul]`. Rewrite using `[this, mul_zero, map_zero]`.
-/
theorem lift_sub_one_at (Y : Matrix ι ι (Fv F v ⊗[F] E)) : At (evFin F v) (lift v Y - 1) := by
  intro u hu
  rw [lift, add_sub_cancel_left]
  ext i j
  simp only [ext0, Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply]
  rw [Algebra.smul_def, mul_comm, tensAt_mul_right]
  have : compFin F E v (algebraMap (AF F) (AE F E) u) = 0 := by
    change (evFin F v u) ⊗ₜ[F] (1 : E) = 0
    rw [hu, TensorProduct.zero_tmul]
  rw [this, mul_zero, map_zero]

/- English proof (translation)
Use `set C := incM F J`. Establish `hC : C.map (compFin F E v) = J.map (inclR (Fv F v))`. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `compFin F E v ((1 : AF F) ⊗ₜ[F] J i j) = (1 : Fv F v) ⊗ₜ[F] J i j`. Express the relevant statement in the definitionally equal form `evFin F v 1 ⊗ₜ[F] J i j = _`.

Rewrite using `[map_one]`. Establish `hT : (lift v Y)ᵀ = 1 + ext0 v (Y - 1)ᵀ`. Rewrite using `[lift, Matrix.transpose_add, Matrix.transpose_one, ext_zero_transpose]`. Establish `hS : (lift v Y).map (cA σ) = 1 + ext0 v ((Y - 1).map (sigR (Fv F v) σ))`. Rewrite using `[← ext_zero_map_conj]`.

Use extensionality with `i j`. Simplify using `[lift, Matrix.one_apply]`. Rewrite using `[hT, hS]`. Establish `e1 : (1 + ext0 v (Y - 1)ᵀ) * C * (1 + ext0 v ((Y - 1).map (sigR (Fv F v) σ))) = C + (ext0 v (Y - 1)ᵀ * C + C * ext0 v ((Y - 1).map (sigR (Fv F v) σ)) + ext0 v (Y - 1)ᵀ * C * ext0 v ((Y - 1).map (sigR (Fv F v) σ)))` using `by noncomm_ring`. Rewrite using `[e1, ext_zero_mul_right, matrixExtendByZero_mul, ext_zero_mul_left, ← matrixExtendByZero_add, ← matrixExtendByZero_add, hC]`.

Establish `hYs : (Y - 1).map (sigR (Fv F v) σ) = Y.map (sigR (Fv F v) σ) - 1`. Rewrite using `[Matrix.map_sub _ (fun a b => map_sub _ a b), Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite using `[hYs, Matrix.transpose_sub, Matrix.transpose_one]`. Use `set Jl : Matrix ι ι (Fv F v ⊗[F] E) := J.map (inclR (Fv F v))`. Establish `e2 : (Yᵀ - 1) * Jl + Jl * (Y.map (sigR (Fv F v) σ) - 1) + (Yᵀ - 1) * Jl * (Y.map (sigR (Fv F v) σ) - 1) = Yᵀ * Jl * Y.map (sigR (Fv F v) σ) - Jl` using `by noncomm_ring`.

Rewrite using `[e2, hY, sub_self, matrixExtendByZero_zero, add_zero]`.
-/
theorem lift_unitary (σ : E →ₐ[F] E) (J : Matrix ι ι E) (Y : Matrix ι ι (Fv F v ⊗[F] E))
    (hY : Yᵀ * J.map (inclR (Fv F v)) * Y.map (sigR (Fv F v) σ) = J.map (inclR (Fv F v))) :
    (lift v Y)ᵀ * incM F J * (lift v Y).map (cA σ) = incM F J := by
  set C := incM F J
  have hC : C.map (compFin F E v) = J.map (inclR (Fv F v)) := by
    ext i j
    change compFin F E v ((1 : AF F) ⊗ₜ[F] J i j) = (1 : Fv F v) ⊗ₜ[F] J i j
    change evFin F v 1 ⊗ₜ[F] J i j = _
    rw [map_one]
  have hT : (lift v Y)ᵀ = 1 + ext0 v (Y - 1)ᵀ := by
    rw [lift, Matrix.transpose_add, Matrix.transpose_one, ext_zero_transpose]
  have hS : (lift v Y).map (cA σ) = 1 + ext0 v ((Y - 1).map (sigR (Fv F v) σ)) := by
    rw [← ext_zero_map_conj]
    ext i j
    simp [lift, Matrix.one_apply]
  rw [hT, hS]
  have e1 : (1 + ext0 v (Y - 1)ᵀ) * C * (1 + ext0 v ((Y - 1).map (sigR (Fv F v) σ))) =
      C + (ext0 v (Y - 1)ᵀ * C + C * ext0 v ((Y - 1).map (sigR (Fv F v) σ)) +
        ext0 v (Y - 1)ᵀ * C * ext0 v ((Y - 1).map (sigR (Fv F v) σ))) := by noncomm_ring
  rw [e1, ext_zero_mul_right, matrixExtendByZero_mul, ext_zero_mul_left, ← matrixExtendByZero_add, ← matrixExtendByZero_add, hC]
  have hYs : (Y - 1).map (sigR (Fv F v) σ) = Y.map (sigR (Fv F v) σ) - 1 := by
    rw [Matrix.map_sub _ (fun a b => map_sub _ a b), Matrix.map_one _ (map_zero _) (map_one _)]
  rw [hYs, Matrix.transpose_sub, Matrix.transpose_one]
  set Jl : Matrix ι ι (Fv F v ⊗[F] E) := J.map (inclR (Fv F v))
  have e2 : (Yᵀ - 1) * Jl + Jl * (Y.map (sigR (Fv F v) σ) - 1) + (Yᵀ - 1) * Jl * (Y.map (sigR (Fv F v) σ) - 1) =
      Yᵀ * Jl * Y.map (sigR (Fv F v) σ) - Jl := by noncomm_ring
  rw [e2, hY, sub_self, matrixExtendByZero_zero, add_zero]

end Lift

end GlobalTheory.DblSurj

namespace GlobalTheory.DblSurj

open Matrix GlobalTheory.EmbChart

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
The claim follows from `Matrix.map_mul (f := f.toRingHom)`.
-/
theorem map_mul_alg (f : Fv F v ⊗[F] E →ₐ[Fv F v] Fv F v) (M N : Matrix ι ι (Fv F v ⊗[F] E)) :
    (M * N).map f = M.map f * N.map f :=
  Matrix.map_mul (f := f.toRingHom)

/- English proof (translation)
Use extensionality with `i j`. Conclude with `split_ext h t (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)`.
-/
theorem mat_split_ext (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {Y Z : Matrix ι ι (Fv F v ⊗[F] E)}
    (h1 : Y.map (splitProj t) = Z.map (splitProj t))
    (h2 : Y.map (splitProj (t.comp σ)) = Z.map (splitProj (t.comp σ))) : Y = Z := by
  ext i j
  exact split_ext h t (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)

def pairMat (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (A B : Matrix ι ι (Fv F v)) :
    Matrix ι ι (Fv F v ⊗[F] E) := fun i j => (splitAlgEquiv h t).symm (A i j, B i j)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[pairMat]`.
-/
theorem pairMat_fst (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (A B : Matrix ι ι (Fv F v)) :
    (pairMat h t A B).map (splitProj t) = A := by
  ext i j; simp [pairMat]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[pairMat]`.
-/
theorem pairMat_snd (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (A B : Matrix ι ι (Fv F v)) :
    (pairMat h t A B).map (splitProj (t.comp σ)) = B := by
  ext i j; simp [pairMat]

/- English proof (translation)
The claim follows from `mat_split_ext h t (by rw [map_mul_alg, pairMat_fst, pairMat_fst, pairMat_fst]) (by rw [map_mul_alg, pairMat_snd, pairMat_snd, pairMat_snd])`.
-/
theorem pairMat_mul (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (A B A' B' : Matrix ι ι (Fv F v)) :
    pairMat h t A B * pairMat h t A' B' = pairMat h t (A * A') (B * B') :=
  mat_split_ext h t (by rw [map_mul_alg, pairMat_fst, pairMat_fst, pairMat_fst])
    (by rw [map_mul_alg, pairMat_snd, pairMat_snd, pairMat_snd])

/- English proof (translation)
The claim follows from `mat_split_ext h t (by rw [pairMat_fst, Matrix.map_one _ (map_zero _) (map_one _)]) (by rw [pairMat_snd, Matrix.map_one _ (map_zero _) (map_one _)])`.
-/
theorem pairMat_one (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) :
    pairMat h t (1 : Matrix ι ι (Fv F v)) 1 = 1 :=
  mat_split_ext h t (by rw [pairMat_fst, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [pairMat_snd, Matrix.map_one _ (map_zero _) (map_one _)])

def conjComp (t : E →ₐ[F] Fv F v) (J : Matrix ι ι E) (g : GL ι (Fv F v)) : Matrix ι ι (Fv F v) :=
  (J.map t)⁻¹ * ((g⁻¹ : GL ι (Fv F v)) : Matrix ι ι (Fv F v))ᵀ * J.map t

/- English proof (translation)
Simplify using `only [conjComp, _root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hJ]`.
-/
theorem conjComp_mul (t : E →ₐ[F] Fv F v) (J : Matrix ι ι E) (hJ : IsUnit (J.map t).det)
    (g₁ g₂ : GL ι (Fv F v)) : conjComp t J (g₁ * g₂) = conjComp t J g₁ * conjComp t J g₂ := by
  simp only [conjComp, _root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv_cancel_left _ _ hJ]

/- English proof (translation)
Simplify using `only [conjComp, inv_one, Units.val_one, Matrix.transpose_one, Matrix.mul_one]`. Conclude with `Matrix.nonsing_inv_mul _ hJ`.
-/
theorem conjComp_one (t : E →ₐ[F] Fv F v) (J : Matrix ι ι E) (hJ : IsUnit (J.map t).det) :
    conjComp t J 1 = 1 := by
  simp only [conjComp, inv_one, Units.val_one, Matrix.transpose_one, Matrix.mul_one]
  exact Matrix.nonsing_inv_mul _ hJ

def locPt (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (J : Matrix ι ι E) (g : GL ι (Fv F v)) :
    Matrix ι ι (Fv F v ⊗[F] E) := pairMat h t g (conjComp t J g)

/- English proof (translation)
Rewrite using `[locPt, locPt, locPt, pairMat_mul, conjComp_mul t J hJ, Units.val_mul]`.
-/
theorem locPt_mul (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (J : Matrix ι ι E)
    (hJ : IsUnit (J.map t).det) (g₁ g₂ : GL ι (Fv F v)) :
    locPt h t J (g₁ * g₂) = locPt h t J g₁ * locPt h t J g₂ := by
  rw [locPt, locPt, locPt, pairMat_mul, conjComp_mul t J hJ, Units.val_mul]

/- English proof (translation)
Rewrite using `[locPt, conjComp_one t J hJ, Units.val_one, pairMat_one]`.
-/
theorem locPt_one (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (J : Matrix ι ι E)
    (hJ : IsUnit (J.map t).det) : locPt h t J 1 = 1 := by
  rw [locPt, conjComp_one t J hJ, Units.val_one, pairMat_one]

/- English proof (translation)
Establish `hJl : ∀ τ : E →ₐ[F] Fv F v, (J.map (inclR (Fv F v))).map (splitProj τ) = J.map τ` using `fun τ => Matrix.ext fun i j => by`. Simplify using `only [Matrix.map_apply]`. Conclude with `splitProj_inclR τ (J i j)`. Establish `hs1 : ((locPt h t J g).map (sigR (Fv F v) σ)).map (splitProj t) = conjComp t J g`. Rewrite using `[Matrix.map_map]`.

Establish `: (splitProj t ∘ sigR (Fv F v) σ) = splitProj (t.comp σ)` using `funext fun y => (splitProj_comp t σ y).symm`. Rewrite using `[this, locPt, pairMat_snd]`. Establish `hs2 : ((locPt h t J g).map (sigR (Fv F v) σ)).map (splitProj (t.comp σ)) = g`. Rewrite using `[Matrix.map_map]`. Establish `: (splitProj (t.comp σ) ∘ sigR (Fv F v) σ) = splitProj t` using `funext fun y => splitProj_comp_sigR h t y`.

Rewrite using `[this, locPt, pairMat_fst]`. Establish `hJs : J.map (t.comp σ) = -(J.map t)ᵀ`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.transpose_apply, AlgHom.comp_apply, Matrix.neg_apply]`. Rewrite using `[skew j i, map_neg]`.

Use `mat_split_ext h t ?_ ?_` and prove the remaining obligations. Rewrite using `[map_mul_alg, map_mul_alg, Matrix.transpose_map, hJl, hs1, locPt, pairMat_fst, conjComp] set Jt := J.map t set A : Matrix ι ι (Fv F v) := ((g⁻¹ : GL ι (Fv F v)) : Matrix ι ι (Fv F v))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_nonsing_inv _ hJ, Matrix.mul_one, Matrix.transpose_mul]`. Use `_ = Jt := by`.

Rewrite using `[show A * (g : Matrix ι ι (Fv F v)) = 1 from Units.inv_mul g, Matrix.transpose_one, Matrix.one_mul]`. Rewrite using `[map_mul_alg, map_mul_alg, Matrix.transpose_map, hJl, hs2, locPt, pairMat_snd, conjComp, hJs] set Jt := J.map t set A : Matrix ι ι (Fv F v) := ((g⁻¹ : GL ι (Fv F v)) : Matrix ι ι (Fv F v))`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]`. Use `_ = -(Jtᵀ * (A * (g : Matrix ι ι (Fv F v)))) := by`.

Rewrite using `[Matrix.mul_nonsing_inv _ hJ, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_assoc]`. Use `_ = -Jtᵀ := by rw [show A * (g : Matrix ι ι (Fv F v)) = 1 from Units.inv_mul g, Matrix.mul_one]`.
-/
theorem locPt_unitary_skew (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (J : Matrix ι ι E)
    (hJ : IsUnit (J.map t).det) (skew : ∀ i j, σ (J j i) = -J i j) (g : GL ι (Fv F v)) :
    (locPt h t J g)ᵀ * J.map (inclR (Fv F v)) * (locPt h t J g).map (sigR (Fv F v) σ) =
      J.map (inclR (Fv F v)) := by
  have hJl : ∀ τ : E →ₐ[F] Fv F v, (J.map (inclR (Fv F v))).map (splitProj τ) = J.map τ := fun τ =>
    Matrix.ext fun i j => by
      simp only [Matrix.map_apply]; exact splitProj_inclR τ (J i j)
  have hs1 : ((locPt h t J g).map (sigR (Fv F v) σ)).map (splitProj t) = conjComp t J g := by
    rw [Matrix.map_map]
    have : (splitProj t ∘ sigR (Fv F v) σ) = splitProj (t.comp σ) := funext fun y => (splitProj_comp t σ y).symm
    rw [this, locPt, pairMat_snd]
  have hs2 : ((locPt h t J g).map (sigR (Fv F v) σ)).map (splitProj (t.comp σ)) = g := by
    rw [Matrix.map_map]
    have : (splitProj (t.comp σ) ∘ sigR (Fv F v) σ) = splitProj t := funext fun y => splitProj_comp_sigR h t y
    rw [this, locPt, pairMat_fst]
  have hJs : J.map (t.comp σ) = -(J.map t)ᵀ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, AlgHom.comp_apply, Matrix.neg_apply]
    rw [skew j i, map_neg]
  refine mat_split_ext h t ?_ ?_
  · rw [map_mul_alg, map_mul_alg, Matrix.transpose_map, hJl, hs1, locPt, pairMat_fst, conjComp]
    set Jt := J.map t
    set A : Matrix ι ι (Fv F v) := ((g⁻¹ : GL ι (Fv F v)) : Matrix ι ι (Fv F v))
    calc (g : Matrix ι ι (Fv F v))ᵀ * Jt * (Jt⁻¹ * Aᵀ * Jt)
        = (g : Matrix ι ι (Fv F v))ᵀ * (Jt * Jt⁻¹) * Aᵀ * Jt := by simp only [Matrix.mul_assoc]
      _ = (A * (g : Matrix ι ι (Fv F v)))ᵀ * Jt := by
          rw [Matrix.mul_nonsing_inv _ hJ, Matrix.mul_one, Matrix.transpose_mul]
      _ = Jt := by
          rw [show A * (g : Matrix ι ι (Fv F v)) = 1 from Units.inv_mul g, Matrix.transpose_one,
            Matrix.one_mul]
  · rw [map_mul_alg, map_mul_alg, Matrix.transpose_map, hJl, hs2, locPt, pairMat_snd, conjComp, hJs]
    set Jt := J.map t
    set A : Matrix ι ι (Fv F v) := ((g⁻¹ : GL ι (Fv F v)) : Matrix ι ι (Fv F v))
    calc (Jt⁻¹ * Aᵀ * Jt)ᵀ * -Jtᵀ * (g : Matrix ι ι (Fv F v))
        = -(Jtᵀ * A * (Jt * Jt⁻¹)ᵀ * (g : Matrix ι ι (Fv F v))) := by
          simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, Matrix.mul_neg,
            Matrix.neg_mul]
      _ = -(Jtᵀ * (A * (g : Matrix ι ι (Fv F v)))) := by
          rw [Matrix.mul_nonsing_inv _ hJ, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_assoc]
      _ = -Jtᵀ := by rw [show A * (g : Matrix ι ι (Fv F v)) = 1 from Units.inv_mul g, Matrix.mul_one]

end Local

end GlobalTheory.DblSurj

namespace GlobalTheory.DblSurj

open scoped Matrix

/- English proof (translation)
Take `⟨hn, A, hA⟩` from `h`. Set `e : Fin r ⊕ Fin s ≃ Fin n` to `finSumFinEquiv.trans (finCongr hn)`. Establish `key : (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star = (Aᵀ * M * A.map star).submatrix e.symm e.symm`. Use extensionality with `i j`. Both sides reduce to the same expression.

Establish `hd` using `congrArg Matrix.det key`. Rewrite `hd` using `[Matrix.det_submatrix_equiv_self, hA, Matrix.det_mul, Matrix.det_mul]`. Introduce `h0`. Rewrite `hd` using `[h0]`. Simplify using `[Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg] at hd`.

Conclude with `pow_ne_zero _ (by norm_num) hd.symm`.
-/
theorem det_ne_zero_of_sig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hn, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hn)
  have key : (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star =
      (Aᵀ * M * A.map star).submatrix e.symm e.symm := by
    ext i j; rfl
  have hd := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, hA, Matrix.det_mul, Matrix.det_mul] at hd
  intro h0
  rw [h0] at hd
  simp [Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg] at hd
  exact pow_ne_zero _ (by norm_num) hd.symm

end GlobalTheory.DblSurj

open scoped Matrix

open GlobalTheory.DblSurj in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v t c g`. Establish `h` using `hP.base.cm`. Establish `hW` using `hP.skew`. Establish `hJ1 : IsUnit (W.J.map t).det`. Take `⟨φ⟩ : Nonempty (F →+* ℂ)` from `inferInstance`.

Establish `h0` using `det_ne_zero_of_sig (hW.sig (InfinitePlace.mk φ))`. Establish `h1 : W.J.det ≠ 0` using `fun e => h0 (by`. Rewrite using `[Matrix.det_smul, show W.J.map _ = RingHom.mapMatrix _ W.J from rfl, ← RingHom.map_det, e, map_zero, mul_zero])`. Rewrite using `[show W.J.map t = (t : E →+* Fv F v).mapMatrix W.J from rfl, ← RingHom.map_det]`. Conclude with `isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)`.

Use `set Jd : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) E := Matrix.fromBlocks W.J 0 0 (-W.J) with hJdef`. Establish `hJd : IsUnit (Jd.map t).det`. Establish `e : Jd.map t = Matrix.fromBlocks (W.J.map t) 0 0 (-(W.J.map t))`. Rewrite using `[hJdef, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero t), Matrix.map_neg _ (map_neg t)]`. Rewrite using `[e, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]`.

Conclude with `hJ1.mul ((isUnit_one.neg.pow _).mul hJ1)`. Establish `skew : ∀ i j, σ (Jd j i) = -Jd i j`. Apply the tactic sequence `rintro (i | i) (j | j) <;> simp [hJdef, hW.skew]`. Establish `hdbl : dbl (incM F W.J) = incM F Jd`. Rewrite using `[hJdef, dbl, incM, incM, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_neg _ (map_neg _)]`.

Use `set g₀ : GL (Fin d ⊕ Fin d) (Fv F v) := GlobalTheory.DblScal.dsum c * g * (GlobalTheory.DblScal.dsum c)⁻¹ with hg₀`. Set `G : GL (Fin d ⊕ Fin d) (AE F E)` to `⟨lift v (locPt h t Jd g₀), lift v (locPt h t Jd g₀⁻¹), by rw [lift_mul, ← locPt_mul h t Jd hJd, mul_inv_cancel, locPt_one h t Jd hJd, lift_one], by rw [lift_mul, ← locPt_mul h t Jd hJd, inv_mul_cancel, locPt_one h t Jd hJd, lift_one]⟩`. Establish `hu : (lift v (locPt h t Jd g₀))ᵀ * dbl (incM F W.J) * (lift v (locPt h t Jd g₀)).map (cA σ) = dbl (incM F W.J)`. Rewrite using `[hdbl]`. Conclude with `lift_unitary v σ Jd _ (locPt_unitary_skew h t Jd hJd skew g₀)`.

Set `p : GlobalTheory.DblScal.UD σ W.J` to `⟨G, hu⟩`. Use `⟨p, lift_sub_one_at v _, ?_⟩` and prove the remaining obligations. Establish `hpi : Matrix.GeneralLinearGroup.map (piW t) p.1 = g₀`. Apply `Units.ext` to reduce the goal to its premises. Use `show (lift v (locPt h t Jd g₀)).map (piW t) = g₀.val`.

Establish `e : ∀ N : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E), N.map (piW t) = (N.map (compFin F E v)).map (splitProj t)` using `fun N => by rw [Matrix.map_map]; rfl`. Rewrite using `[e, compFin_lift, locPt, pairMat_fst]`. Use `show (GlobalTheory.DblScal.dsum c)⁻¹ * Matrix.GeneralLinearGroup.map (piW t) p.1 * GlobalTheory.DblScal.dsum c = g`. Rewrite using `[hpi, hg₀]`. Use `group`.
-/
theorem GlobalTheory.DblSurj.exists_locMatD_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (c : GL (Fin d) (Fv F v)) (g : GL (Fin d ⊕ Fin d) (Fv F v)),
      ∃ p ∈ GlobalTheory.DblScal.UDAt σ W.J (evFin F v), GlobalTheory.DblScal.locMatD t c p = g := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v t c g
  have h := hP.base.cm
  have hW := hP.skew
  have hJ1 : IsUnit (W.J.map t).det := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := det_ne_zero_of_sig (hW.sig (InfinitePlace.mk φ))
    have h1 : W.J.det ≠ 0 := fun e => h0 (by
      rw [Matrix.det_smul, show W.J.map _ = RingHom.mapMatrix _ W.J from rfl, ← RingHom.map_det, e, map_zero,
        mul_zero])
    rw [show W.J.map t = (t : E →+* Fv F v).mapMatrix W.J from rfl, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)
  set Jd : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) E := Matrix.fromBlocks W.J 0 0 (-W.J) with hJdef
  have hJd : IsUnit (Jd.map t).det := by
    have e : Jd.map t = Matrix.fromBlocks (W.J.map t) 0 0 (-(W.J.map t)) := by
      rw [hJdef, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero t), Matrix.map_neg _ (map_neg t)]
    rw [e, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
    exact hJ1.mul ((isUnit_one.neg.pow _).mul hJ1)
  have skew : ∀ i j, σ (Jd j i) = -Jd i j := by
    rintro (i | i) (j | j) <;> simp [hJdef, hW.skew]
  have hdbl : dbl (incM F W.J) = incM F Jd := by
    rw [hJdef, dbl, incM, incM, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_neg _ (map_neg _)]
  set g₀ : GL (Fin d ⊕ Fin d) (Fv F v) := GlobalTheory.DblScal.dsum c * g * (GlobalTheory.DblScal.dsum c)⁻¹ with hg₀
  let G : GL (Fin d ⊕ Fin d) (AE F E) :=
    ⟨lift v (locPt h t Jd g₀), lift v (locPt h t Jd g₀⁻¹),
      by rw [lift_mul, ← locPt_mul h t Jd hJd, mul_inv_cancel, locPt_one h t Jd hJd, lift_one],
      by rw [lift_mul, ← locPt_mul h t Jd hJd, inv_mul_cancel, locPt_one h t Jd hJd, lift_one]⟩
  have hu : (lift v (locPt h t Jd g₀))ᵀ * dbl (incM F W.J) * (lift v (locPt h t Jd g₀)).map (cA σ) =
      dbl (incM F W.J) := by
    rw [hdbl]; exact lift_unitary v σ Jd _ (locPt_unitary_skew h t Jd hJd skew g₀)
  let p : GlobalTheory.DblScal.UD σ W.J := ⟨G, hu⟩
  refine ⟨p, lift_sub_one_at v _, ?_⟩
  have hpi : Matrix.GeneralLinearGroup.map (piW t) p.1 = g₀ := by
    apply Units.ext
    show (lift v (locPt h t Jd g₀)).map (piW t) = g₀.val
    have e : ∀ N : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E),
        N.map (piW t) = (N.map (compFin F E v)).map (splitProj t) := fun N => by rw [Matrix.map_map]; rfl
    rw [e, compFin_lift, locPt, pairMat_fst]
  show (GlobalTheory.DblScal.dsum c)⁻¹ * Matrix.GeneralLinearGroup.map (piW t) p.1 * GlobalTheory.DblScal.dsum c = g
  rw [hpi, hg₀]
  group
