import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomSuppSplit

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.SplitUnitLift

open GlobalTheory.SplitGLLift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : Pl F} {n : ℕ}

/- English proof (translation)
Use `set p := pairHom (J.map τ) hJ g - 1 with hp`. Establish `hN : oneAdd (liftMat h τ) (pairHom (J.map τ) hJ g) = 1 + liftMat h τ p` using `rfl`. Rewrite using `[hN, map_one_add_cA]`. Establish `tr : ∀ {R : Type} [CommRing R] (f : AF F ⊗[F] E →+* R) (A B C : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)), (Aᵀ * B * C).map f = (A.map f)ᵀ * B.map f * C.map f` using `fun f A B C => by`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]`.

Establish `e : J.map τ * (J.map τ)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hJ`. Establish `gi : ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v)) * (g : Matrix (Fin n) (Fin n) (Fv F v)) = 1` using `Units.inv_mul g`. Apply `mat_ext h τ` to reduce the goal to its premises. Introduce `w`. Rewrite using `[tr, map_one_add_of_zero _ h τ (compInf_liftPair h τ w), map_one_add_of_zero _ h τ (compInf_liftPair h τ w)]`.

Simplify using the standard rewrite rules. Introduce `u hu`. Rewrite using `[tr, map_one_add_of_zero _ h τ (compFin_liftPair_ne h τ hu), map_one_add_of_zero _ h τ (compFin_liftPair_ne h τ hu)]`. Simplify using the standard rewrite rules. Rewrite using `[tr, map_one_add_piW, map_one_add_piW, incM, Matrix.map_map]`.

Establish `hJm : J.map (⇑(piW τ) ∘ ⇑(inclR (F` using `F) (AF F))) = J.map τ := Matrix.ext fun i j => piW_inclR τ (J i j)`. Rewrite using `[hJm]`. Simplify using `only [hp, Prod.fst_sub, Prod.snd_sub, Prod.swap, Prod.fst_one, Prod.snd_one, add_sub_cancel]`. Use `show (g : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * J.map τ * ((J.map τ)⁻¹ * ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * J.map τ) = J.map τ`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (J.map τ), e, Matrix.mul_one, ← Matrix.transpose_mul, gi, Matrix.transpose_one, Matrix.one_mul]`.

Rewrite using `[tr, map_one_add_piW_comp, map_one_add_piW_comp, incM, Matrix.map_map]`. Establish `hJm : J.map (⇑(piW (τ.comp σ)) ∘ ⇑(inclR (F` using `F) (AF F))) = algebraMap F (Fv F v) ε • (J.map τ)ᵀ := by`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.map_apply, Function.comp_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[piW_inclR, AlgHom.comp_apply, herm, map_mul, AlgHom.commutes]`.

Rewrite using `[hJm]`. Simplify using `only [hp, Prod.fst_sub, Prod.snd_sub, Prod.swap, Prod.fst_one, Prod.snd_one, add_sub_cancel]`. Use `show ((J.map τ)⁻¹ * ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * J.map τ)ᵀ * (algebraMap F (Fv F v) ε • (J.map τ)ᵀ) * (g : Matrix (Fin n) (Fin n) (Fv F v)) = algebraMap F (Fv F v) ε • (J.map τ)ᵀ`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul]`. Use `congr 1`.

Rewrite using `[Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc ((J.map τ)⁻¹)ᵀ, ← Matrix.transpose_mul, e, Matrix.transpose_one, Matrix.one_mul, gi, Matrix.mul_one]`.
-/
theorem unitary_eps (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) (g : GL (Fin n) (Fv F v)) :
    (oneAdd (liftMat h τ) (pairHom (J.map τ) hJ g))ᵀ * incM F J *
      (oneAdd (liftMat h τ) (pairHom (J.map τ) hJ g)).map (cA σ) = incM F J := by
  set p := pairHom (J.map τ) hJ g - 1 with hp
  have hN : oneAdd (liftMat h τ) (pairHom (J.map τ) hJ g) = 1 + liftMat h τ p := rfl
  rw [hN, map_one_add_cA]
  have tr : ∀ {R : Type} [CommRing R] (f : AF F ⊗[F] E →+* R) (A B C : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)),
      (Aᵀ * B * C).map f = (A.map f)ᵀ * B.map f * C.map f := fun f A B C => by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  have e : J.map τ * (J.map τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJ
  have gi : ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v)) * (g : Matrix (Fin n) (Fin n) (Fv F v)) = 1 :=
    Units.inv_mul g
  apply mat_ext h τ
  · intro w
    rw [tr, map_one_add_of_zero _ h τ (compInf_liftPair h τ w), map_one_add_of_zero _ h τ (compInf_liftPair h τ w)]
    simp
  · intro u hu
    rw [tr, map_one_add_of_zero _ h τ (compFin_liftPair_ne h τ hu), map_one_add_of_zero _ h τ (compFin_liftPair_ne h τ hu)]
    simp
  · rw [tr, map_one_add_piW, map_one_add_piW, incM, Matrix.map_map]
    have hJm : J.map (⇑(piW τ) ∘ ⇑(inclR (F := F) (AF F))) = J.map τ :=
      Matrix.ext fun i j => piW_inclR τ (J i j)
    rw [hJm]
    simp only [hp, Prod.fst_sub, Prod.snd_sub, Prod.swap, Prod.fst_one, Prod.snd_one, add_sub_cancel]
    show (g : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * J.map τ *
      ((J.map τ)⁻¹ * ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * J.map τ) = J.map τ
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (J.map τ), e, Matrix.mul_one,
      ← Matrix.transpose_mul, gi, Matrix.transpose_one, Matrix.one_mul]
  · rw [tr, map_one_add_piW_comp, map_one_add_piW_comp, incM, Matrix.map_map]
    have hJm : J.map (⇑(piW (τ.comp σ)) ∘ ⇑(inclR (F := F) (AF F))) =
        algebraMap F (Fv F v) ε • (J.map τ)ᵀ := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.map_apply, Function.comp_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
      rw [piW_inclR, AlgHom.comp_apply, herm, map_mul, AlgHom.commutes]
    rw [hJm]
    simp only [hp, Prod.fst_sub, Prod.snd_sub, Prod.swap, Prod.fst_one, Prod.snd_one, add_sub_cancel]
    show ((J.map τ)⁻¹ * ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * J.map τ)ᵀ *
      (algebraMap F (Fv F v) ε • (J.map τ)ᵀ) * (g : Matrix (Fin n) (Fin n) (Fv F v)) =
        algebraMap F (Fv F v) ε • (J.map τ)ᵀ
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((J.map τ)⁻¹)ᵀ, ← Matrix.transpose_mul, e, Matrix.transpose_one, Matrix.one_mul, gi,
      Matrix.mul_one]

def liftN (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (hJ : IsUnit (J.map τ).det) :
    GL (Fin n) (Fv F v) →* Matrix (Fin n) (Fin n) (AE F E) :=
  (oneAdd (liftMat h τ)).comp (pairHom (J.map τ) hJ)

def liftU (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) :
    GL (Fin n) (Fv F v) →* UA σ J where
  toFun g := ⟨⟨liftN h τ J hJ g, liftN h τ J hJ g⁻¹, by rw [← map_mul, mul_inv_cancel, map_one],
    by rw [← map_mul, inv_mul_cancel, map_one]⟩, unitary_eps h τ J ε herm hJ g⟩
  map_one' := Subtype.ext (Units.ext (map_one (liftN h τ J hJ)))
  map_mul' g g' := Subtype.ext (Units.ext (map_mul (liftN h τ J hJ) g g'))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_liftU (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) (g : GL (Fin n) (Fv F v)) :
    mat (liftU h τ J ε herm hJ g) = 1 + liftMat h τ (pairHom (J.map τ) hJ g - 1) := rfl

/- English proof (translation)
Use `show At (evFin F v) (mat _ - 1)`. Rewrite using `[mat_liftU, add_sub_cancel_left]`. Conclude with `at_liftMat h τ _`.
-/
theorem liftU_mem_UAt (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (X : Spc F E n) (ε : F)
    (herm : ∀ i j, σ (X.J j i) = algebraMap F E ε * X.J i j) (hJ : IsUnit (X.J.map τ).det) (g : GL (Fin n) (Fv F v)) :
    liftU h τ X.J ε herm hJ g ∈ UAt σ X (evFin F v) := by
  show At (evFin F v) (mat _ - 1)
  rw [mat_liftU, add_sub_cancel_left]
  exact at_liftMat h τ _

/- English proof (translation)
Rewrite using `[mat_liftU, map_one_add_piW]`. Conclude with `add_sub_cancel _ _`.
-/
theorem liftU_piW (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) (g : GL (Fin n) (Fv F v)) :
    (mat (liftU h τ J ε herm hJ g)).map (piW τ) = g.val := by
  rw [mat_liftU, map_one_add_piW]
  exact add_sub_cancel _ _

/- English proof (translation)
Rewrite using `[mat_liftU, map_one_add_piW_comp]`. Conclude with `add_sub_cancel _ _`.
-/
theorem liftU_piW_comp (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) (g : GL (Fin n) (Fv F v)) :
    (mat (liftU h τ J ε herm hJ g)).map (piW (τ.comp σ)) = (J.map τ)⁻¹ * ((g⁻¹ : GL (Fin n) (Fv F v)).val)ᵀ * J.map τ := by
  rw [mat_liftU, map_one_add_piW_comp]
  exact add_sub_cancel _ _

/- English proof (translation)
Establish `h1 : (c • J.map e).det ≠ 0`. Introduce `h0`. Take `⟨y, hy, hMy⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Establish `hx : star y ≠ 0` using `fun h => hy (by simpa using congrArg star h)`. Use `hθ.2.2 (star y) hx` as an intermediate fact.

Rewrite `this` using `[star_star, hMy, dotProduct_zero, Complex.zero_re]`. Conclude with `lt_irrefl _ this`. Establish `h2 : J.det ≠ 0`. Introduce `h0`. Apply `h1` to reduce the goal to its premises.

Establish `hd : (J.map e).det = e J.det` using `(RingHom.map_det e J).symm`. Rewrite using `[Matrix.det_smul, hd, h0, map_zero, mul_zero]`. Establish `hd : (J.map τ).det = τ J.det` using `(AlgHom.map_det τ J).symm`. Rewrite using `[isUnit_iff_ne_zero, hd]`. Conclude with `(map_ne_zero τ).2 h2`.
-/
theorem isUnit_det_of_cartan (J : Matrix (Fin n) (Fin n) E) (τ : E →ₐ[F] Fv F v) (e : E →+* ℂ) (c : ℂ) (hc : c ≠ 0)
    (θ : Matrix (Fin n) (Fin n) ℂ) (hθ : IsCartan (c • J.map e) θ) : IsUnit (J.map τ).det := by
  have h1 : (c • J.map e).det ≠ 0 := by
    intro h0
    obtain ⟨y, hy, hMy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hx : star y ≠ 0 := fun h => hy (by simpa using congrArg star h)
    have := hθ.2.2 (star y) hx
    rw [star_star, hMy, dotProduct_zero, Complex.zero_re] at this
    exact lt_irrefl _ this
  have h2 : J.det ≠ 0 := by
    intro h0
    apply h1
    have hd : (J.map e).det = e J.det := (RingHom.map_det e J).symm
    rw [Matrix.det_smul, hd, h0, map_zero, mul_zero]
  have hd : (J.map τ).det = τ J.det := (AlgHom.map_det τ J).symm
  rw [isUnit_iff_ne_zero, hd]
  exact (map_ne_zero τ).2 h2

end GlobalTheory.SplitUnitLift
