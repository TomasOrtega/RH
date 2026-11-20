import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationCmExtensionStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.ThKUniqMax

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨hn, A, hA⟩` from `h`. Set `e : Fin r ⊕ Fin s ≃ Fin n` to `finSumFinEquiv.trans (finCongr hn)`. Establish `key : (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star = (Aᵀ * M * A.map star).submatrix e.symm e.symm`. Use extensionality with `i j`. Both sides reduce to the same expression.

Establish `hd` using `congrArg Matrix.det key`. Rewrite `hd` using `[Matrix.det_submatrix_equiv_self, hA, Matrix.det_mul, Matrix.det_mul]`. Introduce `h0`. Rewrite `hd` using `[h0]`. Simplify using `[Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg] at hd`.

Conclude with `pow_ne_zero _ (by norm_num) hd.symm`.
-/
theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
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

/- English proof (translation)
Introduce `h0`. Apply `h` to reduce the goal to its premises. Rewrite using `[show J.map f = f.mapMatrix J from rfl, ← RingHom.map_det, h0, map_zero]`.
-/
theorem det_ne_zero_of_map {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (f : E →+* ℂ) (h : (J.map f).det ≠ 0) : J.det ≠ 0 := by
  intro h0
  apply h
  rw [show J.map f = f.mapMatrix J from rfl, ← RingHom.map_det, h0, map_zero]

/- English proof (translation)
Introduce `u`. Rewrite using `[MonoidHom.div_apply, Circle.coe_div, h u, h' u]`. Use `split_ifs`. Simplify using the standard rewrite rules. Rewrite using `[div_eq_mul_inv, ← inv_pow, inv_neg_one, ← pow_add]`.
-/
theorem resEtaPow_div {R Eₐ : Type} [CommRing R] [CommRing Eₐ] [Algebra R Eₐ] {K : Subgroup Rˣ} {χ χ' : Eₐˣ →* Circle}
    {m m' : ℕ} (h : ResEtaPow K χ m) (h' : ResEtaPow K χ' m') : ResEtaPow K (χ / χ') (m + m') := by
  intro u
  rw [MonoidHom.div_apply, Circle.coe_div, h u, h' u]
  split_ifs
  · simp
  · rw [div_eq_mul_inv, ← inv_pow, inv_neg_one, ← pow_add]

/- English proof (translation)
Use `⟨?_, fun x => ?_⟩` and prove the remaining obligations. Conclude with `h.1.div' h'.1`. Rewrite using `[MonoidHom.div_apply, h.2 x, h'.2 x, div_one]`.
-/
theorem isHecke_div {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') := by
  refine ⟨?_, fun x => ?_⟩
  · exact h.1.div' h'.1
  · rw [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]

/- English proof (translation)
Introduce `hK F E _ _ _ _ _ σ B a a' G X om om' hT v P P' hP hP'`. Set `w0` to `(inferInstance : Nonempty (InfinitePlace F)).some`. Establish `hVd : G.V.J.det ≠ 0` using `det_ne_zero_of_map _ (B.emb w0).1 (det_ne_zero_of_hasSig (hT.geo.hV.sig w0))`. Establish `hWd : G.W.J.det ≠ 0`. Use `det_ne_zero_of_hasSig (hT.geo.hW.sig w0)` as an intermediate fact.

Rewrite `this` using `[Matrix.det_smul]`. Conclude with `det_ne_zero_of_map _ _ (right_ne_zero_of_mul this)`. Conclude with `GlobalTheory.T.weil_representation_cm_extension hK.base hK.howeDualityUnitary hK.minguezThetaGL F E σ hT.base.cm a (a + a') G.V G.W G.M B.ψ X.β (X.β / X.α) om hT.base.std hT.geo.hV.herm hVd hT.geo.hW.skew hWd hT.chars.resβ (resEtaPow_div hT.chars.resβ hT.chars.resα) hT.chars.heck …`.
-/
theorem uniqMax : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (P P' : Submodule ℂ ((Fin a × Fin (a + a') → Fv F v) → ℂ)), Maximal (fun Q => GlobalTheory.Published.ThetaSub om v Q ∧ Q ≠ SB _) P → Maximal (fun Q => GlobalTheory.Published.ThetaSub om v Q ∧ Q ≠ SB _) P' → P = P' := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' hT v P P' hP hP'
  let w0 := (inferInstance : Nonempty (InfinitePlace F)).some
  have hVd : G.V.J.det ≠ 0 := det_ne_zero_of_map _ (B.emb w0).1 (det_ne_zero_of_hasSig (hT.geo.hV.sig w0))
  have hWd : G.W.J.det ≠ 0 := by
    have := det_ne_zero_of_hasSig (hT.geo.hW.sig w0)
    rw [Matrix.det_smul] at this
    exact det_ne_zero_of_map _ _ (right_ne_zero_of_mul this)
  exact GlobalTheory.T.weil_representation_cm_extension hK.base hK.howeDualityUnitary hK.minguezThetaGL F E σ hT.base.cm a (a + a') G.V G.W G.M B.ψ
    X.β (X.β / X.α) om hT.base.std hT.geo.hV.herm hVd hT.geo.hW.skew hWd hT.chars.resβ
    (resEtaPow_div hT.chars.resβ hT.chars.resα) hT.chars.heckeβ (isHecke_div hT.chars.heckeβ hT.chars.heckeα) hT.weil v P P' hP hP'

end GlobalTheory.ThKUniqMax

end
