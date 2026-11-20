import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LandherrAndLandherrSt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DetEqNormMulOfSelfDualSameSignatureStatement

noncomputable section

open NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.LandherrSignature

/- English proof (translation)
Take `⟨e, P, hP⟩` from `h`. Introduce `h0`. Establish `h1` using `congrArg det hP`. Rewrite `h1` using `[det_mul, det_mul, det_reindex_self, h0, mul_zero, zero_mul, Formalism.UG.Jpq, det_fromBlocks_zero₂₁, det_neg]`. Simplify using `at h1`.

Conclude with `pow_ne_zero q (neg_ne_zero.2 one_ne_zero) h1.symm`.
-/
theorem det_ne_zero_of_hasSignature {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} {p q : ℕ}
    (h : Formalism.UG.HasSignature A p q) : A.det ≠ 0 := by
  obtain ⟨e, P, hP⟩ := h
  intro h0
  have h1 := congrArg det hP
  rw [det_mul, det_mul, det_reindex_self, h0, mul_zero, zero_mul, Formalism.UG.Jpq, det_fromBlocks_zero₂₁, det_neg] at h1
  simp at h1
  exact pow_ne_zero q (neg_ne_zero.2 one_ne_zero) h1.symm

/- English proof (translation)
Take `⟨e, -⟩` from `id hA`. Establish `key : ∀ C : Matrix n n ℂ, Formalism.UG.HasSignature C p q → ∃ R : Matrix n n ℂ, R.det ≠ 0 ∧ Rᴴ * C * R = (Formalism.UG.Jpq p q).submatrix e e`. Introduce and unpack `C ⟨e', P, hP⟩`. Establish `hP' : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ * C.submatrix e'.symm e'.symm * (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Formalism.UG.Jpq p q` using `hP`. Use `⟨P.val.submatrix e' e, ?_, ?_⟩` and prove the remaining obligations.

Use `IsUnit.ne_zero (isUnit_det_of_right_inverse (B := P.inv.submatrix e e') ?_)` and prove the remaining obligations. Rewrite using `[submatrix_mul_equiv, P.val_inv, submatrix_one_equiv]`. Establish `: C = (C.submatrix e'.symm e'.symm).submatrix e' e'` using `by simp`. Rewrite using `[this, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, hP']`. Take `⟨R, hR, h1⟩` from `key A hA`.

Take `⟨S, hS, h2⟩` from `key B hB`. Establish `hu : IsUnit S.det` using `hS.isUnit`. Use `⟨R * S⁻¹, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[det_mul]`. Conclude with `mul_ne_zero hR (isUnit_nonsing_inv_det _ hu).ne_zero`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = (S * S⁻¹)ᴴ * B * (S * S⁻¹) := by`. Rewrite using `[h1, ← h2]`. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`.

Use `_ = B := by rw [mul_nonsing_inv _ hu]; simp`.
-/
theorem congr_of_hasSignature {n : Type} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ} {p q : ℕ}
    (hA : Formalism.UG.HasSignature A p q) (hB : Formalism.UG.HasSignature B p q) :
    ∃ Q : Matrix n n ℂ, Q.det ≠ 0 ∧ Qᴴ * A * Q = B := by
  obtain ⟨e, -⟩ := id hA
  have key : ∀ C : Matrix n n ℂ, Formalism.UG.HasSignature C p q →
      ∃ R : Matrix n n ℂ, R.det ≠ 0 ∧ Rᴴ * C * R = (Formalism.UG.Jpq p q).submatrix e e := by
    rintro C ⟨e', P, hP⟩
    have hP' : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ * C.submatrix e'.symm e'.symm *
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Formalism.UG.Jpq p q := hP
    refine ⟨P.val.submatrix e' e, ?_, ?_⟩
    · refine IsUnit.ne_zero (isUnit_det_of_right_inverse (B := P.inv.submatrix e e') ?_)
      rw [submatrix_mul_equiv, P.val_inv, submatrix_one_equiv]
    · have : C = (C.submatrix e'.symm e'.symm).submatrix e' e' := by simp
      rw [this, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, hP']
  obtain ⟨R, hR, h1⟩ := key A hA
  obtain ⟨S, hS, h2⟩ := key B hB
  have hu : IsUnit S.det := hS.isUnit
  refine ⟨R * S⁻¹, ?_, ?_⟩
  · rw [det_mul]
    exact mul_ne_zero hR (isUnit_nonsing_inv_det _ hu).ne_zero
  · calc (R * S⁻¹)ᴴ * A * (R * S⁻¹) = S⁻¹ᴴ * (Rᴴ * A * R) * S⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (S * S⁻¹)ᴴ * B * (S * S⁻¹) := by
          rw [h1, ← h2]
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = B := by rw [mul_nonsing_inv _ hu]; simp

/- English proof (translation)
Simplify using `only [Module.Basis.equivFun_symm_apply, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, starRingEnd_apply, dotProduct, mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring`.
-/
theorem form_eq {E V n : Type} [Field E] [StarRing E] [AddCommGroup V] [Module E V] [Fintype n]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (b : Module.Basis n E V) (x y : n → E) :
    h (b.equivFun.symm x) (b.equivFun.symm y) = star x ⬝ᵥ ((Matrix.of fun i j => h (b i) (b j)) *ᵥ y) := by
  simp only [Module.Basis.equivFun_symm_apply, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, starRingEnd_apply, dotProduct, mulVec, Matrix.of_apply,
    Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

/- English proof (translation)
Take `⟨z, hz⟩` from `hn`. Take `⟨P, hP, h⟩` from `GlobalTheory.QNorm.landherr_and_landherrSt.1 E n G G' (fun a b => congrFun (congrFun hG b) a) (fun a b => congrFun (congrFun hG' b) a) hd hd' (fun τ => by`. Take `⟨Q, hQ, h⟩` from `hs τ`. Use `⟨Q.map (starRingEnd ℂ), ?_, ?_⟩` and prove the remaining obligations. Establish `: (Q.map (starRingEnd ℂ)).det = starRingEnd ℂ Q.det` using `(RingHom.map_det (starRingEnd ℂ) Q).symm`.

Rewrite using `[this]`. Conclude with `(map_ne_zero _).mpr hQ`. Rewrite using `[← h]`. Use `congr 1`. Use extensionality with `a b`.

Use the proof step `simp)`. Use the proof step `⟨z, by rw [div_eq_iff hd']; exact hz⟩`. Use `⟨P.map ReciprocityTheory.ChartRestriction.G.FD.cc, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.Published.det_map_cc]`. Conclude with `GlobalTheory.Published.cc_ne_zero hP`.

Rewrite using `[h]`. Use `congr 2`. Use extensionality with `a b`. Conclude with `star_star (P b a)`.
-/
theorem congr_of_det_norm {n : ℕ} (G G' : Matrix (Fin n) (Fin n) E) (hG : Gᴴ = G) (hG' : G'ᴴ = G')
    (hd : G.det ≠ 0) (hd' : G'.det ≠ 0) (hn : ∃ z : E, G.det = z * star z * G'.det)
    (hs : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ Qᴴ * G.map τ * Q = G'.map τ) :
    ∃ P : Matrix (Fin n) (Fin n) E, P.det ≠ 0 ∧ Pᴴ * G * P = G' := by
  obtain ⟨z, hz⟩ := hn
  obtain ⟨P, hP, h⟩ := GlobalTheory.QNorm.landherr_and_landherrSt.1 E n G G'
    (fun a b => congrFun (congrFun hG b) a) (fun a b => congrFun (congrFun hG' b) a) hd hd'
    (fun τ => by
      obtain ⟨Q, hQ, h⟩ := hs τ
      refine ⟨Q.map (starRingEnd ℂ), ?_, ?_⟩
      · have : (Q.map (starRingEnd ℂ)).det = starRingEnd ℂ Q.det := (RingHom.map_det (starRingEnd ℂ) Q).symm
        rw [this]
        exact (map_ne_zero _).mpr hQ
      · rw [← h]
        congr 1
        ext a b
        simp)
    ⟨z, by rw [div_eq_iff hd']; exact hz⟩
  refine ⟨P.map ReciprocityTheory.ChartRestriction.G.FD.cc, ?_, ?_⟩
  · rw [GlobalTheory.Published.det_map_cc]
    exact GlobalTheory.Published.cc_ne_zero hP
  · rw [h]
    congr 2
    ext a b
    exact star_star (P b a)

/- English proof (translation)
Take `⟨z, hz⟩` from `GlobalTheory.T.det_eq_norm_mul_of_selfDual_same_signature E hc W₁ W₂ h₁ h₂ hr hs`. Set `c : Fin W₁.rank ≃ Fin W₂.rank` to `finCongr hr`. Establish `hH : ∀ W : HSpace E, W.gramᴴ = W.gram` using `fun W => by`. Use extensionality with `a b`. Conclude with `W.herm.eq _ _`.

Establish `hd : ∀ W : HSpace E, W.SigOK → W.gram.det ≠ 0` using `fun W hW h0 => by`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Use `det_ne_zero_of_hasSignature (hW τ) ?_` and prove the remaining obligations. Establish `: (W.gram.map τ).det = τ W.gram.det` using `(RingHom.map_det τ W.gram).symm`. Rewrite using `[this, h0, map_zero]`.

Take `⟨P, hP0, hP⟩` from `congr_of_det_norm (W₂.gram.submatrix c c) W₁.gram (by rw [conjTranspose_submatrix, hH]) (hH W₁) (by rw [det_submatrix_equiv_self]; exact hd W₂ h₂) (hd W₁ h₁) ⟨z, by rw [det_submatrix_equiv_self]; exact hz⟩ (fun τ => by`. Use `congr_of_hasSignature ?_ (h₁ τ)` and prove the remaining obligations. Rewrite using `[hs τ]`. Take `⟨e, Q, hQ⟩` from `h₂ τ`. Use `⟨c.trans e, Q, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hQ]`. Use `congr 2)`. Set `b₂` to `W₂.frame.reindex c.symm`. Establish `e₂ : (Matrix.of fun i j => W₂.hT (b₂ i) (b₂ j)) = W₂.gram.submatrix c c`. Use extensionality with `i j`.

Simplify using `[b₂, HSpace.gram]`. Use `⟨(W₁.frame.equivFun.trans (Matrix.toLinearEquiv' P (Matrix.invertibleOfIsUnitDet P hP0.isUnit))).trans b₂.equivFun.symm, fun x y => ?_⟩` and prove the remaining obligations. Take `⟨u, rfl⟩` from `W₁.frame.equivFun.symm.surjective x`. Take `⟨v, rfl⟩` from `W₁.frame.equivFun.symm.surjective y`. Simplify using `only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]`.

Rewrite using `[form_eq, form_eq, e₂]`. Express the relevant statement in the definitionally equal form `star (P *ᵥ u) ⬝ᵥ (_ *ᵥ (P *ᵥ v)) = star u ⬝ᵥ (W₁.gram *ᵥ v)`. Rewrite using `[star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hP]`.
-/
theorem exists_isometry (hc : Formalism.HermitianLatticesTheory.IsCMUnram E) (W₁ W₂ : HSpace E) (h₁ : W₁.SigOK) (h₂ : W₂.SigOK)
    (hr : W₁.rank = W₂.rank) (hs : ∀ τ, W₁.sig τ = W₂.sig τ) :
    ∃ φ : W₁.V ≃ₗ[E] W₂.V, ∀ x y, W₂.hT (φ x) (φ y) = W₁.hT x y := by
  obtain ⟨z, hz⟩ := GlobalTheory.T.det_eq_norm_mul_of_selfDual_same_signature E hc W₁ W₂ h₁ h₂ hr hs
  let c : Fin W₁.rank ≃ Fin W₂.rank := finCongr hr
  have hH : ∀ W : HSpace E, W.gramᴴ = W.gram := fun W => by
    ext a b
    exact W.herm.eq _ _
  have hd : ∀ W : HSpace E, W.SigOK → W.gram.det ≠ 0 := fun W hW h0 => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine det_ne_zero_of_hasSignature (hW τ) ?_
    have : (W.gram.map τ).det = τ W.gram.det := (RingHom.map_det τ W.gram).symm
    rw [this, h0, map_zero]
  obtain ⟨P, hP0, hP⟩ := congr_of_det_norm (W₂.gram.submatrix c c) W₁.gram
    (by rw [conjTranspose_submatrix, hH]) (hH W₁) (by rw [det_submatrix_equiv_self]; exact hd W₂ h₂) (hd W₁ h₁)
    ⟨z, by rw [det_submatrix_equiv_self]; exact hz⟩
    (fun τ => by
      refine congr_of_hasSignature ?_ (h₁ τ)
      rw [hs τ]
      obtain ⟨e, Q, hQ⟩ := h₂ τ
      refine ⟨c.trans e, Q, ?_⟩
      rw [← hQ]
      congr 2)
  let b₂ := W₂.frame.reindex c.symm
  have e₂ : (Matrix.of fun i j => W₂.hT (b₂ i) (b₂ j)) = W₂.gram.submatrix c c := by
    ext i j
    simp [b₂, HSpace.gram]
  refine ⟨(W₁.frame.equivFun.trans (Matrix.toLinearEquiv' P (Matrix.invertibleOfIsUnitDet P hP0.isUnit))).trans
    b₂.equivFun.symm, fun x y => ?_⟩
  obtain ⟨u, rfl⟩ := W₁.frame.equivFun.symm.surjective x
  obtain ⟨v, rfl⟩ := W₁.frame.equivFun.symm.surjective y
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [form_eq, form_eq, e₂]
  change star (P *ᵥ u) ⬝ᵥ (_ *ᵥ (P *ᵥ v)) = star u ⬝ᵥ (W₁.gram *ᵥ v)
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hP]

end CM

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D` and use `haveI : IsCMField D.host.E := D.host.isCMField_hostE fun W₁ W₂ => exists_isometry (E := D.host.E) D.sp.cm.cmUnram W₁ W₂`.
-/
theorem exists_isometry_host : ∀ (D : D7) (W₁ W₂ : HSpace D.host.E), W₁.SigOK → W₂.SigOK → W₁.rank = W₂.rank →
    (∀ τ, W₁.sig τ = W₂.sig τ) →
    ∃ φ : W₁.V ≃ₗ[D.host.E] W₂.V, ∀ x y, W₂.hT (φ x) (φ y) = W₁.hT x y := fun D =>
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  fun W₁ W₂ => exists_isometry (E := D.host.E) D.sp.cm.cmUnram W₁ W₂

end GlobalTheory.LandherrSignature
