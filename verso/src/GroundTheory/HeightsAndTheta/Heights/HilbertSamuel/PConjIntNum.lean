import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsConjIntNum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial NumbersDVR

noncomputable section

namespace ConjIntNum

variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type} [Field F]

/- English proof (translation)
Introduce `d hd`. Rewrite `hd` using `[coeff_map]`. Conclude with `hf fun h => hd (by rw [h, map_zero])`.
-/
theorem isWeightedHomogeneous_map {σ M : Type*} [AddCommMonoid M] (w : σ → M) (τ : F →+* F)
    {f : MvPolynomial σ F} {m : M} (hf : IsWeightedHomogeneous w f m) :
    IsWeightedHomogeneous w (MvPolynomial.map τ f) m := by
  intro d hd
  rw [coeff_map] at hd
  exact hf fun h => hd (by rw [h, map_zero])

def quotEquiv (τ : F ≃+* F) (J : Ideal (MRing ι F)) :
    (MRing ι F ⧸ J) ≃+* (MRing ι F ⧸ J.map (MvPolynomial.map (τ : F →+* F))) :=
  Ideal.quotientEquiv J _ (MvPolynomial.mapEquiv _ τ) (by
    congr 1)

omit [DecidableEq K] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem quotEquiv_mk (τ : F ≃+* F) (J : Ideal (MRing ι F)) (f : MRing ι F) :
    quotEquiv τ J (Ideal.Quotient.mk J f) = Ideal.Quotient.mk _ (MvPolynomial.map (τ : F →+* F) f) :=
  rfl

/- English proof (translation)
Simplify using `only [gradedPiece, Submodule.mem_map, mem_weightedHomogeneousSubmodule]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg, hgx⟩`. Use `⟨MvPolynomial.map (τ.symm : F →+* F) g, isWeightedHomogeneous_map _ _ hg, ?_⟩` and prove the remaining obligations. Use `congrArg (quotEquiv τ J).symm hgx` as an intermediate fact.

Rewrite `this` using `[RingEquiv.symm_apply_apply]`. Rewrite using `[← this]`. Both sides reduce to the same expression. Introduce and unpack `⟨f, hf, rfl⟩`. Conclude with `⟨MvPolynomial.map (τ : F →+* F) f, isWeightedHomogeneous_map _ _ hf, rfl⟩`.
-/
theorem mem_gradedPiece_iff (τ : F ≃+* F) (J : Ideal (MRing ι F)) (m : K → ℕ) (x : MRing ι F ⧸ J) :
    quotEquiv τ J x ∈ gradedPiece (J.map (MvPolynomial.map (τ : F →+* F))) m ↔ x ∈ gradedPiece J m := by
  simp only [gradedPiece, Submodule.mem_map, mem_weightedHomogeneousSubmodule]
  constructor
  · rintro ⟨g, hg, hgx⟩
    refine ⟨MvPolynomial.map (τ.symm : F →+* F) g, isWeightedHomogeneous_map _ _ hg, ?_⟩
    have := congrArg (quotEquiv τ J).symm hgx
    rw [RingEquiv.symm_apply_apply] at this
    rw [← this]
    rfl
  · rintro ⟨f, hf, rfl⟩
    exact ⟨MvPolynomial.map (τ : F →+* F) f, isWeightedHomogeneous_map _ _ hf, rfl⟩

def pieceEquiv (τ : F ≃+* F) (J : Ideal (MRing ι F)) (m : K → ℕ) :
    gradedPiece J m ≃+ gradedPiece (J.map (MvPolynomial.map (τ : F →+* F))) m where
  toFun x := ⟨quotEquiv τ J x, (mem_gradedPiece_iff τ J m x).2 x.2⟩
  invFun y := ⟨(quotEquiv τ J).symm y,
    (mem_gradedPiece_iff τ J m _).1 (by rw [RingEquiv.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext (RingEquiv.symm_apply_apply _ _)
  right_inv y := Subtype.ext (RingEquiv.apply_symm_apply _ _)
  map_add' x y := Subtype.ext (map_add _ _ _)

omit [DecidableEq K] in

/- English proof (translation)
Establish `hs : ∀ (I : Ideal (MRing ι F)) (a : F) (g : MRing ι F), a • Ideal.Quotient.mk I g = Ideal.Quotient.mk I (C a * g)` using `fun I a g => by`. Rewrite using `[← smul_eq_C_mul]`. Conclude with `(map_smul (Ideal.Quotient.mkₐ F I) a g).symm`. Take `⟨f, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite using `[hs, quotEquiv_mk, quotEquiv_mk, hs, map_mul, map_C]`.

Both sides reduce to the same expression.
-/
theorem quotEquiv_smul (τ : F ≃+* F) (J : Ideal (MRing ι F)) (c : F) (x : MRing ι F ⧸ J) :
    quotEquiv τ J (c • x) = τ c • quotEquiv τ J x := by
  have hs : ∀ (I : Ideal (MRing ι F)) (a : F) (g : MRing ι F),
      a • Ideal.Quotient.mk I g = Ideal.Quotient.mk I (C a * g) := fun I a g => by
    rw [← smul_eq_C_mul]
    exact (map_smul (Ideal.Quotient.mkₐ F I) a g).symm
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [hs, quotEquiv_mk, quotEquiv_mk, hs, map_mul, map_C]
  rfl

/- English proof (translation)
Establish `h` using `rank_eq_of_equiv_equiv (τ : F → F) (pieceEquiv τ J m) τ.bijective (fun c x => Subtype.ext (quotEquiv_smul τ J c x))`. Simplify using `only [Module.finrank, h]`.
-/
theorem finrank_gradedPiece (τ : F ≃+* F) (J : Ideal (MRing ι F)) (m : K → ℕ) :
    Module.finrank F (gradedPiece (J.map (MvPolynomial.map (τ : F →+* F))) m) =
      Module.finrank F (gradedPiece J m) := by
  have h := rank_eq_of_equiv_equiv (τ : F → F) (pieceEquiv τ J m) τ.bijective
    (fun c x => Subtype.ext (quotEquiv_smul τ J c x))
  simp only [Module.finrank, h]

/- English proof (translation)
Use function extensionality and compare the values at `m`. Unfold `hilbFn`. Use `split_ifs`. Rewrite using `[finrank_gradedPiece]`. Both sides reduce to the same expression.
-/
theorem hilbFn_map (τ : F ≃+* F) (J : Ideal (MRing ι F)) :
    hilbFn (J.map (MvPolynomial.map (τ : F →+* F))) = hilbFn J := by
  funext m
  unfold hilbFn
  split_ifs
  · rw [finrank_gradedPiece]
  · rfl

/- English proof (translation)
Introduce `K _ ι F _ τ J n bs`. Unfold `NumbersDVR.intNum`. Rewrite using `[hilbFn_map]`.
-/
theorem proof : ConjIntNum.Statement := by
  intro K _ ι F _ τ J n bs
  unfold NumbersDVR.intNum
  rw [hilbFn_map]

end ConjIntNum

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
