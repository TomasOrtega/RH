import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsConjIntNum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial NumbersDVR

noncomputable section

namespace ConjIntNum

variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type} [Field F]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
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
Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Assume the hypotheses and unpack their components. Supply the required witnesses or components.
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
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

A detailed English derivation is pending.
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
Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem finrank_gradedPiece (τ : F ≃+* F) (J : Ideal (MRing ι F)) (m : K → ℕ) :
    Module.finrank F (gradedPiece (J.map (MvPolynomial.map (τ : F →+* F))) m) =
      Module.finrank F (gradedPiece J m) := by
  have h := rank_eq_of_equiv_equiv (τ : F → F) (pieceEquiv τ J m) τ.bijective
    (fun c x => Subtype.ext (quotEquiv_smul τ J c x))
  simp only [Module.finrank, h]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem hilbFn_map (τ : F ≃+* F) (J : Ideal (MRing ι F)) :
    hilbFn (J.map (MvPolynomial.map (τ : F →+* F))) = hilbFn J := by
  funext m
  unfold hilbFn
  split_ifs
  · rw [finrank_gradedPiece]
  · rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem proof : ConjIntNum.Statement := by
  intro K _ ι F _ τ J n bs
  unfold NumbersDVR.intNum
  rw [hilbFn_map]

end ConjIntNum

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
