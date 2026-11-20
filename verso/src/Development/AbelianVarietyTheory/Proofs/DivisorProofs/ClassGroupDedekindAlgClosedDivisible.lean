import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicDivisibleDedekindFiniteTypeAlgClosedStatement
open Polynomial

namespace GlobalTheory.PicDiv

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem classGroup_divisible : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B]
    [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), (q : k) ≠ 0 →
    ∀ c : ClassGroup B, ∃ d : ClassGroup B, d ^ q = c := by
  intro k B _ _ _ _ _ _ _ q hq c
  obtain ⟨d, hd⟩ := GlobalTheory.T.pic_divisible_dedekind_finiteType_algClosed k B q (Ne.isUnit hq) (ClassGroup.equivPic B c)
  refine ⟨(ClassGroup.equivPic B).symm d, ?_⟩
  apply (ClassGroup.equivPic B).injective
  rw [map_pow, MulEquiv.apply_symm_apply, hd]

end GlobalTheory.PicDiv
