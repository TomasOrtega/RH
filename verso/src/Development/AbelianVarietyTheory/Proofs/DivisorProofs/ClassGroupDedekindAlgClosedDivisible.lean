import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicDivisibleDedekindFiniteTypeAlgClosedStatement
open Polynomial

namespace GlobalTheory.PicDiv

/- English proof (translation)
Introduce `k B _ _ _ _ _ _ _ q hq c`. Take `⟨d, hd⟩` from `GlobalTheory.T.pic_divisible_dedekind_finiteType_algClosed k B q (Ne.isUnit hq) (ClassGroup.equivPic B c)`. Use `⟨(ClassGroup.equivPic B).symm d, ?_⟩` and prove the remaining obligations. Apply `(ClassGroup.equivPic B).injective` to reduce the goal to its premises. Rewrite using `[map_pow, MulEquiv.apply_symm_apply, hd]`.
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
