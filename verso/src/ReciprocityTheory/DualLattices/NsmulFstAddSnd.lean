import ReciprocityTheory.DualLattices.InstAddCommMonoidFibreFst

noncomputable section

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

namespace BX

variable (B : BX R₀) {R : LAlg R₀}

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Apply `eq_of_heq` to reduce the goal to its premises. Use `show HEq (B.tr1 _ (B.zero1 (y + y'))) (B.add2 (B.tr1 _ (B.zero1 y)) (B.tr1 _ (B.zero1 y')))`. Use `(B.castFst_heq _ _).trans ?_` and prove the remaining obligations.

Use `(heq_of_eq (B.zeroFst_addSnd y y')).symm.trans ?_` and prove the remaining obligations. Conclude with `B.addSnd_hcongr (zero_nsmul x).symm rfl rfl (B.castFst_heq _ _).symm (B.castFst_heq _ _).symm`. Consider the case `succ n ih`. Apply `eq_of_heq` to reduce the goal to its premises. Use `show HEq (B.tr1 _ (B.add1 (B.nsmul1 (B.add2 u u') n) (B.add2 u u'))) (B.add2 (B.tr1 _ (B.add1 (B.nsmul1 u n) u)) (B.tr1 _ (B.add1 (B.nsmul1 u' n) u')))`.

Use `(B.castFst_heq _ _).trans ?_` and prove the remaining obligations. Rewrite using `[ih, ← B.interchange]`. Conclude with `B.addSnd_hcongr (succ_nsmul x n).symm rfl rfl (B.castFst_heq _ _).symm (B.castFst_heq _ _).symm`.
-/
lemma nsmulFst_addSnd {x y y' : B.G R} (u : B.P R x y) (u' : B.P R x y') (n : ℕ) :
    B.nsmul1 (B.add2 u u') n = B.add2 (B.nsmul1 u n) (B.nsmul1 u' n) := by
  induction n with
  | zero =>
    apply eq_of_heq
    show HEq (B.tr1 _ (B.zero1 (y + y')))
      (B.add2 (B.tr1 _ (B.zero1 y)) (B.tr1 _ (B.zero1 y')))
    refine (B.castFst_heq _ _).trans ?_
    refine (heq_of_eq (B.zeroFst_addSnd y y')).symm.trans ?_
    exact B.addSnd_hcongr (zero_nsmul x).symm rfl rfl
      (B.castFst_heq _ _).symm (B.castFst_heq _ _).symm
  | succ n ih =>
    apply eq_of_heq
    show HEq (B.tr1 _ (B.add1 (B.nsmul1 (B.add2 u u') n) (B.add2 u u')))
      (B.add2 (B.tr1 _ (B.add1 (B.nsmul1 u n) u))
        (B.tr1 _ (B.add1 (B.nsmul1 u' n) u')))
    refine (B.castFst_heq _ _).trans ?_
    rw [ih, ← B.interchange]
    exact B.addSnd_hcongr (succ_nsmul x n).symm rfl rfl
      (B.castFst_heq _ _).symm (B.castFst_heq _ _).symm

end BX

end ReciprocityTheory.PGsh
