import Development.EtaleCohomology.EtaleSheaves.ChowLCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut

namespace LateralTheory.E.IterBCPf

/- English proof (translation)
Proceed by induction on `hq with`. Consider the case `iso e he`. Introduce `X P' a q' g w`. Conclude with `IterLine.iso _ (w.isIso_snd_of_isIso he)`. Consider the case `comp l k hl hk ih`.

Introduce `X P' a q' g w`. Establish `hb : IsPullback (pullback.fst k g) (pullback.snd k g) k g` using `IsPullback.of_hasPullback k g`. Set `m : P' ⟶ pullback k g` to `pullback.lift (a ≫ l) q' (by rw [Category.assoc]; exact w.w)`. Establish `hm : q' = m ≫ pullback.snd k g` using `(pullback.lift_snd _ _ _).symm`. Establish `ht : IsPullback a m l (pullback.fst k g)`.

Use `IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm hb` and prove the remaining obligations. Rewrite using `[← hm]`. Conclude with `w`. Rewrite using `[hm]`. Conclude with `IterLine.comp m _ (IsLine.bc hl ht) (ih hb)`.
-/
theorem iterLine_of_isPullback {S P : Scheme.{0}} {q : P ⟶ S} (hq : IterLine q) :
    ∀ {X P' : Scheme.{0}} {a : P' ⟶ P} {q' : P' ⟶ X} {g : X ⟶ S}, IsPullback a q' q g → IterLine q' := by
  induction hq with
  | iso e he =>
    intro X P' a q' g w
    exact IterLine.iso _ (w.isIso_snd_of_isIso he)
  | comp l k hl hk ih =>
    intro X P' a q' g w
    have hb : IsPullback (pullback.fst k g) (pullback.snd k g) k g := IsPullback.of_hasPullback k g
    let m : P' ⟶ pullback k g := pullback.lift (a ≫ l) q' (by rw [Category.assoc]; exact w.w)
    have hm : q' = m ≫ pullback.snd k g := (pullback.lift_snd _ _ _).symm
    have ht : IsPullback a m l (pullback.fst k g) := by
      refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm hb
      rw [← hm]; exact w
    rw [hm]
    exact IterLine.comp m _ (IsLine.bc hl ht) (ih hb)

/- English proof (translation)
Introduce `P S X q g hq`. Conclude with `iterLine_of_isPullback hq (IsPullback.of_hasPullback g q).flip`.
-/
theorem IterBC_of : IterBC := by
  intro P S X q g hq
  exact iterLine_of_isPullback hq (IsPullback.of_hasPullback g q).flip

end LateralTheory.E.IterBCPf

end
