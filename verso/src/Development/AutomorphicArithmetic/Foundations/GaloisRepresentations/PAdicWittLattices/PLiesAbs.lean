import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

/- English proof (translation)
Introduce `hF hB hP B R _ T hT Z Y C D pZ pY pC pD π hπ sg tg htg s t ht κ h d m hsg hs hκt hsd hℓ tr trg htr htrg x`. Establish `hpb : IsPullback (pullback.snd π s) (pullback.fst π s) s π` using `(IsPullback.of_hasPullback π s).flip`. Establish `hfst : FEt (pullback.fst π s) d` using `hF.1 _ _ s π d hpb hsd`. Use `haveI : IsFinite (pullback.fst π s) := hfst.1`. Use `haveI : Etale (pullback.fst π s) := hfst.2.1`.

Take `⟨tr1, htr1⟩` from `hT.tr pZ (pullback.fst π s ≫ pZ) (pullback.fst π s) rfl`. Establish `hsndp : pullback.snd π s ≫ pD = pullback.fst π s ≫ pZ`. Rewrite using `[← hs, ← Category.assoc, ← pullback.condition, Category.assoc, hπ]`. Establish `base` using `hB T hT pY pD pZ (pullback.fst π s ≫ pZ) (pullback.snd π s) (pullback.fst π s) s π d hsndp hπ rfl hpb hsd tr tr1 htr htr1 ((T.pull t ht) x)`. Establish `htrg' : T.IsTr pZ pC (pullback.lift sg κ h ≫ pullback.fst π s) trg`.

Rewrite using `[pullback.lift_fst]`. Conclude with `htrg`. Establish `hℓq : pullback.lift sg κ h ≫ (pullback.fst π s ≫ pZ) = pC`. Rewrite using `[← Category.assoc, pullback.lift_fst, hsg]`. Establish `push` using `hP T hT pZ (pullback.fst π s ≫ pZ) pC (pullback.lift sg κ h) (pullback.fst π s) d m hℓq rfl hfst hℓ tr1 trg htr1 htrg' ((T.pull (pullback.snd π s) hsndp) ((T.pull t ht) x))`.

Establish `hcongr : ∀ {W : Scheme} {r : W ⟶ B} (f f' : W ⟶ Y) (e : f = f') (hf : f ≫ pY = r) (hf' : f' ≫ pY = r), T.pull f hf x = T.pull f' hf' x`. Introduce `W r f f' e hf hf'`. Substitute `e` using the available equality. Both sides reduce to the same expression. Establish `h1 : (tg ≫ π) ≫ pY = pC` using `by rw [Category.assoc, hπ, htg]`.

Establish `h2 : (pullback.snd π s ≫ t) ≫ pY = pullback.fst π s ≫ pZ` using `by rw [Category.assoc, ht, hsndp]`. Establish `h3 : (pullback.lift sg κ h ≫ pullback.snd π s ≫ t) ≫ pY = pC`. Rewrite using `[Category.assoc, h2, hℓq]`. Establish `hmor : tg ≫ π = pullback.lift sg κ h ≫ pullback.snd π s ≫ t`. Rewrite using `[← Category.assoc, pullback.lift_snd, hκt]`.

Rewrite using `[← T.pull_comp tg π htg hπ h1, hcongr _ _ hmor h1 h3, T.pull_comp (pullback.lift sg κ h) (pullback.snd π s ≫ t) hℓq h2 h3, T.pull_comp (pullback.snd π s) t hsndp ht h2, push, base]`.
-/
theorem UpperTheory.Gal.G3.pLiesAbs :
    FEtBasic → TrBase.{u} → TrPushM.{u} → LiesAbs.{u} := by
  intro hF hB hP B R _ T hT Z Y C D pZ pY pC pD π hπ sg tg htg s t ht κ h d m hsg hs hκt hsd hℓ tr trg htr htrg x
  have hpb : IsPullback (pullback.snd π s) (pullback.fst π s) s π := (IsPullback.of_hasPullback π s).flip
  have hfst : FEt (pullback.fst π s) d := hF.1 _ _ s π d hpb hsd
  haveI : IsFinite (pullback.fst π s) := hfst.1
  haveI : Etale (pullback.fst π s) := hfst.2.1
  obtain ⟨tr1, htr1⟩ := hT.tr pZ (pullback.fst π s ≫ pZ) (pullback.fst π s) rfl
  have hsndp : pullback.snd π s ≫ pD = pullback.fst π s ≫ pZ := by
    rw [← hs, ← Category.assoc, ← pullback.condition, Category.assoc, hπ]
  have base := hB T hT pY pD pZ (pullback.fst π s ≫ pZ) (pullback.snd π s) (pullback.fst π s) s π d
    hsndp hπ rfl hpb hsd tr tr1 htr htr1 ((T.pull t ht) x)
  have htrg' : T.IsTr pZ pC (pullback.lift sg κ h ≫ pullback.fst π s) trg := by
    rw [pullback.lift_fst]; exact htrg
  have hℓq : pullback.lift sg κ h ≫ (pullback.fst π s ≫ pZ) = pC := by
    rw [← Category.assoc, pullback.lift_fst, hsg]
  have push := hP T hT pZ (pullback.fst π s ≫ pZ) pC (pullback.lift sg κ h) (pullback.fst π s) d m hℓq rfl
    hfst hℓ tr1 trg htr1 htrg' ((T.pull (pullback.snd π s) hsndp) ((T.pull t ht) x))
  have hcongr : ∀ {W : Scheme} {r : W ⟶ B} (f f' : W ⟶ Y) (e : f = f') (hf : f ≫ pY = r) (hf' : f' ≫ pY = r),
      T.pull f hf x = T.pull f' hf' x := by
    intro W r f f' e hf hf'
    subst e
    rfl
  have h1 : (tg ≫ π) ≫ pY = pC := by rw [Category.assoc, hπ, htg]
  have h2 : (pullback.snd π s ≫ t) ≫ pY = pullback.fst π s ≫ pZ := by rw [Category.assoc, ht, hsndp]
  have h3 : (pullback.lift sg κ h ≫ pullback.snd π s ≫ t) ≫ pY = pC := by
    rw [Category.assoc, h2, hℓq]
  have hmor : tg ≫ π = pullback.lift sg κ h ≫ pullback.snd π s ≫ t := by
    rw [← Category.assoc, pullback.lift_snd, hκt]
  rw [← T.pull_comp tg π htg hπ h1, hcongr _ _ hmor h1 h3,
    T.pull_comp (pullback.lift sg κ h) (pullback.snd π s ≫ t) hℓq h2 h3,
    T.pull_comp (pullback.snd π s) t hsndp ht h2, push, base]
