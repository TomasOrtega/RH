import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HodgeTraceFromLefschetzAndGroupSide

open UpperTheory.Gal.LocalSmoothExtension

set_option maxHeartbeats 1000000 in
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.HodgeCoh in
/- English proof (translation)
Introduce `memop hg htr bcg opbc optr bcs p _ D G L R _ _ gb k T N J g τ θ a b x hx hxe`. Use `letI : Algebra R ℂ := τ.toAlgebra`. Use `⟨b, x, hx, fun j => ?_⟩` and prove the remaining obligations. Take `⟨-, hfin, het, hop⟩` from `memop p D G L R gb k T N J g j`. Use `haveI := hfin`.

Use `haveI := het`. Establish `hΘ` using `bcg (UpperTheory.Gal.G3.hodge ℂ a b) (Spec.map (CommRingCat.ofHom τ)) (hg ℂ a b)`. Establish `hs : (T.tower N g).s j ≫ (T.tower N g).q = (T.tower N g).s j ≫ (T.tower N g).q` using `rfl`. Establish `h2` using `opbc (UpperTheory.Gal.G3.hodge ℂ a b) (Spec.map (CommRingCat.ofHom τ)) (T.tower N g).q ((T.tower N g).s j ≫ (T.tower N g).q) (T.tower N g).q ((T.tower N g).s j) ((T.tower N g).t j) hs ((T.tower N g).comm j) _ (hop _ hΘ)`. Take `⟨hf', he', -⟩` from `bcs (Spec.map (CommRingCat.ofHom τ)) (T.tower N g).q ((T.tower N g).s j ≫ (T.tower N g).q) ((T.tower N g).s j ≫ (T.tower N g).q) ((T.tower N g).s j) hs ((T.tower N g).s j) hs PEmpty (fun e => e.elim) (fun e => e.elim)`.

Use `haveI := hf'`. Use `haveI := he'`. Establish `ht' : UpperTheory.Gal.G3.bcMap (Spec.map (CommRingCat.ofHom τ)) ((T.tower N g).t j) ((T.tower N g).comm j) ≫ pullback.snd (T.tower N g).q (Spec.map (CommRingCat.ofHom τ)) = UpperTheory.Gal.G3.bcMap (Spec.map (CommRingCat.ofHom τ)) ((T.tower N g).s j) hs ≫ pullback.snd (T.tower N …`. Unfold `UpperTheory.Gal.G3.bcMap`. Rewrite using `[pullback.lift_snd, pullback.lift_snd]`.

Establish `htr'` using `htr ℂ a b (pullback.snd (T.tower N g).q (Spec.map (CommRingCat.ofHom τ))) _ (UpperTheory.Gal.G3.bcMap (Spec.map (CommRingCat.ofHom τ)) ((T.tower N g).s j) hs) rfl`. Establish `hA` using `(optr (UpperTheory.Gal.G3.hodge ℂ a b) (hg ℂ a b) _ _ _ _ _ rfl ht' _ htr' _).1 h2`. Establish `e1 : (UpperTheory.Gal.Int.Geo.bcAlong (T.tower N g) τ).s j = UpperTheory.Gal.G3.bcMap (Spec.map (CommRingCat.ofHom τ)) ((T.tower N g).s j) hs` using `rfl`. Use `⟨e1 ▸ hf', e1 ▸ he', Eq.trans ?_ (hxe j)⟩` and prove the remaining obligations. Rewrite using `[hA]`.

Both sides reduce to the same expression.
-/
theorem UpperTheory.Gal.LocalSmoothExtension.occOf_of :
    MemOp → UpperTheory.Gal.G3.HodgeGood → UpperTheory.Gal.G3.HodgeTr → UpperTheory.Gal.G3.BcGood.{0} → UpperTheory.Gal.G3.OpBc.{0} → UpperTheory.Gal.G3.OpTr.{0} → UpperTheory.Gal.G3.BcSplits → OccOf := by
  intro memop hg htr bcg opbc optr bcs p _ D G L R _ _ gb k T N J g τ θ a b x hx hxe
  letI : Algebra R ℂ := τ.toAlgebra
  refine ⟨b, x, hx, fun j => ?_⟩
  obtain ⟨-, hfin, het, hop⟩ := memop p D G L R gb k T N J g j
  haveI := hfin
  haveI := het
  have hΘ := bcg (UpperTheory.Gal.G3.hodge ℂ a b) (Spec.map (CommRingCat.ofHom τ)) (hg ℂ a b)
  have hs : (T.tower N g).s j ≫ (T.tower N g).q = (T.tower N g).s j ≫ (T.tower N g).q := rfl
  have h2 := opbc (UpperTheory.Gal.G3.hodge ℂ a b) (Spec.map (CommRingCat.ofHom τ)) (T.tower N g).q
    ((T.tower N g).s j ≫ (T.tower N g).q) (T.tower N g).q ((T.tower N g).s j) ((T.tower N g).t j) hs
    ((T.tower N g).comm j) _ (hop _ hΘ)
  obtain ⟨hf', he', -⟩ := bcs (Spec.map (CommRingCat.ofHom τ)) (T.tower N g).q
    ((T.tower N g).s j ≫ (T.tower N g).q) ((T.tower N g).s j ≫ (T.tower N g).q) ((T.tower N g).s j) hs
    ((T.tower N g).s j) hs PEmpty (fun e => e.elim) (fun e => e.elim)
  haveI := hf'
  haveI := he'
  have ht' : UpperTheory.Gal.G3.bcMap (Spec.map (CommRingCat.ofHom τ)) ((T.tower N g).t j) ((T.tower N g).comm j) ≫
      pullback.snd (T.tower N g).q (Spec.map (CommRingCat.ofHom τ)) =
      UpperTheory.Gal.G3.bcMap (Spec.map (CommRingCat.ofHom τ)) ((T.tower N g).s j) hs ≫
      pullback.snd (T.tower N g).q (Spec.map (CommRingCat.ofHom τ)) := by
    unfold UpperTheory.Gal.G3.bcMap
    rw [pullback.lift_snd, pullback.lift_snd]
  have htr' := htr ℂ a b (pullback.snd (T.tower N g).q (Spec.map (CommRingCat.ofHom τ))) _
    (UpperTheory.Gal.G3.bcMap (Spec.map (CommRingCat.ofHom τ)) ((T.tower N g).s j) hs) rfl
  have hA := (optr (UpperTheory.Gal.G3.hodge ℂ a b) (hg ℂ a b) _ _ _ _ _ rfl ht' _ htr' _).1 h2
  have e1 : (UpperTheory.Gal.Int.Geo.bcAlong (T.tower N g) τ).s j =
      UpperTheory.Gal.G3.bcMap (Spec.map (CommRingCat.ofHom τ)) ((T.tower N g).s j) hs := rfl
  refine ⟨e1 ▸ hf', e1 ▸ he', Eq.trans ?_ (hxe j)⟩
  rw [hA]
  rfl
