import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `hChar hFam hWbc hRp hOp q _ n i Z' S' Z S v p' p g _ w hpb hw hq x`. Use `haveI : IsFinite p' := MorphismProperty.of_isPullback (P := @IsFinite) hpb inferInstance`. Establish `hw' : IsWt p' (Wt.comap v w)` using `hWbc v p' p g w hpb hw`. Establish `hq' : IsUnit ((q : ℕ) : Γ(S', ⊤))`. Use `hq.map g.appTop.hom` as an intermediate fact.

Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Take `⟨_, hs, _⟩` from `hChar q i p w hw hq`. Take `⟨τ', hτ', hτeq⟩` from `hFam q i v p' p g w hpb (trFam p w q i) hs`. Rewrite using `[(hChar q i p w hw hq).2.2 _ hs n, (hChar q i p' _ hw' hq').2.2 τ' hτ' n]`. Take `⟨a, ha⟩` from `(hRp (ZMod q) _ Z n).1 x`.

Establish `h1` using `hOp _ _ (trFam p w q i) n x a ha`. Establish `h2` using `(hRp (ZMod q) _ S n).2.2.2.1 S' g _ _ h1`. Establish `h3` using `(hRp (ZMod q) _ Z n).2.2.2.1 Z' v x a ha`. Establish `h4` using `hOp _ _ τ' n _ _ h3`. Establish `h5 : Rp ((τ'.op n) ((cpull ((chains (ZMod q)).map (sch.map v)) (res (ZMod q) (tw q i)) n) x)) (Sec.res g ((((trFam p w q i).deg n).app (Sq.self p)) a))`.

Establish `e` using `hτeq n a`. Conclude with `e ▸ h4`. Conclude with `((hRp (ZMod q) _ S' n).2.2.1 _ _ _ _ h2 h5).2.1 rfl`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.trBC_of :
    TrChar → FamBC → WtBC → RpBasic → RpOp → TrBC := by
  intro hChar hFam hWbc hRp hOp q _ n i Z' S' Z S v p' p g _ w hpb hw hq x
  haveI : IsFinite p' := MorphismProperty.of_isPullback (P := @IsFinite) hpb inferInstance
  have hw' : IsWt p' (Wt.comap v w) := hWbc v p' p g w hpb hw
  have hq' : IsUnit ((q : ℕ) : Γ(S', ⊤)) := by
    have := hq.map g.appTop.hom
    rwa [map_natCast] at this
  obtain ⟨_, hs, _⟩ := hChar q i p w hw hq
  obtain ⟨τ', hτ', hτeq⟩ := hFam q i v p' p g w hpb (trFam p w q i) hs
  rw [(hChar q i p w hw hq).2.2 _ hs n, (hChar q i p' _ hw' hq').2.2 τ' hτ' n]
  obtain ⟨a, ha⟩ := (hRp (ZMod q) _ Z n).1 x
  have h1 := hOp _ _ (trFam p w q i) n x a ha
  have h2 := (hRp (ZMod q) _ S n).2.2.2.1 S' g _ _ h1
  have h3 := (hRp (ZMod q) _ Z n).2.2.2.1 Z' v x a ha
  have h4 := hOp _ _ τ' n _ _ h3
  have h5 : Rp ((τ'.op n) ((cpull ((chains (ZMod q)).map (sch.map v)) (res (ZMod q) (tw q i)) n) x))
      (Sec.res g ((((trFam p w q i).deg n).app (Sq.self p)) a)) := by
    have e := hτeq n a
    exact e ▸ h4
  exact ((hRp (ZMod q) _ S' n).2.2.1 _ _ _ _ h2 h5).2.1 rfl
