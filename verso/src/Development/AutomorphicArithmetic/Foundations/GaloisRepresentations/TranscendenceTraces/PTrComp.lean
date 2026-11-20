import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `hChar hFam hWc hRp hOp q _ n i W Z S r p _ _ w' w hr hp hq x`. Establish `hrp : IsWt (r ≫ p) (Wt.mul r w' w)` using `hWc r p w' w hr hp`. Establish `hqZ : IsUnit ((q : ℕ) : Γ(Z, ⊤))`. Use `hq.map p.appTop.hom` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis.

Take `⟨_, hsr, _⟩` from `hChar q i r w' hr hqZ`. Take `⟨_, hsp, _⟩` from `hChar q i p w hp hq`. Take `⟨σ, hσ, hσeq⟩` from `hFam q i r p w' w (trFam r w' q i) (trFam p w q i) hsr hsp`. Rewrite using `[(hChar q i (r ≫ p) _ hrp hq).2.2 σ hσ n, (hChar q i p w hp hq).2.2 _ hsp n, (hChar q i r w' hr hqZ).2.2 _ hsr n]`. Take `⟨a, ha⟩` from `(hRp (ZMod q) _ W n).1 x`.

Establish `h1` using `hOp _ _ (trFam r w' q i) n x a ha`. Establish `h2` using `hOp _ _ (trFam p w q i) n _ _ h1`. Establish `h3` using `hOp _ _ σ n x a ha`. Rewrite `h3` using `[hσeq n a]`. Conclude with `((hRp (ZMod q) _ S n).2.2.1 _ _ _ _ h3 h2).2.1 rfl`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.trComp_of :
    TrChar → FamComp → WtComp → RpBasic → RpOp → TrComp := by
  intro hChar hFam hWc hRp hOp q _ n i W Z S r p _ _ w' w hr hp hq x
  have hrp : IsWt (r ≫ p) (Wt.mul r w' w) := hWc r p w' w hr hp
  have hqZ : IsUnit ((q : ℕ) : Γ(Z, ⊤)) := by
    have := hq.map p.appTop.hom
    rwa [map_natCast] at this
  obtain ⟨_, hsr, _⟩ := hChar q i r w' hr hqZ
  obtain ⟨_, hsp, _⟩ := hChar q i p w hp hq
  obtain ⟨σ, hσ, hσeq⟩ := hFam q i r p w' w (trFam r w' q i) (trFam p w q i) hsr hsp
  rw [(hChar q i (r ≫ p) _ hrp hq).2.2 σ hσ n, (hChar q i p w hp hq).2.2 _ hsp n,
    (hChar q i r w' hr hqZ).2.2 _ hsr n]
  obtain ⟨a, ha⟩ := (hRp (ZMod q) _ W n).1 x
  have h1 := hOp _ _ (trFam r w' q i) n x a ha
  have h2 := hOp _ _ (trFam p w q i) n _ _ h1
  have h3 := hOp _ _ σ n x a ha
  rw [hσeq n a] at h3
  exact ((hRp (ZMod q) _ S n).2.2.1 _ _ _ _ h3 h2).2.1 rfl
