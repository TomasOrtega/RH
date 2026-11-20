import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CsdSsOfFull
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

/- English proof (translation)
Introduce `F K Ω _ _ _ _ _ _ _ _ _ A v w h h' j i hP x y x' y' hx hy H`. Take `⟨c, hc, -⟩` from `GlobalTheory.T.place_over_transport_ring_iso F Ω A v h K Ω A w h' _ _ i hP`. Establish `key : ∀ (z : WD h) (z' : WD h'), WDRel (RingEquiv.refl Ω) z z' → (∀ s, z.charPol s = z'.charPol (c s)) ∧ z.lpDim = z'.lpDim`. Introduce and unpack `_ _ ⟨n, b, b', rfl, rfl, -, hρ⟩`. Use `⟨fun s => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[WD.charPol_mk, WD.charPol_mk, hρ s (c s) ((hc s (c s)).mpr rfl)]`. Rewrite using `[WD.lpDim_mk, WD.lpDim_mk]`. Establish `ab : ∀ (z : WD h) (z' : WD h'), WDRel (RingEquiv.refl Ω) z z' → UpperTheory.V.Lev.AbW z → UpperTheory.V.Lev.AbW z'`. Introduce `z z' hz a g g'`. Take `⟨h1, h2⟩` from `key z z' hz`.

Take `⟨g, rfl⟩` from `c.surjective g`. Take `⟨g', rfl⟩` from `c.surjective g'`. Rewrite using `[← h2, ← a g g', h1, map_mul, map_mul, map_mul, map_inv, map_inv]`. Introduce `hab s`. Rewrite using `[(key x x' hx).1, (key y y' hy).1]`.

Conclude with `H (hab.imp (ab x x' hx) (ab y y' hy)) (c s)`.
-/
theorem UpperTheory.V.Lev.ssMove :
    UpperTheory.V.Lev.SsMove := by
  intro F K Ω _ _ _ _ _ _ _ _ _ A v w h h' j i hP x y x' y' hx hy H
  obtain ⟨c, hc, -⟩ := GlobalTheory.T.place_over_transport_ring_iso F Ω A v h K Ω A w h' _ _ i hP
  have key : ∀ (z : WD h) (z' : WD h'), WDRel (RingEquiv.refl Ω) z z' →
      (∀ s, z.charPol s = z'.charPol (c s)) ∧ z.lpDim = z'.lpDim := by
    rintro _ _ ⟨n, b, b', rfl, rfl, -, hρ⟩
    refine ⟨fun s => ?_, ?_⟩
    · rw [WD.charPol_mk, WD.charPol_mk, hρ s (c s) ((hc s (c s)).mpr rfl)]
    · rw [WD.lpDim_mk, WD.lpDim_mk]
  have ab : ∀ (z : WD h) (z' : WD h'), WDRel (RingEquiv.refl Ω) z z' →
      UpperTheory.V.Lev.AbW z → UpperTheory.V.Lev.AbW z' := by
    intro z z' hz a g g'
    obtain ⟨h1, h2⟩ := key z z' hz
    obtain ⟨g, rfl⟩ := c.surjective g
    obtain ⟨g', rfl⟩ := c.surjective g'
    rw [← h2, ← a g g', h1, map_mul, map_mul, map_mul, map_inv, map_inv]
  intro hab s
  rw [(key x x' hx).1, (key y y' hy).1]
  exact H (hab.imp (ab x x' hx) (ab y y' hy)) (c s)
