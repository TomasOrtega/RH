import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.CoverLowOfCov

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV GlobalTheory.HodgeCoh UpperTheory.Gal.G3 UpperTheory.Gal.Int.Geo
universe u v

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
private theorem hodgeTrace_pull_congr {F : Type} [Field F] {Y Z : Scheme.{0}} (s t : Y ⟶ Z) [IsFinite s] [Etale s]
    (p : Z ⟶ sp F) {q q' : Y ⟶ sp F} (e : q = q') (h₁ : s ≫ p = q) (h₂ : t ≫ p = q) (h₁' : s ≫ p = q') (h₂' : t ≫ p = q')
    (a b : ℕ) (x : hodgeH p a b) :
    hodgeTrace h₁ a b (hodgePull h₂ a b x) = hodgeTrace h₁' a b (hodgePull h₂' a b x) := by
  subst e; rfl

/- English proof (translation)
Introduce `hBc hTr hTrBc k F _ _ φ H g _ _ a b`. Use `letI : Algebra k F := φ.toAlgebra`. Take `⟨hF, hE, -⟩` from `hBc (Spec.map (CommRingCat.ofHom φ)) H.q (H.s g ≫ H.q) (H.s g ≫ H.q) (H.s g) rfl (H.s g) rfl PEmpty (fun e => e.elim) (fun e => e.elim)`. Use `⟨hF, hE, hodgeTrace (bcMap_snd _ (H.s g) rfl) a b, ?_, ?_⟩` and prove the remaining obligations. Conclude with `hTrBc (hodge F a b) _ H.q (H.s g ≫ H.q) (H.s g) rfl _ (hTr F a b _ _ _ (bcMap_snd _ _ _))`.

Introduce `hF' hE' x`. Conclude with `@hodgeTrace_pull_congr _ _ _ _ _ _ hF' hE' _ _ _ (bcMap_snd (Spec.map (CommRingCat.ofHom φ)) (H.s g) rfl) _ _ _ _ a b x`.
-/
theorem UpperTheory.Gal.G3.jHodgeOpBc :
    BcSplits → HodgeTr → TrBc.{0} → HodgeOpBc := by
  intro hBc hTr hTrBc k F _ _ φ H g _ _ a b
  letI : Algebra k F := φ.toAlgebra
  obtain ⟨hF, hE, -⟩ := hBc (Spec.map (CommRingCat.ofHom φ)) H.q (H.s g ≫ H.q) (H.s g ≫ H.q) (H.s g) rfl
    (H.s g) rfl PEmpty (fun e => e.elim) (fun e => e.elim)
  refine ⟨hF, hE, hodgeTrace (bcMap_snd _ (H.s g) rfl) a b, ?_, ?_⟩
  · exact hTrBc (hodge F a b) _ H.q (H.s g ≫ H.q) (H.s g) rfl _ (hTr F a b _ _ _ (bcMap_snd _ _ _))
  · intro hF' hE' x
    exact @hodgeTrace_pull_congr _ _ _ _ _ _ hF' hE' _ _ _
      (bcMap_snd (Spec.map (CommRingCat.ofHom φ)) (H.s g) rfl) _ _ _ _ a b x
