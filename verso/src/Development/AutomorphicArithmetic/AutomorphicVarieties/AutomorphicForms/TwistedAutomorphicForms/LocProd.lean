import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.EqOneOfMemLev

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap finiteCompletionMap infiniteAdeleMap)

private noncomputable def UpperTheory.V.Af.Tw.compAt (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    AdeleRing (𝓞 K) K →* v.adicCompletion K where
  toFun a := a.2 v
  map_one' := rfl
  map_mul' _ _ := rfl

private noncomputable def UpperTheory.V.Af.Tw.infPart (K : Type) [Field K] [NumberField K] :
    AdeleRing (𝓞 K) K →* InfiniteAdeleRing K where
  toFun a := a.1
  map_one' := rfl
  map_mul' _ _ := rfl

/- English proof (translation)
Simplify using `only [localIdele, finiteSingle, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk]`. Conclude with `RestrictedProduct.mulSingle_eq_same _ _ _`.
-/
private theorem UpperTheory.V.Af.Tw.loc_same {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) : (localIdele K v x).val.2 v = x := by
  classical
  simp only [localIdele, finiteSingle, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk]
  exact RestrictedProduct.mulSingle_eq_same _ _ _

/- English proof (translation)
Simplify using `only [localIdele, finiteSingle, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk]`. Conclude with `RestrictedProduct.mulSingle_eq_of_ne _ _ h`.
-/
private theorem UpperTheory.V.Af.Tw.loc_ne {K : Type} [Field K] [NumberField K] {v w : HeightOneSpectrum (𝓞 K)}
    (h : w ≠ v) (x : (v.adicCompletion K)ˣ) : (localIdele K v x).val.2 w = 1 := by
  classical
  simp only [localIdele, finiteSingle, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk]
  exact RestrictedProduct.mulSingle_eq_of_ne _ _ h

/- English proof (translation)
Unfold `UpperTheory.V.Af.Tw.LocProd`. Introduce `F L _ _ _ _ _ v x`. Set `y : ∀ w : HeightOneSpectrum (𝓞 L), (w.adicCompletion L)ˣ` to `fun w => Units.map (finiteCompletionMap F L w).toMonoidHom (Units.map (UpperTheory.V.Af.Tw.compAt F (HeightOneSpectrum.under (𝓞 F) w)) (localIdele F v x))`. Establish `hy : ∀ w, ((y w : (w.adicCompletion L)ˣ) : w.adicCompletion L) = finiteCompletionMap F L w ((localIdele F v x).val.2 (HeightOneSpectrum.under (𝓞 F) w))` using `fun w => rfl`. Establish `hmem : ∀ w : HeightOneSpectrum (𝓞 L), w ∈ aboveF F v ↔ HeightOneSpectrum.under (𝓞 F) w = v` using `fun w => by`.

Unfold `aboveF`. Simplify using the standard rewrite rules. Establish `key : ∀ a b : AdeleRing (𝓞 L) L, UpperTheory.V.Af.Tw.infPart L a = UpperTheory.V.Af.Tw.infPart L b → (∀ w, UpperTheory.V.Af.Tw.compAt L w a = UpperTheory.V.Af.Tw.compAt L w b) → a = b` using `fun a b h1 h2 => Prod.ext h1 (RestrictedProduct.ext _ _ h2)`. Use `⟨y, ?_, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[Units.coe_prod]`. Apply `key` to reduce the goal to its premises. Rewrite using `[map_prod]`. Establish `h1 : ∀ w, UpperTheory.V.Af.Tw.infPart L ((localIdele L w (y w)).val) = 1` using `fun w => rfl`. Simplify using `only [h1, Finset.prod_const_one]`.

Use `show infiniteAdeleMap F L 1 = 1`. Conclude with `map_one _`. Introduce `w'`. Rewrite using `[map_prod]`. Use `show finiteCompletionMap F L w' ((localIdele F v x).val.2 (HeightOneSpectrum.under (𝓞 F) w')) = ∏ w ∈ aboveF F v, (localIdele L w (y w)).val.2 w'`.

Distinguish the cases in `hw' : HeightOneSpectrum.under (𝓞 F) w' = v`. Rewrite using `[Finset.prod_eq_single w']`. Rewrite using `[UpperTheory.V.Af.Tw.loc_same, hy]`. Introduce `b _ hb`. Conclude with `UpperTheory.V.Af.Tw.loc_ne (Ne.symm hb) _`.

Introduce `h`. Conclude with `absurd ((hmem w').mpr hw') h`. Rewrite using `[UpperTheory.V.Af.Tw.loc_ne hw', map_one, Finset.prod_eq_one]`. Introduce `b hb`. Conclude with `UpperTheory.V.Af.Tw.loc_ne (fun h => hw' (by rw [h]; exact (hmem b).mp hb)) _`.

Introduce `hunr hx w hw`. Substitute `hw` using the available equality. Unfold `IsUnifAt at hx ⊢`. Rewrite using `[hy, UpperTheory.V.Af.Tw.loc_same, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, hunr w rfl, pow_one]`. Conclude with `hx`.
-/
theorem UpperTheory.V.Af.Tw.locProd :
    UpperTheory.V.Af.Tw.LocProd := by
  unfold UpperTheory.V.Af.Tw.LocProd
  intro F L _ _ _ _ _ v x
  classical
  let y : ∀ w : HeightOneSpectrum (𝓞 L), (w.adicCompletion L)ˣ := fun w =>
    Units.map (finiteCompletionMap F L w).toMonoidHom
      (Units.map (UpperTheory.V.Af.Tw.compAt F (HeightOneSpectrum.under (𝓞 F) w)) (localIdele F v x))
  have hy : ∀ w, ((y w : (w.adicCompletion L)ˣ) : w.adicCompletion L) =
      finiteCompletionMap F L w ((localIdele F v x).val.2 (HeightOneSpectrum.under (𝓞 F) w)) :=
    fun w => rfl
  have hmem : ∀ w : HeightOneSpectrum (𝓞 L),
      w ∈ aboveF F v ↔ HeightOneSpectrum.under (𝓞 F) w = v :=
    fun w => by
      unfold aboveF
      simp
  have key : ∀ a b : AdeleRing (𝓞 L) L, UpperTheory.V.Af.Tw.infPart L a = UpperTheory.V.Af.Tw.infPart L b →
      (∀ w, UpperTheory.V.Af.Tw.compAt L w a = UpperTheory.V.Af.Tw.compAt L w b) → a = b :=
    fun a b h1 h2 => Prod.ext h1 (RestrictedProduct.ext _ _ h2)
  refine ⟨y, ?_, ?_⟩
  · apply Units.ext
    rw [Units.coe_prod]
    apply key
    · rw [map_prod]
      have h1 : ∀ w, UpperTheory.V.Af.Tw.infPart L ((localIdele L w (y w)).val) = 1 := fun w => rfl
      simp only [h1, Finset.prod_const_one]
      show infiniteAdeleMap F L 1 = 1
      exact map_one _
    · intro w'
      rw [map_prod]
      show finiteCompletionMap F L w' ((localIdele F v x).val.2 (HeightOneSpectrum.under (𝓞 F) w')) =
        ∏ w ∈ aboveF F v, (localIdele L w (y w)).val.2 w'
      by_cases hw' : HeightOneSpectrum.under (𝓞 F) w' = v
      · rw [Finset.prod_eq_single w']
        · rw [UpperTheory.V.Af.Tw.loc_same, hy]
        · intro b _ hb
          exact UpperTheory.V.Af.Tw.loc_ne (Ne.symm hb) _
        · intro h
          exact absurd ((hmem w').mpr hw') h
      · rw [UpperTheory.V.Af.Tw.loc_ne hw', map_one, Finset.prod_eq_one]
        intro b hb
        exact UpperTheory.V.Af.Tw.loc_ne (fun h => hw' (by rw [h]; exact (hmem b).mp hb)) _
  · intro hunr hx w hw
    subst hw
    unfold IsUnifAt at hx ⊢
    rw [hy, UpperTheory.V.Af.Tw.loc_same, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, hunr w rfl, pow_one]
    exact hx
