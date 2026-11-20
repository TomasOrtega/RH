import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkMapInjective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS.Modif

/- English proof (translation)
Introduce `F _ Y _ p U d M hp hU y hR`. Establish `hprop : ∀ {Z : Scheme.{0}} {s : Z ⟶ Sp F}, IsProjOver s → IsProper s`. Introduce `Z s hs`. Take `⟨N, c, hc, rfl⟩` from `hs`. Use `isProper_str F N` as an intermediate fact.

Use `infer_instance`. Use `haveI : IsProper p := hprop hp`. Use `haveI : IsProper (M.σ ≫ p) := hprop M.proj`. Use `haveI : IsProper M.σ := IsProper.of_comp M.σ p`. Use `haveI : Nonempty M.X := by haveI := M.iso`.

Take `⟨u, hu⟩` from `hU`. Take `⟨z, -⟩` from `(M.σ ∣_ U).surjective ⟨u, hu⟩`. Conclude with `⟨z.1⟩`. Use `haveI : IsIntegral M.X := HSApp.ValCrit.isIntegral_X M`. Set `R` to `Y.presheaf.stalk y`.

Use `haveI : IsDomain R := inferInstanceAs (IsDomain (Y.presheaf.stalk y))`. Use `haveI : IsDiscreteValuationRing R := hR`. Set `η` to `genericPoint Y`. Establish `hηU : η ∈ U` using `((genericPoint_spec Y).mem_open_set_iff U.isOpen).2 (by simpa using hU)`. Set `i₂ : Spec R ⟶ Y` to `Y.fromSpecStalk y`.

Establish `hgen : ∀ w : Spec R, (∀ u, w ⤳ u) → i₂ w = η`. Introduce `w hw`. Establish `hq : η ∈ Set.range i₂`. Rewrite using `[Scheme.range_fromSpecStalk]`. Conclude with `(genericPoint_spec Y).specializes (Set.mem_univ y)`.

Take `⟨q, hq⟩` from `hq`. Establish `h1 : i₂ w ⤳ η` using `hq ▸ (hw q).map i₂.continuous`. Conclude with `(h1.antisymm ((genericPoint_spec Y).specializes (Set.mem_univ _))).eq`. Set `K` to `FractionRing R`. Set `j : Spec (.of K) ⟶ Spec R` to `Spec.map (CommRingCat.ofHom (algebraMap R K))`.

Establish `hj : ∀ s : Spec (.of K), ∀ u : Spec R, j s ⤳ u`. Introduce `s u`. Use `(PrimeSpectrum.le_iff_specializes _ _).1 ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Ideal.comap (algebraMap R K) s.asIdeal ≤ u.asIdeal`. Use `haveI : s.asIdeal.IsPrime := s.isPrime`.

Rewrite using `[Ideal.eq_bot_of_prime s.asIdeal, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)]`. Conclude with `bot_le`. Establish `hKU : ⊤ ≤ (j ≫ i₂) ⁻¹ᵁ U` using `fun s _ => by show i₂ (j s) ∈ U`. Rewrite using `[hgen (j s) (hj s)]`. Conclude with `hηU`.

Take `⟨i₁, hi₁, -⟩` from `M.existsUnique_lift (j ≫ i₂) hKU`. Establish `hE : ValuativeCriterion.Existence M.σ`. Establish `h : UniversallyClosed M.σ` using `inferInstance`. Rewrite `h` using `[UniversallyClosed.eq_valuativeCriterion]`. Conclude with `h.1`.

Take `⟨⟨L⟩⟩` from `hE (@ValuativeCommSq.mk _ _ M.σ R inferInstance ‹IsDomain R› inferInstance K inferInstance inferInstance inferInstance i₁ i₂ ⟨hi₁⟩)`. Set `c` to `IsLocalRing.closedPoint R`. Establish `hfr : L.l ≫ M.σ = i₂` using `L.fac_right`. Use `⟨L.l c, ?_, ?_⟩` and prove the remaining obligations. Use `show (L.l ≫ M.σ) c = y`.

Rewrite using `[hfr]`. Conclude with `Scheme.fromSpecStalk_closedPoint`. Establish `key : ∀ g : Spec R ⟶ Y, g = i₂ → Function.Bijective (g.stalkMap c).hom`. Introduce and unpack `_ rfl`. Establish `e : i₂.stalkMap c ≫ (stalkClosedPointIso R).hom = (Y.presheaf.stalkCongr _).hom` using `Scheme.stalkClosedPointTo_fromSpecStalk y`.

Use `haveI : IsIso (i₂.stalkMap c ≫ (stalkClosedPointIso R).hom) := by rw [e]; infer_instance`. Use `haveI : IsIso (i₂.stalkMap c) := IsIso.of_isIso_comp_right _ (stalkClosedPointIso R).hom`. Conclude with `ConcreteCategory.bijective_of_isIso _`. Establish `hb` using `key _ hfr`. Establish `e₀` using `Scheme.Hom.stalkMap_comp L.l M.σ c`.

Establish `hb2 : Function.Bijective (M.σ.stalkMap (L.l c) ≫ L.l.stalkMap c).hom` using `by rw [← e₀]; exact hb`. Use `replace hb : Function.Bijective ((L.l.stalkMap c).hom ∘ (M.σ.stalkMap (L.l c)).hom) := hb2`. Set `t` to `genericPoint (Spec R)`. Establish `ht : ∀ u : Spec R, t ⤳ u` using `fun u => (genericPoint_spec (Spec R)).specializes (Set.mem_univ u)`. Establish `hσt : M.σ (L.l t) = η` using `by show (L.l ≫ M.σ) t = η`.

Rewrite using `[hfr]`. Conclude with `hgen t ht`. Establish `hσg : M.σ (genericPoint M.X) = η`. Establish `h1 : M.σ (genericPoint M.X) ⤳ η` using `hσt ▸ ((genericPoint_spec M.X).specializes (Set.mem_univ (L.l t))).map M.σ.continuous`. Conclude with `(h1.antisymm ((genericPoint_spec Y).specializes (Set.mem_univ _))).eq`.

Establish `hlt : L.l t = genericPoint M.X` using `by haveI := M.iso`. Establish `m1 : L.l t ∈ M.opn` using `show M.σ (L.l t) ∈ U from hσt ▸ hηU`. Establish `m2 : genericPoint M.X ∈ M.opn` using `show M.σ (genericPoint M.X) ∈ U from hσg ▸ hηU`. Establish `e : (M.σ ∣_ U) ⟨L.l t, m1⟩ = (M.σ ∣_ U) ⟨genericPoint M.X, m2⟩` using `Subtype.ext ((morphismRestrict_base_coe M.σ U ⟨L.l t, m1⟩).trans ((hσt.trans hσg.symm).trans (morphismRestrict_base_coe M.σ U ⟨genericPoint M.X, m2⟩).symm))`. Conclude with `congrArg Subtype.val ((M.σ ∣_ U).isOpenEmbedding.injective e)`.

Establish `hBinj : Function.Injective (L.l.stalkMap c).hom`. Establish `hsp : t ⤳ c` using `ht c`. Establish `nat` using `Scheme.Hom.stalkSpecializes_stalkMap L.l t c hsp`. Establish `hf : IsField (M.X.presheaf.stalk (L.l t))`. Rewrite using `[hlt]`.

Conclude with `Field.toIsField M.X.functionField`. Establish `i1 : Function.Injective (L.l.stalkMap t).hom`. Use `letI := hf.toField`. Conclude with `RingHom.injective _`. Establish `i2 : Function.Injective (M.X.presheaf.stalkSpecializes (hsp.map L.l.continuous)).hom`.

Use `(injective_iff_map_eq_zero _).2 fun a ha => ?_` and prove the remaining obligations. Take `⟨V, hV, f, rfl⟩` from `M.X.presheaf.germ_exist a`. Establish `e` using `congrArg (fun φ => φ.hom f) (M.X.presheaf.germ_stalkSpecializes hV (hsp.map L.l.continuous))`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at e`. Rewrite `ha` using `[e]`.

Rewrite using `[germ_injective_of_isIntegral M.X _ _ (ha.trans (map_zero _).symm), map_zero]`. Establish `i3 : Function.Injective (((Spec R).presheaf.stalkSpecializes hsp).hom ∘ (L.l.stalkMap c).hom)`. Establish `h4 : Function.Injective (M.X.presheaf.stalkSpecializes (hsp.map L.l.continuous) ≫ L.l.stalkMap t).hom` using `i1.comp i2`. Rewrite `h4` using `[nat]`. Conclude with `h4`.

Conclude with `i3.of_comp`. Use `⟨hb.1.of_comp, fun a => ?_⟩` and prove the remaining obligations. Take `⟨b, hb'⟩` from `hb.2 ((L.l.stalkMap c).hom a)`. Conclude with `⟨b, hBinj hb'⟩`.
-/
theorem exists_bijective_stalkMap_of_dvr : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F)
    (U : Y.Opens) (d : ℕ) (M : Modif p U d), IsProjOver p → (U : Set Y).Nonempty → ∀ y : Y,
      IsDiscreteValuationRing (Y.presheaf.stalk y) →
      ∃ x : M.X, M.σ x = y ∧ Function.Bijective (M.σ.stalkMap x).hom := by
  intro F _ Y _ p U d M hp hU y hR
  have hprop : ∀ {Z : Scheme.{0}} {s : Z ⟶ Sp F}, IsProjOver s → IsProper s := by
    intro Z s hs
    obtain ⟨N, c, hc, rfl⟩ := hs
    have := isProper_str F N
    infer_instance
  haveI : IsProper p := hprop hp
  haveI : IsProper (M.σ ≫ p) := hprop M.proj
  haveI : IsProper M.σ := IsProper.of_comp M.σ p
  haveI : Nonempty M.X := by
    haveI := M.iso
    obtain ⟨u, hu⟩ := hU
    obtain ⟨z, -⟩ := (M.σ ∣_ U).surjective ⟨u, hu⟩
    exact ⟨z.1⟩
  haveI : IsIntegral M.X := HSApp.ValCrit.isIntegral_X M
  let R := Y.presheaf.stalk y
  haveI : IsDomain R := inferInstanceAs (IsDomain (Y.presheaf.stalk y))
  haveI : IsDiscreteValuationRing R := hR
  let η := genericPoint Y
  have hηU : η ∈ U := ((genericPoint_spec Y).mem_open_set_iff U.isOpen).2 (by simpa using hU)
  let i₂ : Spec R ⟶ Y := Y.fromSpecStalk y

  have hgen : ∀ w : Spec R, (∀ u, w ⤳ u) → i₂ w = η := by
    intro w hw
    have hq : η ∈ Set.range i₂ := by
      rw [Scheme.range_fromSpecStalk]; exact (genericPoint_spec Y).specializes (Set.mem_univ y)
    obtain ⟨q, hq⟩ := hq
    have h1 : i₂ w ⤳ η := hq ▸ (hw q).map i₂.continuous
    exact (h1.antisymm ((genericPoint_spec Y).specializes (Set.mem_univ _))).eq
  let K := FractionRing R
  let j : Spec (.of K) ⟶ Spec R := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have hj : ∀ s : Spec (.of K), ∀ u : Spec R, j s ⤳ u := by
    intro s u
    refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
    change Ideal.comap (algebraMap R K) s.asIdeal ≤ u.asIdeal
    haveI : s.asIdeal.IsPrime := s.isPrime
    rw [Ideal.eq_bot_of_prime s.asIdeal, ← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)]
    exact bot_le
  have hKU : ⊤ ≤ (j ≫ i₂) ⁻¹ᵁ U := fun s _ => by
    show i₂ (j s) ∈ U
    rw [hgen (j s) (hj s)]
    exact hηU
  obtain ⟨i₁, hi₁, -⟩ := M.existsUnique_lift (j ≫ i₂) hKU
  have hE : ValuativeCriterion.Existence M.σ := by
    have h : UniversallyClosed M.σ := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  obtain ⟨⟨L⟩⟩ := hE (@ValuativeCommSq.mk _ _ M.σ R inferInstance ‹IsDomain R› inferInstance K inferInstance
    inferInstance inferInstance i₁ i₂ ⟨hi₁⟩)
  let c := IsLocalRing.closedPoint R
  have hfr : L.l ≫ M.σ = i₂ := L.fac_right
  refine ⟨L.l c, ?_, ?_⟩
  · show (L.l ≫ M.σ) c = y
    rw [hfr]
    exact Scheme.fromSpecStalk_closedPoint

  have key : ∀ g : Spec R ⟶ Y, g = i₂ → Function.Bijective (g.stalkMap c).hom := by
    rintro _ rfl
    have e : i₂.stalkMap c ≫ (stalkClosedPointIso R).hom = (Y.presheaf.stalkCongr _).hom :=
      Scheme.stalkClosedPointTo_fromSpecStalk y
    haveI : IsIso (i₂.stalkMap c ≫ (stalkClosedPointIso R).hom) := by rw [e]; infer_instance
    haveI : IsIso (i₂.stalkMap c) := IsIso.of_isIso_comp_right _ (stalkClosedPointIso R).hom
    exact ConcreteCategory.bijective_of_isIso _
  have hb := key _ hfr
  have e₀ := Scheme.Hom.stalkMap_comp L.l M.σ c
  have hb2 : Function.Bijective (M.σ.stalkMap (L.l c) ≫ L.l.stalkMap c).hom := by rw [← e₀]; exact hb
  replace hb : Function.Bijective ((L.l.stalkMap c).hom ∘ (M.σ.stalkMap (L.l c)).hom) := hb2

  let t := genericPoint (Spec R)
  have ht : ∀ u : Spec R, t ⤳ u := fun u => (genericPoint_spec (Spec R)).specializes (Set.mem_univ u)
  have hσt : M.σ (L.l t) = η := by
    show (L.l ≫ M.σ) t = η
    rw [hfr]; exact hgen t ht
  have hσg : M.σ (genericPoint M.X) = η := by
    have h1 : M.σ (genericPoint M.X) ⤳ η :=
      hσt ▸ ((genericPoint_spec M.X).specializes (Set.mem_univ (L.l t))).map M.σ.continuous
    exact (h1.antisymm ((genericPoint_spec Y).specializes (Set.mem_univ _))).eq
  have hlt : L.l t = genericPoint M.X := by
    haveI := M.iso
    have m1 : L.l t ∈ M.opn := show M.σ (L.l t) ∈ U from hσt ▸ hηU
    have m2 : genericPoint M.X ∈ M.opn := show M.σ (genericPoint M.X) ∈ U from hσg ▸ hηU
    have e : (M.σ ∣_ U) ⟨L.l t, m1⟩ = (M.σ ∣_ U) ⟨genericPoint M.X, m2⟩ :=
      Subtype.ext ((morphismRestrict_base_coe M.σ U ⟨L.l t, m1⟩).trans
        ((hσt.trans hσg.symm).trans (morphismRestrict_base_coe M.σ U ⟨genericPoint M.X, m2⟩).symm))
    exact congrArg Subtype.val ((M.σ ∣_ U).isOpenEmbedding.injective e)

  have hBinj : Function.Injective (L.l.stalkMap c).hom := by
    have hsp : t ⤳ c := ht c
    have nat := Scheme.Hom.stalkSpecializes_stalkMap L.l t c hsp
    have hf : IsField (M.X.presheaf.stalk (L.l t)) := by
      rw [hlt]; exact Field.toIsField M.X.functionField
    have i1 : Function.Injective (L.l.stalkMap t).hom := by
      letI := hf.toField
      exact RingHom.injective _
    have i2 : Function.Injective (M.X.presheaf.stalkSpecializes (hsp.map L.l.continuous)).hom := by
      refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
      obtain ⟨V, hV, f, rfl⟩ := M.X.presheaf.germ_exist a
      have e := congrArg (fun φ => φ.hom f) (M.X.presheaf.germ_stalkSpecializes hV (hsp.map L.l.continuous))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
      rw [e] at ha
      rw [germ_injective_of_isIntegral M.X _ _ (ha.trans (map_zero _).symm), map_zero]
    have i3 : Function.Injective (((Spec R).presheaf.stalkSpecializes hsp).hom ∘ (L.l.stalkMap c).hom) := by
      have h4 : Function.Injective (M.X.presheaf.stalkSpecializes (hsp.map L.l.continuous) ≫ L.l.stalkMap t).hom :=
        i1.comp i2
      rw [nat] at h4
      exact h4
    exact i3.of_comp
  refine ⟨hb.1.of_comp, fun a => ?_⟩
  obtain ⟨b, hb'⟩ := hb.2 ((L.l.stalkMap c).hom a)
  exact ⟨b, hBinj hb'⟩

end GlobalTheory.CompHS.Modif
