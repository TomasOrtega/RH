import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRankAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedOfLocalIdealPointPropertyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionOfBasicOpenCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzLieConditionLocallyCutOutByIdealStatement

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

/- English proof (translation)
Use `Spec.map_injective h` as an intermediate fact. Conclude with `congrArg CommRingCat.Hom.hom this`.
-/
theorem lieOc_spMap_inj {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] {f g : R₁ →+* R₂} (h : spMap f = spMap g) : f = g := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

/- English proof (translation)
Assemble the required witnesses or components as `⟨(Spec.preimage y).hom, by simp [spMap]⟩`.
-/
theorem lieOc_exists_spMap {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (y : Sp R₂ ⟶ Sp R₁) : ∃ f : R₁ →+* R₂, y = spMap f :=
  ⟨(Spec.preimage y).hom, by simp [spMap]⟩

/- English proof (translation)
Simplify using `[spMap, ← Spec.map_comp]`.
-/
theorem lieOc_spMap_comp {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] (f : R₁ →+* R₂) (g : R₂ →+* R₃) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp [spMap, ← Spec.map_comp]

/- English proof (translation)
Set `P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop` to `fun R' _ x => ∀ β : R →+* R', x ≫ s = spMap β → LieHer b act β x`. Establish `hP : ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ S), x ≫ s = spMap β → (P R' x ↔ LieHer b act β x)`. Introduce `R' _ β x hx`. Use `⟨fun h => h β hx, fun h β' hx' => ?_⟩` and prove the remaining obligations. Establish `: β' = β` using `lieOc_spMap_inj (hx'.symm.trans hx)`.

Substitute `this` using the available equality. Conclude with `h`. Establish `her : ∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'') (x : Sp R' ⟶ S), P R' x → P R'' (spMap g ≫ x)`. Introduce `R' _ R'' _ g x hx β'' hβ''`. Take `⟨β, hβ⟩` from `lieOc_exists_spMap (x ≫ s)`.

Establish `e : β'' = g.comp β` using `lieOc_spMap_inj (by rw [← hβ'', Category.assoc, hβ, lieOc_spMap_comp])`. Substitute `e` using the available equality. Introduce `R''' _ g'`. Establish `h` using `hx β hβ R''' (g'.comp g)`. Rewrite `h` using `[← lieOc_spMap_comp]`.

Simplify `h` using `[Category.assoc, RingHom.comp_assoc]`. Establish `loc : ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S) (t : Finset R'), Ideal.span (t : Set R') = ⊤ → (∀ r ∈ t, P (Localization.Away r) (spMap (algebraMap R' (Localization.Away r)) ≫ x)) → P R' x` using `by classical`. Introduce `R' _ x t ht hloc β hβ R'' _ g`. Establish `hloc' : ∀ r ∈ t, LieHer b act ((algebraMap R' (Localization.Away r)).comp β) (spMap (algebraMap R' (Localization.Away r)) ≫ x)` using `fun r hr => hloc r hr _ (by rw [Category.assoc, hβ, lieOc_spMap_comp])`. Establish `key : ∀ r : R', (Localization.awayMap g r).comp (algebraMap R' (Localization.Away r)) = (algebraMap R'' (Localization.Away (g r))).comp g` using `fun r => IsLocalization.map_comp _`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `GlobalTheory.T.harrisTaylor_lie_condition_of_basicOpen_cover p D R b S A act R'' (g.comp β) (spMap g ≫ x) (t.image g) ?_ ?_` and prove the remaining obligations. Rewrite using `[Finset.coe_image, ← Ideal.map_span, ht, Ideal.map_top]`. Introduce `r'' hr''`. Take `⟨r, hr, rfl⟩` from `Finset.mem_image.1 hr''`.

Establish `h` using `(hloc' r hr (Localization.Away (g r)) (Localization.awayMap g r)).1`. Rewrite `h` using `[← Category.assoc, lieOc_spMap_comp, ← RingHom.comp_assoc, key]`. Rewrite using `[← Category.assoc, lieOc_spMap_comp, ← RingHom.comp_assoc]`. Conclude with `h`. Introduce `k _ _ g' i`.

Establish `hex : ∃ r ∈ t, g' (g r) ≠ 0`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `: Ideal.span (t : Set R') ≤ RingHom.ker (g'.comp g)` using `Ideal.span_le.2 fun r hr => by simpa using hcon r hr`. Rewrite `this` using `[ht]`.

Establish `h1 : (1 : R') ∈ RingHom.ker (g'.comp g)` using `this Submodule.mem_top`. Simplify using `at h1`. Take `⟨r, hr, hne⟩` from `hex`. Set `hr' : Localization.Away r →+* k` to `IsLocalization.Away.lift r (g := g'.comp g) (isUnit_iff_ne_zero.2 hne)`. Establish `hlift : hr'.comp (algebraMap R' (Localization.Away r)) = g'.comp g` using `IsLocalization.Away.lift_comp r _`.

Establish `h` using `(hloc' r hr (Localization.Away r) (RingHom.id _)).2 k hr' i`. Establish `e1 : spMap hr' ≫ spMap (RingHom.id (Localization.Away r)) ≫ spMap (algebraMap R' (Localization.Away r)) ≫ x = spMap g' ≫ spMap g ≫ x`. Simplify using `only [← Category.assoc, lieOc_spMap_comp]`. Rewrite using `[RingHom.id_comp, hlift]`. Establish `e2 : hr'.comp ((RingHom.id _).comp ((algebraMap R' (Localization.Away r)).comp β)) = g'.comp (g.comp β)`.

Rewrite using `[RingHom.id_comp, ← RingHom.comp_assoc, hlift, RingHom.comp_assoc]`. Rewrite `h` using `[e1, e2]`. Conclude with `h`. Take `⟨Z, i, hi, hZ⟩` from `GlobalTheory.T.isClosed_of_local_ideal_point_property S P her loc (fun z => by`. Take `⟨U, hU, hz, K, hK⟩` from `GlobalTheory.T.kottwitzLieCondition_locally_cut_out_by_ideal p D R b S s A hA act z`.

Use `⟨U, hU, hz, K, fun R' _ f => ?_⟩` and prove the remaining obligations. Take `⟨β, hβ⟩` from `lieOc_exists_spMap (spMap f ≫ hU.fromSpec ≫ s)`. Rewrite using `[hP R' β _ (by rw [Category.assoc]; exact hβ)]`. Conclude with `hK R' f β hβ)`. Conclude with `⟨Z, i, hi, fun R' _ β x hx => (hZ R' x).trans (hP R' β x hx)⟩`.
-/
theorem lieHer_closed (b : Base D R) (s : S ⟶ Sp R) (A : Over S) [GrpObj A] [IsCommMonObj A]
    (hA : Smooth A.hom) (act : OActN D.O A) :
    ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧
      ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ S), x ≫ s = spMap β →
        ((∃ y : Sp R' ⟶ Z, y ≫ i = x) ↔ LieHer b act β x) := by
  let P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop := fun R' _ x =>
    ∀ β : R →+* R', x ≫ s = spMap β → LieHer b act β x
  have hP : ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ S), x ≫ s = spMap β →
      (P R' x ↔ LieHer b act β x) := by
    intro R' _ β x hx
    refine ⟨fun h => h β hx, fun h β' hx' => ?_⟩
    have : β' = β := lieOc_spMap_inj (hx'.symm.trans hx)
    subst this; exact h

  have her : ∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'') (x : Sp R' ⟶ S),
      P R' x → P R'' (spMap g ≫ x) := by
    intro R' _ R'' _ g x hx β'' hβ''
    obtain ⟨β, hβ⟩ := lieOc_exists_spMap (x ≫ s)
    have e : β'' = g.comp β := lieOc_spMap_inj (by rw [← hβ'', Category.assoc, hβ, lieOc_spMap_comp])
    subst e
    intro R''' _ g'
    have h := hx β hβ R''' (g'.comp g)
    rw [← lieOc_spMap_comp] at h
    simpa [Category.assoc, RingHom.comp_assoc] using h

  have loc : ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S) (t : Finset R'), Ideal.span (t : Set R') = ⊤ →
      (∀ r ∈ t, P (Localization.Away r) (spMap (algebraMap R' (Localization.Away r)) ≫ x)) → P R' x := by
    classical
    intro R' _ x t ht hloc β hβ R'' _ g
    have hloc' : ∀ r ∈ t, LieHer b act ((algebraMap R' (Localization.Away r)).comp β)
        (spMap (algebraMap R' (Localization.Away r)) ≫ x) := fun r hr =>
      hloc r hr _ (by rw [Category.assoc, hβ, lieOc_spMap_comp])
    have key : ∀ r : R', (Localization.awayMap g r).comp (algebraMap R' (Localization.Away r)) =
        (algebraMap R'' (Localization.Away (g r))).comp g := fun r => IsLocalization.map_comp _
    refine ⟨?_, ?_⟩
    · refine GlobalTheory.T.harrisTaylor_lie_condition_of_basicOpen_cover p D R b S A act R'' (g.comp β) (spMap g ≫ x) (t.image g) ?_ ?_
      · rw [Finset.coe_image, ← Ideal.map_span, ht, Ideal.map_top]
      · intro r'' hr''
        obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hr''
        have h := (hloc' r hr (Localization.Away (g r)) (Localization.awayMap g r)).1
        rw [← Category.assoc, lieOc_spMap_comp, ← RingHom.comp_assoc, key] at h
        rw [← Category.assoc, lieOc_spMap_comp, ← RingHom.comp_assoc]
        exact h
    · intro k _ _ g' i
      have hex : ∃ r ∈ t, g' (g r) ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        have : Ideal.span (t : Set R') ≤ RingHom.ker (g'.comp g) :=
          Ideal.span_le.2 fun r hr => by simpa using hcon r hr
        rw [ht] at this
        have h1 : (1 : R') ∈ RingHom.ker (g'.comp g) := this Submodule.mem_top
        simp at h1
      obtain ⟨r, hr, hne⟩ := hex
      let hr' : Localization.Away r →+* k := IsLocalization.Away.lift r (g := g'.comp g) (isUnit_iff_ne_zero.2 hne)
      have hlift : hr'.comp (algebraMap R' (Localization.Away r)) = g'.comp g :=
        IsLocalization.Away.lift_comp r _
      have h := (hloc' r hr (Localization.Away r) (RingHom.id _)).2 k hr' i
      have e1 : spMap hr' ≫ spMap (RingHom.id (Localization.Away r)) ≫ spMap (algebraMap R' (Localization.Away r)) ≫ x =
          spMap g' ≫ spMap g ≫ x := by
        simp only [← Category.assoc, lieOc_spMap_comp]
        rw [RingHom.id_comp, hlift]
      have e2 : hr'.comp ((RingHom.id _).comp ((algebraMap R' (Localization.Away r)).comp β)) = g'.comp (g.comp β) := by
        rw [RingHom.id_comp, ← RingHom.comp_assoc, hlift, RingHom.comp_assoc]
      rw [e1, e2] at h
      exact h
  obtain ⟨Z, i, hi, hZ⟩ := GlobalTheory.T.isClosed_of_local_ideal_point_property S P her loc (fun z => by
    obtain ⟨U, hU, hz, K, hK⟩ := GlobalTheory.T.kottwitzLieCondition_locally_cut_out_by_ideal p D R b S s A hA act z
    refine ⟨U, hU, hz, K, fun R' _ f => ?_⟩
    obtain ⟨β, hβ⟩ := lieOc_exists_spMap (spMap f ≫ hU.fromSpec ≫ s)
    rw [hP R' β _ (by rw [Category.assoc]; exact hβ)]
    exact hK R' f β hβ)
  exact ⟨Z, i, hi, fun R' _ β x hx => (hZ R' x).trans (hP R' β x hx)⟩

end GlobalTheory.UPel.HT
