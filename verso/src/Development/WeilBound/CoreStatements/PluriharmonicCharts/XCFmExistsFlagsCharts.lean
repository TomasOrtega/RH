import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenUIsGenFam
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

/- English proof (translation)
Establish `hξ` using `Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ`. Establish `hi : IsLocalHom i` using `⟨fun a ha => isUnit_iff_ne_zero.mpr (fun h0 => by simp [h0] at ha)⟩`. Establish `hloc : IsLocalHom (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i).hom`. Rewrite using `[CommRingCat.hom_comp]`. Use `infer_instance`.

Establish `key` using `(SpecToEquivOfLocalRing X (CommRingCat.of G)).right_inv ⟨_, Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i, hloc⟩`. Rewrite `key` using `[SpecToEquivOfLocalRing_eq_iff]`. Take `⟨h1, h2⟩` from `key`. Express the relevant statement in the definitionally equal form `(Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫ X.fromSpecStalk (ξ (IsLocalRing.closedPoint Ω))) (IsLocalRing.closedPoint G) = ξ (IsLocalRing.closedPoint Ω) at h1`. Express the relevant statement in the definitionally equal form `Scheme.stalkClosedPointTo (Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫ X.fromSpecStalk (ξ (IsLocalRing.closedPoint Ω))) = (X.presheaf.stalkCongr (Inseparable.of_eq h1)).hom ≫ Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i at h2`.

Establish `hg : Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫ X.fromSpecStalk (ξ (IsLocalRing.closedPoint Ω)) = Spec.map (CommRingCat.ofHom i) ≫ ξ`. Rewrite using `[Spec.map_comp, Category.assoc, hξ]`. Use `revert h1 h2`. Generalize the expression as in `Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫ X.fromSpecStalk (ξ (IsLocalRing.closedPoint Ω)) = k at hg`. Substitute `hg` using the available equality.

Introduce `h1 h2`. Conclude with `⟨h1, h2⟩`.
-/
private theorem stalkClosedPointTo_specMap_comp_eq {X : Scheme.{0}} {Ω G : Type} [Field Ω] [Field G]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (i : Ω →+* G) :
    ∃ e : (Spec.map (CommRingCat.ofHom i) ≫ ξ) (IsLocalRing.closedPoint G) = ξ (IsLocalRing.closedPoint Ω),
      Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom i) ≫ ξ) =
        (X.presheaf.stalkCongr (Inseparable.of_eq e)).hom ≫ Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i := by
  have hξ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have hi : IsLocalHom i := ⟨fun a ha => isUnit_iff_ne_zero.mpr (fun h0 => by simp [h0] at ha)⟩
  have hloc : IsLocalHom (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i).hom := by
    rw [CommRingCat.hom_comp]
    infer_instance
  have key := (SpecToEquivOfLocalRing X (CommRingCat.of G)).right_inv
    ⟨_, Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i, hloc⟩
  rw [SpecToEquivOfLocalRing_eq_iff] at key
  obtain ⟨h1, h2⟩ := key
  change (Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫
    X.fromSpecStalk (ξ (IsLocalRing.closedPoint Ω))) (IsLocalRing.closedPoint G) = ξ (IsLocalRing.closedPoint Ω) at h1
  change Scheme.stalkClosedPointTo (Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫
    X.fromSpecStalk (ξ (IsLocalRing.closedPoint Ω))) = (X.presheaf.stalkCongr (Inseparable.of_eq h1)).hom ≫
      Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i at h2
  have hg : Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫
      X.fromSpecStalk (ξ (IsLocalRing.closedPoint Ω)) = Spec.map (CommRingCat.ofHom i) ≫ ξ := by
    rw [Spec.map_comp, Category.assoc, hξ]
  revert h1 h2
  generalize Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫
    X.fromSpecStalk (ξ (IsLocalRing.closedPoint Ω)) = k at hg
  subst hg
  intro h1 h2
  exact ⟨h1, h2⟩

/- English proof (translation)
Substitute `hg` using the available equality. Take `⟨e, he⟩` from `stalkClosedPointTo_specMap_comp_eq ξ i`. Rewrite using `[he]`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, TopCat.Presheaf.stalkCongr_hom, CommRingCat.hom_ofHom]`. Use `congr 2`.

Establish `hh` using `TopCat.Presheaf.stalkSpecializes_comp X.presheaf (Inseparable.of_eq e.symm).specializes hy`. Conclude with `congrArg (fun k => CommRingCat.Hom.hom k s) hh`.
-/
private theorem stalkClosedPointTo_stalkSpecializes_comp {X : Scheme.{0}} {Ω G : Type} [Field Ω] [Field G]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (i : Ω →+* G) (g : Spec (CommRingCat.of G) ⟶ X)
    (hg : g = Spec.map (CommRingCat.ofHom i) ≫ ξ) (y : X) (hy : g (IsLocalRing.closedPoint G) ⤳ y)
    (h : ξ (IsLocalRing.closedPoint Ω) ⤳ y) (s : X.presheaf.stalk y) :
    (Scheme.stalkClosedPointTo g).hom ((X.presheaf.stalkSpecializes hy).hom s) =
      i ((Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.stalkSpecializes h).hom s)) := by
  subst hg
  obtain ⟨e, he⟩ := stalkClosedPointTo_specMap_comp_eq ξ i
  rw [he]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, TopCat.Presheaf.stalkCongr_hom, CommRingCat.hom_ofHom]
  congr 2
  have hh := TopCat.Presheaf.stalkSpecializes_comp X.presheaf (Inseparable.of_eq e.symm).specializes hy
  exact congrArg (fun k => CommRingCat.Hom.hom k s) hh

/- English proof (translation)
Introduce `X X' Ω G _ _ ξ ξ' f i κ x hT hG' hD p' c₁ h`. Use `set q : Cpt ξ := ⟨f p'.1, h⟩ with hq`. Establish `K : ∀ s : X.presheaf.stalk (f p'.1), genMap ξ' p' ((f.stalkMap p'.1).hom s) = i (genMap ξ q s)`. Introduce `s`. Establish `e1` using `stalkClosedPointTo_stalkSpecializes_comp ξ i (ξ' ≫ f) hD (f p'.1) (f.base.hom.map_specializes p'.2) h s`.

Rewrite `e1` using `[Scheme.stalkClosedPointTo_comp]`. Conclude with `(congrArg (Scheme.stalkClosedPointTo ξ').hom (Scheme.Hom.stalkSpecializes_stalkMap_apply f _ _ p'.2 s).symm).trans e1`. Establish `F1 : ∀ a, a ∈ regAt ξ q → i a ∈ regAt ξ' p'`. Introduce `a ha`. Take `⟨s, rfl⟩` from `RingHom.mem_range.mp ha`.

Conclude with `RingHom.mem_range.mpr ⟨_, K s⟩`. Establish `F2 : ∀ a, a ∈ regAt ξ q → (i a)⁻¹ ∈ regAt ξ' p' → a⁻¹ ∈ regAt ξ q`. Introduce `a ha hinv`. Take `⟨s, rfl⟩` from `RingHom.mem_range.mp ha`. Take `⟨t, ht⟩` from `RingHom.mem_range.mp hinv`.

Distinguish the cases in `h0 : genMap ξ q s = 0`. Rewrite using `[h0, _root_.inv_zero]`. Conclude with `zero_mem _`. Establish `hu : IsUnit ((f.stalkMap p'.1).hom s)`. Establish `hm : (f.stalkMap p'.1).hom s * t = 1`.

Apply `hG'.inj p'` to reduce the goal to its premises. Rewrite using `[map_mul, map_one, K, ht, mul_inv_cancel₀ ((map_ne_zero i).mpr h0)]`. Conclude with `isUnit_iff_exists_inv.mpr ⟨t, hm⟩`. Take `⟨v, hv⟩` from `(isUnit_map_iff (f.stalkMap p'.1).hom s).mp hu`. Use `RingHom.mem_range.mpr ⟨↑v⁻¹, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hv, map_units_inv]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨(map_ne_zero i).mpr h1, fun c' => ?_⟩` and prove the remaining obligations. Use `show i (x c') / i (x c₁) ∈ regAt ξ' p'`.

Rewrite using `[← map_div₀]`. Conclude with `F1 _ (h2 c')`. Introduce and unpack `⟨h1, h2⟩`. Establish `h1' : x c₁ ≠ 0` using `fun h0 => h1 (by simp [h0])`. Take `⟨c, hc⟩` from `hT.cover q`.

Take `⟨hc0, hc⟩` from `hc`. Use `⟨h1', fun c' => ?_⟩` and prove the remaining obligations. Establish `hinv : (i (x c₁ / x c))⁻¹ ∈ regAt ξ' p'`. Rewrite using `[map_div₀, inv_div]`. Conclude with `h2 c`.

Establish `hw` using `F2 _ (hc c₁) hinv`. Establish `e : x c' / x c₁ = (x c' / x c) * (x c₁ / x c)⁻¹`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `mul_mem (hc c') hw`.
-/
theorem PositivityTheory.Xgp.inChart_iff_inChart_map_of_dominates : ∀ (X X' : Scheme.{0}) (Ω G : Type) [Field Ω] [Field G] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of G) ⟶ X') (f : X' ⟶ X) (i : Ω →+* G) (κ : Type) (x : κ → Ω), CoordTie ℤ ξ x → IsCptGen ξ' → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∀ (p' : Cpt ξ') (c₁ : κ) (h : genPt ξ ⤳ f p'.1), InChart ξ x c₁ ⟨f p'.1, h⟩ ↔ InChart ξ' (fun k => i (x k)) c₁ p' := by
  intro X X' Ω G _ _ ξ ξ' f i κ x hT hG' hD p' c₁ h
  set q : Cpt ξ := ⟨f p'.1, h⟩ with hq
  have K : ∀ s : X.presheaf.stalk (f p'.1), genMap ξ' p' ((f.stalkMap p'.1).hom s) = i (genMap ξ q s) := by
    intro s
    have e1 := stalkClosedPointTo_stalkSpecializes_comp ξ i (ξ' ≫ f) hD (f p'.1) (f.base.hom.map_specializes p'.2) h s
    rw [Scheme.stalkClosedPointTo_comp] at e1
    exact (congrArg (Scheme.stalkClosedPointTo ξ').hom
      (Scheme.Hom.stalkSpecializes_stalkMap_apply f _ _ p'.2 s).symm).trans e1
  have F1 : ∀ a, a ∈ regAt ξ q → i a ∈ regAt ξ' p' := by
    intro a ha
    obtain ⟨s, rfl⟩ := RingHom.mem_range.mp ha
    exact RingHom.mem_range.mpr ⟨_, K s⟩
  have F2 : ∀ a, a ∈ regAt ξ q → (i a)⁻¹ ∈ regAt ξ' p' → a⁻¹ ∈ regAt ξ q := by
    intro a ha hinv
    obtain ⟨s, rfl⟩ := RingHom.mem_range.mp ha
    obtain ⟨t, ht⟩ := RingHom.mem_range.mp hinv
    by_cases h0 : genMap ξ q s = 0
    · rw [h0, _root_.inv_zero]
      exact zero_mem _
    have hu : IsUnit ((f.stalkMap p'.1).hom s) := by
      have hm : (f.stalkMap p'.1).hom s * t = 1 := by
        apply hG'.inj p'
        rw [map_mul, map_one, K, ht, mul_inv_cancel₀ ((map_ne_zero i).mpr h0)]
      exact isUnit_iff_exists_inv.mpr ⟨t, hm⟩
    obtain ⟨v, hv⟩ := (isUnit_map_iff (f.stalkMap p'.1).hom s).mp hu
    refine RingHom.mem_range.mpr ⟨↑v⁻¹, ?_⟩
    rw [← hv, map_units_inv]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(map_ne_zero i).mpr h1, fun c' => ?_⟩
    show i (x c') / i (x c₁) ∈ regAt ξ' p'
    rw [← map_div₀]
    exact F1 _ (h2 c')
  · rintro ⟨h1, h2⟩
    have h1' : x c₁ ≠ 0 := fun h0 => h1 (by simp [h0])
    obtain ⟨c, hc⟩ := hT.cover q
    obtain ⟨hc0, hc⟩ := hc
    refine ⟨h1', fun c' => ?_⟩
    have hinv : (i (x c₁ / x c))⁻¹ ∈ regAt ξ' p' := by
      rw [map_div₀, inv_div]
      exact h2 c
    have hw := F2 _ (hc c₁) hinv
    have e : x c' / x c₁ = (x c' / x c) * (x c₁ / x c)⁻¹ := by
      field_simp
    rw [e]
    exact mul_mem (hc c') hw
