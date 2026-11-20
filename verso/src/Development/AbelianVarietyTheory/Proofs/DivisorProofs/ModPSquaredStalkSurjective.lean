import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI.StalkKer

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
/- English proof (translation)
Use `map_natCast ((X.presheaf.germ ⊤ x trivial).hom.comp ((f.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of (ZMod n))).inv.hom)) n` as an intermediate fact. Rewrite using `[← this, ZMod.natCast_self, map_zero]`.
-/
private lemma natCast_eq_zero_stalk_of_over_zmod (n : ℕ) {X : Scheme} (f : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (ZMod n)) (x : X) :
    ((n : ℕ) : X.presheaf.stalk x) = 0 := by
  have := map_natCast ((X.presheaf.germ ⊤ x trivial).hom.comp
    ((f.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of (ZMod n))).inv.hom)) n
  rw [← this, ZMod.natCast_self, map_zero]

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
/- English proof (translation)
Substitute `hy` using the available equality. Establish `h1` using `Scheme.Spec_stalkClosedPointTo_fromSpecStalk (h ≫ π)`. Establish `h2 : Scheme.stalkClosedPointTo (h ≫ π) = q` using `Spec.map_injective ((cancel_mono (Y.fromSpecStalk _)).1 (h1.trans hh))`. Rewrite using `[← h2, Scheme.stalkClosedPointTo_comp]`. Simplify using `[hz]`.
-/
private lemma stalk_hom_eq_zero_of_stalkMap_eq_zero {X Y : Scheme} (π : X ⟶ Y) (y : X) {R : CommRingCat}
    [IsLocalRing R] (h : Spec R ⟶ X) (hy : h (IsLocalRing.closedPoint R) = y)
    (q : Y.presheaf.stalk (π y) ⟶ R) (hh : h ≫ π = Spec.map q ≫ Y.fromSpecStalk (π y))
    (z : Y.presheaf.stalk (π y)) (hz : (π.stalkMap y).hom z = 0) : q.hom z = 0 := by
  subst hy
  have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (h ≫ π)
  have h2 : Scheme.stalkClosedPointTo (h ≫ π) = q :=
    Spec.map_injective ((cancel_mono (Y.fromSpecStalk _)).1 (h1.trans hh))
  rw [← h2, Scheme.stalkClosedPointTo_comp]
  simp [hz]

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in

/- English proof (translation)
Introduce `p hp Y X g f π hPB y`. Establish `hci : IsClosedImmersion π` using `MorphismProperty.of_isPullback (P := @IsClosedImmersion) hPB.flip (IsClosedImmersion.spec_of_surjective _ (ZMod.ringHom_surjective _))`. Use `⟨π.stalkMap_surjective y, fun z => ⟨fun hz => ?_, ?_⟩⟩` and prove the remaining obligations. Set `O` to `Y.presheaf.stalk (π y)`. Set `I : Ideal O` to `Ideal.span {((p : ℕ) : O)}`.

Establish `hsq : ((p : ℕ) : O) ^ 2 = 0`. Rewrite using `[← Nat.cast_pow]`. Conclude with `natCast_eq_zero_stalk_of_over_zmod (p ^ 2) g (π y)`. Establish `hI : I ≠ ⊤`. Introduce `hT`.

Establish `hu : IsUnit ((p : ℕ) : O)` using `Ideal.span_singleton_eq_top.1 hT`. Establish `h0 : IsUnit (0 : O)` using `hsq ▸ hu.pow 2`. Conclude with `zero_ne_one (isUnit_zero_iff.1 h0)`. Use `haveI : Nontrivial (O ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI`. Use `haveI : IsLocalRing (O ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective`.

Use `haveI hloc : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective`. Establish `hpQ : ((p : ℕ) : O ⧸ I) = 0`. Rewrite using `[← map_natCast (Ideal.Quotient.mk I)]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)`. Use `haveI : CharP (O ⧸ I) p := ringChar.of_eq (CharP.ringChar_of_prime_eq_zero hp.out hpQ)`.

Set `q : O ⟶ CommRingCat.of (O ⧸ I)` to `CommRingCat.ofHom (Ideal.Quotient.mk I)`. Use `haveI : IsLocalHom q.hom := hloc`. Set `a : Spec (CommRingCat.of (O ⧸ I)) ⟶ Y` to `Spec.map q ≫ Y.fromSpecStalk (π y)`. Set `b : Spec (CommRingCat.of (O ⧸ I)) ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (ZMod p)` to `Spec.map (CommRingCat.ofHom (ZMod.castHom (dvd_refl p) (O ⧸ I)))`. Establish `hcomm : a ≫ g = b ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))`.

Take `⟨φ, hφ⟩` from `Spec.map_surjective (a ≫ g)`. Rewrite using `[← hφ]`. Express the relevant statement in the definitionally equal form `Spec.map φ = Spec.map _ ≫ Spec.map _`. Rewrite using `[← Spec.map_comp]`. Use `congr 1`.

Apply `CommRingCat.hom_ext` to reduce the goal to its premises. Conclude with `RingHom.ext_zmod _ _`. Set `h` to `hPB.lift a b hcomm`. Establish `hh : h ≫ π = a` using `hPB.lift_fst a b hcomm`. Establish `hy : h (IsLocalRing.closedPoint (O ⧸ I)) = y`.

Apply `π.isClosedEmbedding.injective` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(h ≫ π) _ = _`. Rewrite using `[hh]`. Express the relevant statement in the definitionally equal form `Y.fromSpecStalk (π y) ((Spec.map q) (IsLocalRing.closedPoint (O ⧸ I))) = π y`. Rewrite using `[Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]`.

Establish `hq` using `stalk_hom_eq_zero_of_stalkMap_eq_zero π y h hy q hh z hz`. Establish `hmem : z ∈ I` using `Ideal.Quotient.eq_zero_iff_mem.1 hq`. Take `⟨w, hw⟩` from `Ideal.mem_span_singleton'.1 hmem`. Conclude with `⟨w, by rw [← hw, mul_comm]⟩`. Introduce and unpack `⟨w, rfl⟩`.

Rewrite using `[map_mul, map_natCast, natCast_eq_zero_stalk_of_over_zmod p f y, zero_mul]`.
-/
theorem _root_.GlobalTheory.DI.StalkKer.stalkMap_surjective_ker : ∀ (p : ℕ) [Fact p.Prime] (Y X : Scheme.{0})
    (g : Y ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (ZMod (p ^ 2))) (f : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (ZMod p)) (π : X ⟶ Y),
    IsPullback π f g (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))) →
    ∀ y : X, Function.Surjective (π.stalkMap y).hom ∧
      ∀ z, (π.stalkMap y).hom z = 0 ↔ ∃ w, z = p * w := by
  intro p hp Y X g f π hPB y
  have hci : IsClosedImmersion π :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hPB.flip
      (IsClosedImmersion.spec_of_surjective _ (ZMod.ringHom_surjective _))
  refine ⟨π.stalkMap_surjective y, fun z => ⟨fun hz => ?_, ?_⟩⟩
  · let O := Y.presheaf.stalk (π y)
    let I : Ideal O := Ideal.span {((p : ℕ) : O)}
    have hsq : ((p : ℕ) : O) ^ 2 = 0 := by
      rw [← Nat.cast_pow]; exact natCast_eq_zero_stalk_of_over_zmod (p ^ 2) g (π y)
    have hI : I ≠ ⊤ := by
      intro hT
      have hu : IsUnit ((p : ℕ) : O) := Ideal.span_singleton_eq_top.1 hT
      have h0 : IsUnit (0 : O) := hsq ▸ hu.pow 2
      exact zero_ne_one (isUnit_zero_iff.1 h0)
    haveI : Nontrivial (O ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
    haveI : IsLocalRing (O ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    haveI hloc : IsLocalHom (Ideal.Quotient.mk I) :=
      IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    have hpQ : ((p : ℕ) : O ⧸ I) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk I)]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    haveI : CharP (O ⧸ I) p := ringChar.of_eq (CharP.ringChar_of_prime_eq_zero hp.out hpQ)
    let q : O ⟶ CommRingCat.of (O ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
    haveI : IsLocalHom q.hom := hloc
    let a : Spec (CommRingCat.of (O ⧸ I)) ⟶ Y := Spec.map q ≫ Y.fromSpecStalk (π y)
    let b : Spec (CommRingCat.of (O ⧸ I)) ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (ZMod p) :=
      Spec.map (CommRingCat.ofHom (ZMod.castHom (dvd_refl p) (O ⧸ I)))
    have hcomm : a ≫ g = b ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)) := by
      obtain ⟨φ, hφ⟩ := Spec.map_surjective (a ≫ g)
      rw [← hφ]
      change Spec.map φ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      exact RingHom.ext_zmod _ _
    let h := hPB.lift a b hcomm
    have hh : h ≫ π = a := hPB.lift_fst a b hcomm
    have hy : h (IsLocalRing.closedPoint (O ⧸ I)) = y := by
      apply π.isClosedEmbedding.injective
      change (h ≫ π) _ = _
      rw [hh]
      change Y.fromSpecStalk (π y) ((Spec.map q) (IsLocalRing.closedPoint (O ⧸ I))) = π y
      rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
    have hq := stalk_hom_eq_zero_of_stalkMap_eq_zero π y h hy q hh z hz
    have hmem : z ∈ I := Ideal.Quotient.eq_zero_iff_mem.1 hq
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hmem
    exact ⟨w, by rw [← hw, mul_comm]⟩
  · rintro ⟨w, rfl⟩
    rw [map_mul, map_natCast, natCast_eq_zero_stalk_of_over_zmod p f y, zero_mul]

end GlobalTheory.DI.StalkKer
