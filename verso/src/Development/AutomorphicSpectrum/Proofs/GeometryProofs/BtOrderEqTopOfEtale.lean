import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.Ar.BT.EtaleTop

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

/- English proof (translation)
Use `haveI : y.asIdeal.IsPrime := PrimeSpectrum.isPrime (R := R) y`. Use `letI : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk y) := StructureSheaf.stalkAlgebra R y`. Establish `: IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk y) y.asIdeal` using `StructureSheaf.IsLocalization.to_stalk R y`. Conclude with `GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_isDomain y.asIdeal _`.
-/
theorem stalk_spec_normal [IsIntegrallyClosed R] (y : Spec (CommRingCat.of R)) :
    IsDomain ((Spec (CommRingCat.of R)).presheaf.stalk y) ∧
      IsIntegrallyClosed ((Spec (CommRingCat.of R)).presheaf.stalk y) := by
  haveI : y.asIdeal.IsPrime := PrimeSpectrum.isPrime (R := R) y
  letI : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk y) := StructureSheaf.stalkAlgebra R y
  have : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk y) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R y
  exact GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_isDomain y.asIdeal _

/- English proof (translation)
Establish `hw : (Γ.pt t).left ≫ Γ.G.hom = (genPt R).hom` using `Over.w (Γ.pt t)`. Establish `: Γ.G.hom ((Γ.pt t).left x) = (genPt R).hom x`. Rewrite using `[← hw]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Use `show Ideal.comap (algebraMap R (FractionRing R)) x.asIdeal = ⊥`. Establish `hx : x.asIdeal = ⊥` using `@Ideal.eq_bot_of_prime _ _ x.asIdeal x.isPrime`. Rewrite using `[hx, ← RingHom.ker_eq_comap_bot]`. Conclude with `(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))`.
-/
theorem genPt_asIdeal (Γ : QFGroup R T) (t : T) (x : Spec (CommRingCat.of (FractionRing R))) :
    (Γ.G.hom ((Γ.pt t).left x)).asIdeal = ⊥ := by
  have hw : (Γ.pt t).left ≫ Γ.G.hom = (genPt R).hom := Over.w (Γ.pt t)
  have : Γ.G.hom ((Γ.pt t).left x) = (genPt R).hom x := by
    rw [← hw]; rfl
  rw [this]
  show Ideal.comap (algebraMap R (FractionRing R)) x.asIdeal = ⊥
  have hx : x.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ x.asIdeal x.isPrime
  rw [hx, ← RingHom.ker_eq_comap_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))

/- English proof (translation)
Establish `h' : @LE.le (PrimeSpectrum R) _ y z` using `(PrimeSpectrum.le_iff_specializes (R := R) y z).2 h`. Establish `h'' : y.asIdeal ≤ z.asIdeal` using `h'`. Use `PrimeSpectrum.ext (le_antisymm h'' ?_)` and prove the remaining obligations. Rewrite using `[hz]`. Conclude with `bot_le`.
-/
theorem eq_of_specializes_bot {y z : Spec (CommRingCat.of R)} (h : y ⤳ z) (hz : z.asIdeal = ⊥) :
    y = z := by
  have h' : @LE.le (PrimeSpectrum R) _ y z := (PrimeSpectrum.le_iff_specializes (R := R) y z).2 h
  have h'' : y.asIdeal ≤ z.asIdeal := h'
  refine PrimeSpectrum.ext (le_antisymm h'' ?_)
  rw [hz]; exact bot_le

/- English proof (translation)
Establish `hd` using `(f.isDiscrete_preimage_singleton (f b)).to_subtype`. Establish `: (⟨a, e⟩ : f ⁻¹' {f b}) ⤳ ⟨b, rfl⟩` using `Topology.IsInducing.subtypeVal.specializes_iff.mp h`. Conclude with `congrArg Subtype.val this.eq`.
-/
theorem eq_of_specializes_lqf {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyQuasiFinite f] {a b : X}
    (h : a ⤳ b) (e : f a = f b) : a = b := by
  have hd := (f.isDiscrete_preimage_singleton (f b)).to_subtype
  have : (⟨a, e⟩ : f ⁻¹' {f b}) ⤳ ⟨b, rfl⟩ := Topology.IsInducing.subtypeVal.specializes_iff.mp h
  exact congrArg Subtype.val this.eq

/- English proof (translation)
Use `Γ.quasiFinite` as an intermediate fact. Take `⟨h1, h2⟩` from `stalk_spec_normal (R := R) (Γ.G.hom g)`. Establish `hdom : IsDomain (Γ.G.left.presheaf.stalk g)` using `(GlobalTheory.isDomain_and_isIntegrallyClosed_stalk_of_smooth Γ.G.hom g).1`. Set `e₀ : Spec (Γ.G.left.presheaf.stalk g)` to `(⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum _)`. Establish `key : ∀ u : T, (Γ.pt u).left x ⤳ g → Γ.G.left.fromSpecStalk g e₀ = (Γ.pt u).left x`.

Introduce `u hu`. Establish `hr : (Γ.pt u).left x ∈ Set.range (Γ.G.left.fromSpecStalk g)`. Rewrite using `[Scheme.range_fromSpecStalk]`. Conclude with `hu`. Take `⟨a, ha⟩` from `hr`.

Establish `he₀a : e₀ ⤳ a` using `(PrimeSpectrum.le_iff_specializes (R := Γ.G.left.presheaf.stalk g) e₀ a).1 (show (⊥ : Ideal _) ≤ _ from bot_le)`. Establish `h3 : Γ.G.left.fromSpecStalk g e₀ ⤳ (Γ.pt u).left x` using `ha ▸ he₀a.map (Γ.G.left.fromSpecStalk g).continuous`. Use `eq_of_specializes_lqf Γ.G.hom h3 ?_` and prove the remaining obligations. Conclude with `eq_of_specializes_bot (h3.map Γ.G.hom.continuous) (genPt_asIdeal Γ u x)`. Conclude with `Γ.pt_inj s t x x ((key s hs).symm.trans (key t ht))`.
-/
theorem eq_of_specializes_pt [IsIntegrallyClosed R] (Γ : QFGroup R T) (hE : Etale Γ.G.hom)
    (x : Spec (CommRingCat.of (FractionRing R))) (g : Γ.G.left) (s t : T)
    (hs : (Γ.pt s).left x ⤳ g) (ht : (Γ.pt t).left x ⤳ g) : s = t := by
  have := Γ.quasiFinite
  obtain ⟨h1, h2⟩ := stalk_spec_normal (R := R) (Γ.G.hom g)
  have hdom : IsDomain (Γ.G.left.presheaf.stalk g) :=
    (GlobalTheory.isDomain_and_isIntegrallyClosed_stalk_of_smooth Γ.G.hom g).1
  let e₀ : Spec (Γ.G.left.presheaf.stalk g) := (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum _)
  have key : ∀ u : T, (Γ.pt u).left x ⤳ g → Γ.G.left.fromSpecStalk g e₀ = (Γ.pt u).left x := by
    intro u hu
    have hr : (Γ.pt u).left x ∈ Set.range (Γ.G.left.fromSpecStalk g) := by
      rw [Scheme.range_fromSpecStalk]; exact hu
    obtain ⟨a, ha⟩ := hr
    have he₀a : e₀ ⤳ a := (PrimeSpectrum.le_iff_specializes (R := Γ.G.left.presheaf.stalk g) e₀ a).1
      (show (⊥ : Ideal _) ≤ _ from bot_le)
    have h3 : Γ.G.left.fromSpecStalk g e₀ ⤳ (Γ.pt u).left x := ha ▸ he₀a.map (Γ.G.left.fromSpecStalk g).continuous
    refine eq_of_specializes_lqf Γ.G.hom h3 ?_
    exact eq_of_specializes_bot (h3.map Γ.G.hom.continuous) (genPt_asIdeal Γ u x)
  exact Γ.pt_inj s t x x ((key s hs).symm.trans (key t ht))

/- English proof (translation)
Substitute `hf` using the available equality. Establish `: (genPt R).hom.appLE ⊤ ⊤ e = (genPt R).hom.appTop` using `rfl`. Rewrite using `[this]`. Express the relevant statement in the definitionally equal form `(Scheme.ΓSpecIso _).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))).appTop ≫ _ = _`. Rewrite using `[Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]`.
-/
theorem genPt_appLE (f : Spec (CommRingCat.of (FractionRing R)) ⟶ Spec (CommRingCat.of R))
    (hf : f = (genPt R).hom) (e) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ ⊤ e ≫
        (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom =
      CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
  subst hf
  have : (genPt R).hom.appLE ⊤ ⊤ e = (genPt R).hom.appTop := rfl
  rw [this]
  change (Scheme.ΓSpecIso _).inv ≫
    (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))).appTop ≫ _ = _
  rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

/- English proof (translation)
Set `x₀ : Spec (CommRingCat.of (FractionRing R))` to `(IsLocalRing.closedPoint (FractionRing R) : PrimeSpectrum _)`. Set `P : T → Γ.G.left` to `fun t => (Γ.pt t).left x₀`. Set `Z : Set Γ.G.left` to `⋃ t ∈ {t | ¬ P t ⤳ g}, closure {P t}`. Establish `hZ : IsClosed Z` using `(Set.toFinite _).isClosed_biUnion fun _ _ => isClosed_closure`. Set `U : Γ.G.left.Opens` to `⟨Zᶜ, hZ.isOpen_compl⟩`.

Establish `hgU : g ∈ U` using `by show g ∉ Z`. Simplify using `only [Z, Set.mem_iUnion, Set.mem_setOf_eq, not_exists]`. Introduce `t ht hg`. Conclude with `ht (specializes_iff_mem_closure.2 hg)`. Establish `hPU : ∀ t, P t ∈ U → P t ⤳ g`.

Introduce `t ht`. Assume the negation of the conclusion as `hn`. Conclude with `ht (Set.mem_biUnion (x := t) hn (subset_closure rfl))`. Use `⟨U, hgU, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hex : ∃ t₀, P t₀ ⤳ g`.

Take `⟨t₀, ht₀⟩` from `hex`. Use `⟨(Γ.G.hom.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (φ t₀)), ?_⟩` and prove the remaining obligations. Introduce `t h`. Establish `htU : P t ∈ U` using `h (show x₀ ∈ (⊤ : (Spec (CommRingCat.of (FractionRing R))).Opens) from trivial)`. Use `eq_of_specializes_pt Γ hE x₀ g t t₀ (hPU t htU) ht₀` as an intermediate fact.

Substitute `this` using the available equality. Establish `hw : (Γ.pt t).left ≫ Γ.G.hom = (genPt R).hom` using `Over.w (Γ.pt t)`. Establish `key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ Γ.G.hom.appLE ⊤ U le_top ≫ (Γ.pt t).left.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom = CommRingCat.ofHom (algebraMap R (FractionRing R))` using `by erw [Scheme.Hom.appLE_comp_appLE_assoc]`. Conclude with `genPt_appLE _ hw _`. Conclude with `congrArg (fun m => m.hom (φ t)) key`.

Use `⟨0, fun t h => ?_⟩` and prove the remaining obligations. Conclude with `absurd ⟨t, hPU t (h (show x₀ ∈ (⊤ : (Spec (CommRingCat.of (FractionRing R))).Opens) from trivial))⟩ hex`.
-/
theorem regularAt_const [Finite T] [IsIntegrallyClosed R] (Γ : QFGroup R T) (hE : Etale Γ.G.hom)
    (φ : T → R) (g : Γ.G.left) :
    Γ.RegularAt (fun h => algebraMap R (FractionRing R) (φ h)) g := by
  classical
  let x₀ : Spec (CommRingCat.of (FractionRing R)) :=
    (IsLocalRing.closedPoint (FractionRing R) : PrimeSpectrum _)
  let P : T → Γ.G.left := fun t => (Γ.pt t).left x₀
  let Z : Set Γ.G.left := ⋃ t ∈ {t | ¬ P t ⤳ g}, closure {P t}
  have hZ : IsClosed Z := (Set.toFinite _).isClosed_biUnion fun _ _ => isClosed_closure
  let U : Γ.G.left.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
  have hgU : g ∈ U := by
    show g ∉ Z
    simp only [Z, Set.mem_iUnion, Set.mem_setOf_eq, not_exists]
    intro t ht hg
    exact ht (specializes_iff_mem_closure.2 hg)
  have hPU : ∀ t, P t ∈ U → P t ⤳ g := by
    intro t ht
    by_contra hn
    exact ht (Set.mem_biUnion (x := t) hn (subset_closure rfl))
  refine ⟨U, hgU, ?_⟩
  by_cases hex : ∃ t₀, P t₀ ⤳ g
  · obtain ⟨t₀, ht₀⟩ := hex
    refine ⟨(Γ.G.hom.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (φ t₀)), ?_⟩
    intro t h
    have htU : P t ∈ U := h (show x₀ ∈ (⊤ : (Spec (CommRingCat.of (FractionRing R))).Opens) from trivial)
    have := eq_of_specializes_pt Γ hE x₀ g t t₀ (hPU t htU) ht₀
    subst this
    have hw : (Γ.pt t).left ≫ Γ.G.hom = (genPt R).hom := Over.w (Γ.pt t)
    have key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ Γ.G.hom.appLE ⊤ U le_top ≫
        (Γ.pt t).left.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom =
          CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
      erw [Scheme.Hom.appLE_comp_appLE_assoc]
      exact genPt_appLE _ hw _
    exact congrArg (fun m => m.hom (φ t)) key
  · refine ⟨0, fun t h => ?_⟩
    exact absurd ⟨t, hPU t (h (show x₀ ∈ (⊤ : (Spec (CommRingCat.of (FractionRing R))).Opens) from trivial))⟩ hex

/- English proof (translation)
Introduce `R _ _ _ T _ _ Γ hE`. Use `eq_top_iff.2 fun f _ => Algebra.subset_adjoin ?_` and prove the remaining obligations. Introduce `t g _`. Conclude with `regularAt_const Γ hE (fun h => f (t * h)) g`.
-/
theorem btOrder_top_eq_top_of_etale : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T), Etale Γ.G.hom → Γ.btOrder ⊤ = ⊤ := by
  intro R _ _ _ T _ _ Γ hE
  refine eq_top_iff.2 fun f _ => Algebra.subset_adjoin ?_
  intro t g _
  exact regularAt_const Γ hE (fun h => f (t * h)) g

end GlobalTheory.CompanionTheory.Ar.BT.EtaleTop
