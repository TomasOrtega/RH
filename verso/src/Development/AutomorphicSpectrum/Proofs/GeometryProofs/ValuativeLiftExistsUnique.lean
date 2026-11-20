import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

namespace CoordExtend

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def valC {R : Type} [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X) :
    X.presheaf.stalk (centre z) ⟶ CommRingCat.of R :=
  Scheme.stalkClosedPointTo z

abbrev val {R : Type} [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X) :
    X.presheaf.stalk (centre z) →+* R :=
  (valC z).hom

instance {R : Type} [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X) :
    IsLocalHom (val z) :=
  Scheme.isLocalHom_stalkClosedPointTo' z

def gm (ξ : Spec (CommRingCat.of Ω) ⟶ X) {p : X} (h : genPt ξ ⤳ p) : X.presheaf.stalk p →+* Ω :=
  genMap ξ ⟨p, h⟩

/- English proof (translation)
The claim follows from `hG.inj ⟨p, h⟩`.
-/
theorem gm_inj {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hG : IsCptGen ξ) {p : X} (h : genPt ξ ⤳ p) :
    Function.Injective (gm ξ h) :=
  hG.inj ⟨p, h⟩

/- English proof (translation)
The claim follows from `RingHom.mem_range.1 ha`.
-/
theorem exists_gm {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : X} {h : genPt ξ ⤳ p} {a : Ω}
    (ha : a ∈ regAt ξ ⟨p, h⟩) : ∃ s : X.presheaf.stalk p, gm ξ h s = a :=
  RingHom.mem_range.1 ha

/- English proof (translation)
The claim follows from `RingHom.mem_range.2 ⟨s, rfl⟩`.
-/
theorem mem_regAt_of_gm {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : X} {h : genPt ξ ⤳ p}
    (s : X.presheaf.stalk p) : gm ξ h s ∈ regAt ξ ⟨p, h⟩ :=
  RingHom.mem_range.2 ⟨s, rfl⟩

/- English proof (translation)
Establish `e : Spec.map (X.presheaf.germ U (centre f) h) ≫ hU.fromSpec = X.fromSpecStalk (centre f)`. Rewrite using `[← hU.fromSpecStalk_eq_fromSpecStalk h]`. Both sides reduce to the same expression. Rewrite using `[Spec.map_comp, Category.assoc, e]`. Conclude with `Scheme.Spec_stalkClosedPointTo_fromSpecStalk f`.
-/
theorem spec_germ_fromSpec {R : Type} [CommRing R] [IsLocalRing R] (f : Spec (CommRingCat.of R) ⟶ X)
    {U : X.Opens} (hU : IsAffineOpen U) (h : centre f ∈ U) :
    Spec.map (X.presheaf.germ U (centre f) h ≫ valC f) ≫ hU.fromSpec = f := by
  have e : Spec.map (X.presheaf.germ U (centre f) h) ≫ hU.fromSpec = X.fromSpecStalk (centre f) := by
    rw [← hU.fromSpecStalk_eq_fromSpecStalk h]; rfl
  rw [Spec.map_comp, Category.assoc, e]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk f

/- English proof (translation)
Take `⟨W, hW, g, rfl⟩` from `X.presheaf.germ_exist s`. Take `⟨_, ⟨U, hU, rfl⟩, hmem, hle⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open hW W.2`. Use `replace hU : IsAffineOpen U := hU`. Establish `hUW : U ≤ W` using `hle`. Establish `hmem' : centre (Spec.map τ ≫ f) ∈ U` using `w.mem_open U.2 hmem`.

Establish `h1` using `spec_germ_fromSpec f hU hmem`. Establish `h2` using `spec_germ_fromSpec (Spec.map τ ≫ f) hU hmem'`. Establish `h3 : X.presheaf.germ U _ hmem' ≫ valC (Spec.map τ ≫ f) = (X.presheaf.germ U _ hmem ≫ valC f) ≫ τ`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[← cancel_mono hU.fromSpec, h2, Spec.map_comp, Category.assoc, h1]`.

Establish `h5 : X.presheaf.germ U _ hmem ≫ X.presheaf.stalkSpecializes w = X.presheaf.germ U _ hmem'` using `TopCat.Presheaf.germ_stalkSpecializes ..`. Rewrite `h3` using `[← h5, Category.assoc]`. Establish `h6 : X.presheaf.map (homOfLE hUW).op ≫ X.presheaf.germ U _ hmem = X.presheaf.germ W _ hW` using `X.presheaf.germ_res (homOfLE hUW) _ hmem`. Rewrite using `[← h6]`. Conclude with `congrArg (fun q => q.hom ((X.presheaf.map (homOfLE hUW).op).hom g)) h3`.
-/
theorem val_specializes {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    (τ : CommRingCat.of R ⟶ CommRingCat.of S) (f : Spec (CommRingCat.of R) ⟶ X)
    (w : centre (Spec.map τ ≫ f) ⤳ centre f) (s : X.presheaf.stalk (centre f)) :
    val (Spec.map τ ≫ f) ((X.presheaf.stalkSpecializes w).hom s) = τ.hom (val f s) := by
  obtain ⟨W, hW, g, rfl⟩ := X.presheaf.germ_exist s
  obtain ⟨_, ⟨U, hU, rfl⟩, hmem, hle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hW W.2
  replace hU : IsAffineOpen U := hU
  have hUW : U ≤ W := hle
  have hmem' : centre (Spec.map τ ≫ f) ∈ U := w.mem_open U.2 hmem
  have h1 := spec_germ_fromSpec f hU hmem
  have h2 := spec_germ_fromSpec (Spec.map τ ≫ f) hU hmem'
  have h3 : X.presheaf.germ U _ hmem' ≫ valC (Spec.map τ ≫ f) =
      (X.presheaf.germ U _ hmem ≫ valC f) ≫ τ := by
    apply Spec.map_injective
    rw [← cancel_mono hU.fromSpec, h2, Spec.map_comp, Category.assoc, h1]
  have h5 : X.presheaf.germ U _ hmem ≫ X.presheaf.stalkSpecializes w = X.presheaf.germ U _ hmem' :=
    TopCat.Presheaf.germ_stalkSpecializes ..
  rw [← h5, Category.assoc] at h3
  have h6 : X.presheaf.map (homOfLE hUW).op ≫ X.presheaf.germ U _ hmem = X.presheaf.germ W _ hW :=
    X.presheaf.germ_res (homOfLE hUW) _ hmem
  rw [← h6]
  exact congrArg (fun q => q.hom ((X.presheaf.map (homOfLE hUW).op).hom g)) h3

def gpC (ξ : Spec (CommRingCat.of Ω) ⟶ X) : X.presheaf.stalk (genPt ξ) ⟶ CommRingCat.of Ω :=
  Scheme.stalkClosedPointTo ξ

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(X.presheaf.stalkSpecializes w ≫ X.presheaf.stalkSpecializes hp ≫ gpC ξ).hom t = (X.presheaf.stalkSpecializes hq ≫ gpC ξ).hom t`. Rewrite using `[← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]`.
-/
theorem gm_specializes (ξ : Spec (CommRingCat.of Ω) ⟶ X) {p q : X} (hp : genPt ξ ⤳ p) (hq : genPt ξ ⤳ q)
    (w : p ⤳ q) (t : X.presheaf.stalk q) :
    gm ξ hp ((X.presheaf.stalkSpecializes w).hom t) = gm ξ hq t := by
  change (X.presheaf.stalkSpecializes w ≫ X.presheaf.stalkSpecializes hp ≫ gpC ξ).hom t =
    (X.presheaf.stalkSpecializes hq ≫ gpC ξ).hom t
  rw [← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]

/- English proof (translation)
Establish `hg : genPt ξ ∈ U` using `hp.mem_open U.2 hpU`. Establish `e : ∀ (r : X) (hr : genPt ξ ⤳ r) (hrU : r ∈ U), gm ξ hr ((X.presheaf.germ U r hrU).hom g) = (X.presheaf.germ U (genPt ξ) hg ≫ gpC ξ).hom g`. Introduce `r hr hrU`. Express the relevant statement in the definitionally equal form `(X.presheaf.germ U r hrU ≫ X.presheaf.stalkSpecializes hr ≫ gpC ξ).hom g = _`. Rewrite using `[TopCat.Presheaf.germ_stalkSpecializes_assoc]`.

Rewrite using `[e p hp hpU, e q hq hqU]`.
-/
theorem gm_germ (ξ : Spec (CommRingCat.of Ω) ⟶ X) {U : X.Opens} {p q : X} (hp : genPt ξ ⤳ p)
    (hq : genPt ξ ⤳ q) (hpU : p ∈ U) (hqU : q ∈ U) (g : Γ(X, U)) :
    gm ξ hp ((X.presheaf.germ U p hpU).hom g) = gm ξ hq ((X.presheaf.germ U q hqU).hom g) := by
  have hg : genPt ξ ∈ U := hp.mem_open U.2 hpU
  have e : ∀ (r : X) (hr : genPt ξ ⤳ r) (hrU : r ∈ U), gm ξ hr ((X.presheaf.germ U r hrU).hom g) =
      (X.presheaf.germ U (genPt ξ) hg ≫ gpC ξ).hom g := by
    intro r hr hrU
    change (X.presheaf.germ U r hrU ≫ X.presheaf.stalkSpecializes hr ≫ gpC ξ).hom g = _
    rw [TopCat.Presheaf.germ_stalkSpecializes_assoc]
  rw [e p hp hpU, e q hq hqU]

def GoodChart {C : Type} [Field C] (V : ValuationSubring C) (ξ : Spec (CommRingCat.of Ω) ⟶ X) {κ : Type}
    (x : κ → Ω) (zC : Spec (CommRingCat.of C) ⟶ X) (h : genPt ξ ⤳ centre zC) (c : κ) : Prop :=
  x c ≠ 0 ∧ ∀ j, ∃ s : X.presheaf.stalk (centre zC), gm ξ h s = x j / x c ∧ val zC s ∈ V

/- English proof (translation)
Take `⟨c, hc, hreg⟩` from `hT.cover ⟨centre zC, h⟩`. Use `choose s hs using fun j => exists_gm (hreg j)`. Establish `: Nonempty κ` using `⟨c⟩`. Take `⟨d, hd⟩` from `Finite.exists_max (fun j => V.valuation (val zC (s j)))`. Establish `hsc : s c = 1` using `gm_inj hT.gen h (by rw [hs, map_one, div_self hc])`.

Establish `hv1 : val zC (s c) = 1` using `by rw [hsc, map_one]`. Establish `hr : val zC (s d) ≠ 0`. Introduce `h0`. Establish `h1` using `hd c`. Rewrite `h1` using `[hv1, h0]`.

Simplify using `at h1`. Establish `hunit : IsUnit (s d)` using `isUnit_of_map_unit (val zC) _ hr.isUnit`. Establish `hne : x d / x c ≠ 0`. Rewrite using `[← hs d]`. Conclude with `(hunit.map (gm ξ h)).ne_zero`.

Establish `hxd : x d ≠ 0` using `fun h0 => hne (by simp [h0])`. Take `⟨e, he⟩` from `hunit`. Use `⟨d, hxd, fun j => ⟨s j * (↑e⁻¹ : X.presheaf.stalk (centre zC)), ?_, ?_⟩⟩` and prove the remaining obligations. Establish `h1 : gm ξ h (↑e⁻¹ : X.presheaf.stalk (centre zC)) * (x d / x c) = 1`. Rewrite using `[← hs d, ← he, ← map_mul, Units.inv_mul, map_one]`.

Establish `h2 : gm ξ h (↑e⁻¹ : X.presheaf.stalk (centre zC)) = x c / x d`. Clear denominators, using `at h1 ⊢` for the nonvanishing conditions. Conclude with `h1`. Rewrite using `[map_mul, hs j, h2]`. Clear the denominators using the available nonvanishing facts.

Establish `h1 : val zC (↑e⁻¹ : X.presheaf.stalk (centre zC)) * val zC (s d) = 1`. Rewrite using `[← he, ← map_mul, Units.inv_mul, map_one]`. Establish `h2 : val zC (↑e⁻¹ : X.presheaf.stalk (centre zC)) = (val zC (s d))⁻¹` using `eq_inv_of_mul_eq_one_left h1`. Rewrite using `[map_mul, h2, ← V.valuation_le_one_iff, map_mul, map_inv₀, ← div_eq_mul_inv]`. Establish `hv : V.valuation (val zC (s d)) ≠ 0`.

Simplify using `using hr`. Conclude with `(div_le_one₀ (zero_lt_iff.2 hv)).2 (hd j)`.
-/
theorem exists_goodChart {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type} [Finite κ] {x : κ → Ω}
    (hT : CoordTie ℤ ξ x) {C : Type} [Field C] (V : ValuationSubring C)
    (zC : Spec (CommRingCat.of C) ⟶ X) (h : genPt ξ ⤳ centre zC) : ∃ c, GoodChart V ξ x zC h c := by
  obtain ⟨c, hc, hreg⟩ := hT.cover ⟨centre zC, h⟩
  choose s hs using fun j => exists_gm (hreg j)
  have : Nonempty κ := ⟨c⟩
  obtain ⟨d, hd⟩ := Finite.exists_max (fun j => V.valuation (val zC (s j)))
  have hsc : s c = 1 := gm_inj hT.gen h (by rw [hs, map_one, div_self hc])
  have hv1 : val zC (s c) = 1 := by rw [hsc, map_one]
  have hr : val zC (s d) ≠ 0 := by
    intro h0
    have h1 := hd c
    rw [hv1, h0] at h1
    simp at h1
  have hunit : IsUnit (s d) := isUnit_of_map_unit (val zC) _ hr.isUnit
  have hne : x d / x c ≠ 0 := by
    rw [← hs d]
    exact (hunit.map (gm ξ h)).ne_zero
  have hxd : x d ≠ 0 := fun h0 => hne (by simp [h0])
  obtain ⟨e, he⟩ := hunit
  refine ⟨d, hxd, fun j => ⟨s j * (↑e⁻¹ : X.presheaf.stalk (centre zC)), ?_, ?_⟩⟩
  · have h1 : gm ξ h (↑e⁻¹ : X.presheaf.stalk (centre zC)) * (x d / x c) = 1 := by
      rw [← hs d, ← he, ← map_mul, Units.inv_mul, map_one]
    have h2 : gm ξ h (↑e⁻¹ : X.presheaf.stalk (centre zC)) = x c / x d := by
      field_simp at h1 ⊢
      exact h1
    rw [map_mul, hs j, h2]
    field_simp
  · have h1 : val zC (↑e⁻¹ : X.presheaf.stalk (centre zC)) * val zC (s d) = 1 := by
      rw [← he, ← map_mul, Units.inv_mul, map_one]
    have h2 : val zC (↑e⁻¹ : X.presheaf.stalk (centre zC)) = (val zC (s d))⁻¹ :=
      eq_inv_of_mul_eq_one_left h1
    rw [map_mul, h2, ← V.valuation_le_one_iff, map_mul, map_inv₀, ← div_eq_mul_inv]
    have hv : V.valuation (val zC (s d)) ≠ 0 := by
      simpa using hr
    exact (div_le_one₀ (zero_lt_iff.2 hv)).2 (hd j)

/- English proof (translation)
Take `⟨hc, hj⟩` from `hg`. Take `⟨U, hU, hmem⟩` from `hT.affine c hc`. Establish `hch : InChart ξ x c ⟨centre zC, h⟩` using `⟨hc, fun j => by`. Take `⟨s, hs, -⟩` from `hj j`. Rewrite using `[← hs]`.

Conclude with `mem_regAt_of_gm s⟩`. Establish `hp : centre zC ∈ U` using `(hmem _).2 ⟨h, hch⟩`. Establish `hadj : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), ∃ s : X.presheaf.stalk (centre zC), gm ξ h s = a ∧ val zC s ∈ V`. Introduce `a ha`. Proceed by induction on `ha using Algebra.adjoin_induction with`.

Consider the case `mem a ha`. Take `⟨j, rfl⟩` from `ha`. Conclude with `hj j`. Consider the case `algebraMap n`. Use `⟨(n : X.presheaf.stalk (centre zC)), by simp, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_intCast]`. Conclude with `intCast_mem V n`. Consider the case `add a b _ _ iha ihb`. Take `⟨s, hs, hsV⟩` from `iha`. Take `⟨t, ht, htV⟩` from `ihb`.

Conclude with `⟨s + t, by rw [map_add, hs, ht], by rw [map_add]; exact add_mem hsV htV⟩`. Consider the case `mul a b _ _ iha ihb`. Take `⟨s, hs, hsV⟩` from `iha`. Take `⟨t, ht, htV⟩` from `ihb`. Conclude with `⟨s * t, by rw [map_mul, hs, ht], by rw [map_mul]; exact mul_mem hsV htV⟩`.

Set `ψ : Γ(X, U) ⟶ CommRingCat.of C` to `X.presheaf.germ U (centre zC) hp ≫ valC zC`. Establish `hψ : ∀ g, ψ.hom g ∈ V`. Introduce `g`. Establish `hreg : gm ξ h ((X.presheaf.germ U (centre zC) hp).hom g) ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c)`. Use `(hT.ring c hc _).2 fun p hpc => ?_` and prove the remaining obligations.

Establish `hpU : p.1 ∈ U` using `(hmem _).2 ⟨p.2, hpc⟩`. Rewrite using `[gm_germ ξ h p.2 hp hpU g]`. Conclude with `mem_regAt_of_gm _`. Take `⟨s, hs, hsV⟩` from `hadj _ hreg`. Use `gm_inj hT.gen h hs` as an intermediate fact.

Rewrite `hsV` using `[this]`. Conclude with `hsV`. Set `ρ : Γ(X, U) ⟶ CommRingCat.of V` to `CommRingCat.ofHom (ψ.hom.codRestrict V hψ)`. Establish `hρ : ρ ≫ CommRingCat.ofHom (algebraMap V C) = ψ`. Use extensionality with `g`.

Both sides reduce to the same expression. Establish `hzU : centre (Spec.map ρ ≫ hU.fromSpec) ∈ U`. Establish `h1 : centre (Spec.map ρ ≫ hU.fromSpec) ∈ Set.range hU.fromSpec` using `⟨Spec.map ρ (IsLocalRing.closedPoint V), rfl⟩`. Rewrite `h1` using `[hU.range_fromSpec]`. Conclude with `h1`.

Take `⟨hz, hzc⟩` from `(hmem _).1 hzU`. Use `⟨Spec.map ρ ≫ hU.fromSpec, hz, ?_, hzc⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, ← Spec.map_comp, hρ]`. Conclude with `spec_germ_fromSpec zC hU hp`.
-/
theorem exists_of_goodChart {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type} {x : κ → Ω}
    (hT : CoordTie ℤ ξ x) {C : Type} [Field C] (V : ValuationSubring C)
    (zC : Spec (CommRingCat.of C) ⟶ X) (h : genPt ξ ⤳ centre zC) {c : κ}
    (hg : GoodChart V ξ x zC h c) :
    ∃ (z : Spec (CommRingCat.of V) ⟶ X) (hz : genPt ξ ⤳ centre z),
      Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z = zC ∧ InChart ξ x c ⟨centre z, hz⟩ := by
  obtain ⟨hc, hj⟩ := hg
  obtain ⟨U, hU, hmem⟩ := hT.affine c hc
  have hch : InChart ξ x c ⟨centre zC, h⟩ := ⟨hc, fun j => by
    obtain ⟨s, hs, -⟩ := hj j
    rw [← hs]
    exact mem_regAt_of_gm s⟩
  have hp : centre zC ∈ U := (hmem _).2 ⟨h, hch⟩
  have hadj : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c),
      ∃ s : X.presheaf.stalk (centre zC), gm ξ h s = a ∧ val zC s ∈ V := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨j, rfl⟩ := ha
      exact hj j
    | algebraMap n =>
      refine ⟨(n : X.presheaf.stalk (centre zC)), by simp, ?_⟩
      rw [map_intCast]
      exact intCast_mem V n
    | add a b _ _ iha ihb =>
      obtain ⟨s, hs, hsV⟩ := iha
      obtain ⟨t, ht, htV⟩ := ihb
      exact ⟨s + t, by rw [map_add, hs, ht], by rw [map_add]; exact add_mem hsV htV⟩
    | mul a b _ _ iha ihb =>
      obtain ⟨s, hs, hsV⟩ := iha
      obtain ⟨t, ht, htV⟩ := ihb
      exact ⟨s * t, by rw [map_mul, hs, ht], by rw [map_mul]; exact mul_mem hsV htV⟩
  let ψ : Γ(X, U) ⟶ CommRingCat.of C := X.presheaf.germ U (centre zC) hp ≫ valC zC
  have hψ : ∀ g, ψ.hom g ∈ V := by
    intro g
    have hreg : gm ξ h ((X.presheaf.germ U (centre zC) hp).hom g) ∈
        Algebra.adjoin ℤ (Set.range fun j => x j / x c) := by
      refine (hT.ring c hc _).2 fun p hpc => ?_
      have hpU : p.1 ∈ U := (hmem _).2 ⟨p.2, hpc⟩
      rw [gm_germ ξ h p.2 hp hpU g]
      exact mem_regAt_of_gm _
    obtain ⟨s, hs, hsV⟩ := hadj _ hreg
    have := gm_inj hT.gen h hs
    rw [this] at hsV
    exact hsV
  let ρ : Γ(X, U) ⟶ CommRingCat.of V := CommRingCat.ofHom (ψ.hom.codRestrict V hψ)
  have hρ : ρ ≫ CommRingCat.ofHom (algebraMap V C) = ψ := by
    ext g
    rfl
  have hzU : centre (Spec.map ρ ≫ hU.fromSpec) ∈ U := by
    have h1 : centre (Spec.map ρ ≫ hU.fromSpec) ∈ Set.range hU.fromSpec :=
      ⟨Spec.map ρ (IsLocalRing.closedPoint V), rfl⟩
    rw [hU.range_fromSpec] at h1
    exact h1
  obtain ⟨hz, hzc⟩ := (hmem _).1 hzU
  refine ⟨Spec.map ρ ≫ hU.fromSpec, hz, ?_, hzc⟩
  rw [← Category.assoc, ← Spec.map_comp, hρ]
  exact spec_germ_fromSpec zC hU hp

/- English proof (translation)
Establish `w : centre (Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z) ⤳ centre z` using `(IsLocalRing.specializes_closedPoint (R := V) _).map z.continuous`. Take `⟨c', hc', hreg⟩` from `hT.cover ⟨centre z, hz⟩`. Take `⟨hc, hj⟩` from `hg`. Take `⟨t, ht⟩` from `exists_gm (hreg c)`. Take `⟨u, hu, huV⟩` from `hj c'`.

Establish `ht'` using `gm_specializes ξ h hz w t`. Rewrite `ht'` using `[ht]`. Establish `hmul : (X.presheaf.stalkSpecializes w).hom t * u = 1`. Apply `gm_inj hT.gen h` to reduce the goal to its premises. Rewrite using `[map_mul, map_one, ht', hu]`.

Clear the denominators using the available nonvanishing facts. Establish `hv` using `val_specializes (CommRingCat.ofHom (algebraMap V C)) z w t`. Establish `hvu : val z t * ⟨_, huV⟩ = 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use `congrArg (val (Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z)) hmul` as an intermediate fact.

Rewrite `this` using `[map_mul, map_one, hv]`. Conclude with `this`. Establish `hunit : IsUnit t` using `isUnit_of_map_unit (val z) _ (IsUnit.of_mul_eq_one _ hvu)`. Take `⟨e, rfl⟩` from `hunit`. Use `⟨hc, fun j => ?_⟩` and prove the remaining obligations.

Take `⟨b, hb⟩` from `exists_gm (hreg j)`. Establish `h1 : gm ξ hz (↑e⁻¹ : X.presheaf.stalk (centre z)) * (x c / x c') = 1`. Rewrite using `[← ht, ← map_mul, Units.inv_mul, map_one]`. Establish `h2 : gm ξ hz (↑e⁻¹ : X.presheaf.stalk (centre z)) = x c' / x c`. Clear denominators, using `at h1 ⊢` for the nonvanishing conditions.

Conclude with `h1`. Establish `h3 : x j / x c = gm ξ hz (b * (↑e⁻¹ : X.presheaf.stalk (centre z)))`. Rewrite using `[map_mul, hb, h2]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[h3]`.

Conclude with `mem_regAt_of_gm _`.
-/
theorem inChart_of_goodChart {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type} {x : κ → Ω}
    (hT : CoordTie ℤ ξ x) {C : Type} [Field C] (V : ValuationSubring C)
    (z : Spec (CommRingCat.of V) ⟶ X) (hz : genPt ξ ⤳ centre z)
    (h : genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z)) {c : κ}
    (hg : GoodChart V ξ x (Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z) h c) :
    InChart ξ x c ⟨centre z, hz⟩ := by
  have w : centre (Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z) ⤳ centre z :=
    (IsLocalRing.specializes_closedPoint (R := V) _).map z.continuous
  obtain ⟨c', hc', hreg⟩ := hT.cover ⟨centre z, hz⟩
  obtain ⟨hc, hj⟩ := hg
  obtain ⟨t, ht⟩ := exists_gm (hreg c)
  obtain ⟨u, hu, huV⟩ := hj c'
  have ht' := gm_specializes ξ h hz w t
  rw [ht] at ht'
  have hmul : (X.presheaf.stalkSpecializes w).hom t * u = 1 := by
    apply gm_inj hT.gen h
    rw [map_mul, map_one, ht', hu]
    field_simp
  have hv := val_specializes (CommRingCat.ofHom (algebraMap V C)) z w t
  have hvu : val z t * ⟨_, huV⟩ = 1 := by
    apply Subtype.ext
    have := congrArg (val (Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z)) hmul
    rw [map_mul, map_one, hv] at this
    exact this
  have hunit : IsUnit t := isUnit_of_map_unit (val z) _ (IsUnit.of_mul_eq_one _ hvu)
  obtain ⟨e, rfl⟩ := hunit
  refine ⟨hc, fun j => ?_⟩
  obtain ⟨b, hb⟩ := exists_gm (hreg j)
  have h1 : gm ξ hz (↑e⁻¹ : X.presheaf.stalk (centre z)) * (x c / x c') = 1 := by
    rw [← ht, ← map_mul, Units.inv_mul, map_one]
  have h2 : gm ξ hz (↑e⁻¹ : X.presheaf.stalk (centre z)) = x c' / x c := by
    field_simp at h1 ⊢
    exact h1
  have h3 : x j / x c = gm ξ hz (b * (↑e⁻¹ : X.presheaf.stalk (centre z))) := by
    rw [map_mul, hb, h2]
    field_simp
  rw [h3]
  exact mem_regAt_of_gm _

/- English proof (translation)
Take `⟨φ₁, e₁⟩ : ∃ φ, Spec.map φ ≫ hU.fromSpec = z₁` from `⟨_, spec_germ_fromSpec z₁ hU h₁⟩`. Take `⟨φ₂, e₂⟩ : ∃ φ, Spec.map φ ≫ hU.fromSpec = z₂` from `⟨_, spec_germ_fromSpec z₂ hU h₂⟩`. Substitute `e₁ e₂` using the available equality. Rewrite `e` using `[← Category.assoc, ← Category.assoc, cancel_mono, ← Spec.map_comp, ← Spec.map_comp]`. Establish `e'` using `Spec.map_injective e`.

Establish `: φ₁ = φ₂`. Use extensionality with `g`. Conclude with `congrArg (fun m => m.hom g) e'`. Rewrite using `[this]`.
-/
theorem eq_of_mem_affine {C : Type} [Field C] (V : ValuationSubring C)
    (z₁ z₂ : Spec (CommRingCat.of V) ⟶ X) {U : X.Opens} (hU : IsAffineOpen U)
    (h₁ : centre z₁ ∈ U) (h₂ : centre z₂ ∈ U)
    (e : Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z₁ =
      Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z₂) : z₁ = z₂ := by
  obtain ⟨φ₁, e₁⟩ : ∃ φ, Spec.map φ ≫ hU.fromSpec = z₁ := ⟨_, spec_germ_fromSpec z₁ hU h₁⟩
  obtain ⟨φ₂, e₂⟩ : ∃ φ, Spec.map φ ≫ hU.fromSpec = z₂ := ⟨_, spec_germ_fromSpec z₂ hU h₂⟩
  subst e₁ e₂
  rw [← Category.assoc, ← Category.assoc, cancel_mono, ← Spec.map_comp, ← Spec.map_comp] at e
  have e' := Spec.map_injective e
  have : φ₁ = φ₂ := by
    ext g
    exact congrArg (fun m => m.hom g) e'
  rw [this]

end CoordExtend

open CoordExtend in

/- English proof (translation)
Introduce `X Ω _ ξ κ _ x hT C _ V zC h`. Take `⟨c, hg⟩` from `exists_goodChart hT V zC h`. Take `⟨z, hz, hzC, hch⟩` from `exists_of_goodChart hT V zC h hg`. Use `⟨z, ⟨hz, hzC⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `y ⟨hy, hyC⟩`.

Take `⟨U, hU, hmem⟩` from `hT.affine c hg.1`. Establish `hych : InChart ξ x c ⟨centre y, hy⟩`. Substitute `hyC` using the available equality. Conclude with `inChart_of_goodChart hT V y hy h hg`. Conclude with `eq_of_mem_affine V y z hU ((hmem _).2 ⟨hy, hych⟩) ((hmem _).2 ⟨hz, hch⟩) (hyC.trans hzC.symm)`.
-/
theorem coord_point_extends : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (κ : Type) [Finite κ] (x : κ → Ω), CoordTie ℤ ξ x →
    ∀ (C : Type) [Field C] (V : ValuationSubring C) (zC : Spec (CommRingCat.of C) ⟶ X),
    genPt ξ ⤳ centre zC →
    ∃! z : Spec (CommRingCat.of V) ⟶ X, genPt ξ ⤳ centre z ∧
      Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z = zC := by
  intro X Ω _ ξ κ _ x hT C _ V zC h
  obtain ⟨c, hg⟩ := exists_goodChart hT V zC h
  obtain ⟨z, hz, hzC, hch⟩ := exists_of_goodChart hT V zC h hg
  refine ⟨z, ⟨hz, hzC⟩, ?_⟩
  rintro y ⟨hy, hyC⟩
  obtain ⟨U, hU, hmem⟩ := hT.affine c hg.1
  have hych : InChart ξ x c ⟨centre y, hy⟩ := by
    subst hyC
    exact inChart_of_goodChart hT V y hy h hg
  exact eq_of_mem_affine V y z hU ((hmem _).2 ⟨hy, hych⟩) ((hmem _).2 ⟨hz, hch⟩) (hyC.trans hzC.symm)

end GlobalTheory.CompanionTheory.Ar
