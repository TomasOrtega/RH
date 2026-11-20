import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AddJFintype
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsVBOneOfChartGenerators
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagStep.CoordsRestrict

variable {X X' : Scheme.{0}} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω]

/- English proof (translation)
Take `⟨hA, s₁, hs₁, hr⟩` from `h₁`. Take `⟨hB, s₂, hs₂, ht⟩` from `h₂`. Establish `e : s₁ = s₂` using `hg.inj ⟨centre z, hA⟩ (hs₁.trans hs₂.symm)`. Rewrite using `[← hr, ← ht, e]`.
-/
theorem valAt_unique {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} (hg : IsCptGen ξ')
    {z : Spec (CommRingCat.of ℂ) ⟶ X'} {a : Ω} {r t : ℂ} (h₁ : ValAt ξ' z a r) (h₂ : ValAt ξ' z a t) :
    r = t := by
  obtain ⟨hA, s₁, hs₁, hr⟩ := h₁
  obtain ⟨hB, s₂, hs₂, ht⟩ := h₂
  have e : s₁ = s₂ := hg.inj ⟨centre z, hA⟩ (hs₁.trans hs₂.symm)
  rw [← hr, ← ht, e]

/- English proof (translation)
Take `⟨hA, s₁, hs₁, hr⟩` from `h₁`. Take `⟨hB, s₂, hs₂, ht⟩` from `h₂`. Conclude with `⟨hA, s₁ * s₂, by rw [map_mul, hs₁, hs₂], (map_mul _ s₁ s₂).trans (congrArg₂ (· * ·) hr ht)⟩`.
-/
theorem valAt_mul {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} {z : Spec (CommRingCat.of ℂ) ⟶ X'} {a b : Ω}
    {r t : ℂ} (h₁ : ValAt ξ' z a r) (h₂ : ValAt ξ' z b t) : ValAt ξ' z (a * b) (r * t) := by
  obtain ⟨hA, s₁, hs₁, hr⟩ := h₁
  obtain ⟨hB, s₂, hs₂, ht⟩ := h₂
  exact ⟨hA, s₁ * s₂, by rw [map_mul, hs₁, hs₂],
    (map_mul _ s₁ s₂).trans (congrArg₂ (· * ·) hr ht)⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨h, 1, map_one _, map_one _⟩`.
-/
theorem valAt_one {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} {z : Spec (CommRingCat.of ℂ) ⟶ X'}
    (h : genPt ξ' ⤳ centre z) : ValAt ξ' z (1 : Ω) 1 :=
  ⟨h, 1, map_one _, map_one _⟩

/- English proof (translation)
Conclude with `IsUnit.of_map φ s (Ne.isUnit h)`.
-/
theorem isUnit_of_local {A : Type*} [CommRing A] (φ : A →+* ℂ) [IsLocalHom φ] (s : A) (h : φ s ≠ 0) :
    IsUnit s := by
  exact IsUnit.of_map φ s (Ne.isUnit h)

/- English proof (translation)
Take `⟨h, s, hs, hr'⟩` from `hv`. Establish `hu : IsUnit s` using `isUnit_of_local (Scheme.stalkClosedPointTo z).hom s (by rw [hr']; exact hr)`. Take `⟨u, rfl⟩` from `hu`. Establish `hinv : genMap ξ' ⟨centre z, h'⟩ ↑u⁻¹ * genMap ξ' ⟨centre z, h'⟩ ↑u = 1`. Rewrite using `[← map_mul, Units.inv_mul, map_one]`.

Establish `hne : genMap ξ' ⟨centre z, h'⟩ ↑u ≠ 0` using `fun h0 => by`. Rewrite `hinv` using `[h0, mul_zero]`. Conclude with `zero_ne_one hinv`. Use `⟨?_, ⟨↑u, hs⟩, ⟨↑u⁻¹, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← hs]`.

Conclude with `hne`. Rewrite using `[← hs]`. Conclude with `eq_inv_of_mul_eq_one_left hinv`.
-/
theorem unitAt_of_valAt {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} {z : Spec (CommRingCat.of ℂ) ⟶ X'}
    (h' : genPt ξ' ⤳ centre z) {a : Ω} {r : ℂ} (hr : r ≠ 0) (hv : ValAt ξ' z a r) :
    unitAt ξ' ⟨centre z, h'⟩ a := by
  obtain ⟨h, s, hs, hr'⟩ := hv
  have hu : IsUnit s := isUnit_of_local (Scheme.stalkClosedPointTo z).hom s (by rw [hr']; exact hr)
  obtain ⟨u, rfl⟩ := hu
  have hinv : genMap ξ' ⟨centre z, h'⟩ ↑u⁻¹ * genMap ξ' ⟨centre z, h'⟩ ↑u = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hne : genMap ξ' ⟨centre z, h'⟩ ↑u ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hinv
    exact zero_ne_one hinv
  refine ⟨?_, ⟨↑u, hs⟩, ⟨↑u⁻¹, ?_⟩⟩
  · rw [← hs]; exact hne
  · rw [← hs]; exact eq_inv_of_mul_eq_one_left hinv

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
private theorem stalkSpecializes_comp_stalkClosedPointTo_congr {K : Type} [Field K] (g₁ g₂ : Spec (CommRingCat.of K) ⟶ X)
    (e : g₁ = g₂) {q : X} (h₁ : g₁ (IsLocalRing.closedPoint K) ⤳ q) (h₂ : g₂ (IsLocalRing.closedPoint K) ⤳ q) :
    X.presheaf.stalkSpecializes h₁ ≫ Scheme.stalkClosedPointTo g₁ =
      X.presheaf.stalkSpecializes h₂ ≫ Scheme.stalkClosedPointTo g₂ := by
  subst e; rfl

/- English proof (translation)
Use `TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_` and prove the remaining obligations. Rewrite using `[TopCat.Presheaf.germ_stalkSpecializes_assoc, TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.germ_stalkClosedPointTo, Scheme.germ_stalkClosedPointTo_assoc]`. Simplify using `only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, Category.assoc]`. Rewrite using `[← Scheme.ΓSpecIso_naturality]`. Simplify using `only [← Category.assoc]`.

Use `congr 1`.
-/
private theorem stalkSpecializes_comp_stalkClosedPointTo_specMap_comp {K K' : Type} [Field K] [Field K'] (i : K →+* K')
    (g : Spec (CommRingCat.of K) ⟶ X) {q : X}
    (h₂ : (Spec.map (CommRingCat.ofHom i) ≫ g) (IsLocalRing.closedPoint K') ⤳ q)
    (hp : g (IsLocalRing.closedPoint K) ⤳ q) :
    X.presheaf.stalkSpecializes h₂ ≫ Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom i) ≫ g) =
      X.presheaf.stalkSpecializes hp ≫ Scheme.stalkClosedPointTo g ≫ CommRingCat.ofHom i := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
  rw [TopCat.Presheaf.germ_stalkSpecializes_assoc, TopCat.Presheaf.germ_stalkSpecializes_assoc,
    Scheme.germ_stalkClosedPointTo, Scheme.germ_stalkClosedPointTo_assoc]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, Category.assoc]
  rw [← Scheme.ΓSpecIso_naturality]
  simp only [← Category.assoc]
  congr 1

/- English proof (translation)
Take `⟨s, hs⟩` from `RingHom.mem_range.1 ha`. Use `⟨(Scheme.stalkClosedPointTo (z ≫ f)).hom s, ⟨hp, s, hs, rfl⟩, h', (f.stalkMap (centre z)).hom s, ?_, ?_⟩` and prove the remaining obligations. Establish `h₁ : (ξ' ≫ f) (IsLocalRing.closedPoint Ω) ⤳ f (centre z)` using `f.base.hom.map_specializes h'`. Establish `h₂ : (Spec.map (CommRingCat.ofHom i) ≫ ξ) (IsLocalRing.closedPoint Ω) ⤳ f (centre z)`. Rewrite using `[← hd]`.

Conclude with `h₁`. Establish `h'' : ξ' (IsLocalRing.closedPoint Ω) ⤳ centre z` using `h'`. Establish `hp'' : ξ (IsLocalRing.closedPoint Ω₀) ⤳ f (centre z)` using `hp`. Establish `key : f.stalkMap (centre z) ≫ X'.presheaf.stalkSpecializes h'' ≫ Scheme.stalkClosedPointTo ξ' = X.presheaf.stalkSpecializes hp'' ≫ Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i`. Rewrite using `[← Category.assoc, ← Scheme.Hom.stalkSpecializes_stalkMap, Category.assoc, ← Scheme.stalkClosedPointTo_comp]`.

Conclude with `(stalkSpecializes_comp_stalkClosedPointTo_congr (ξ' ≫ f) (Spec.map (CommRingCat.ofHom i) ≫ ξ) hd h₁ h₂).trans (stalkSpecializes_comp_stalkClosedPointTo_specMap_comp i ξ h₂ hp'')`. Use `congrArg (fun φ => φ.hom s) key` as an intermediate fact. Rewrite using `[← hs]`. Conclude with `this`. Rewrite using `[Scheme.stalkClosedPointTo_comp]`.

Both sides reduce to the same expression.
-/
theorem valAt_of_regAt {ξ : Spec (CommRingCat.of Ω₀) ⟶ X} {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} {f : X' ⟶ X}
    {i : Ω₀ →+* Ω} (hd : Dominates ξ' ξ f i) (z : Spec (CommRingCat.of ℂ) ⟶ X')
    (h' : genPt ξ' ⤳ centre z) (hp : genPt ξ ⤳ f (centre z)) {a : Ω₀}
    (ha : a ∈ regAt ξ ⟨f (centre z), hp⟩) :
    ∃ r : ℂ, ValAt ξ (z ≫ f) a r ∧ ValAt ξ' z (i a) r := by
  obtain ⟨s, hs⟩ := RingHom.mem_range.1 ha
  refine ⟨(Scheme.stalkClosedPointTo (z ≫ f)).hom s, ⟨hp, s, hs, rfl⟩, h', (f.stalkMap (centre z)).hom s, ?_, ?_⟩
  · have h₁ : (ξ' ≫ f) (IsLocalRing.closedPoint Ω) ⤳ f (centre z) := f.base.hom.map_specializes h'
    have h₂ : (Spec.map (CommRingCat.ofHom i) ≫ ξ) (IsLocalRing.closedPoint Ω) ⤳ f (centre z) := by
      rw [← hd]; exact h₁
    have h'' : ξ' (IsLocalRing.closedPoint Ω) ⤳ centre z := h'
    have hp'' : ξ (IsLocalRing.closedPoint Ω₀) ⤳ f (centre z) := hp
    have key : f.stalkMap (centre z) ≫ X'.presheaf.stalkSpecializes h'' ≫ Scheme.stalkClosedPointTo ξ' =
        X.presheaf.stalkSpecializes hp'' ≫ Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i := by
      rw [← Category.assoc, ← Scheme.Hom.stalkSpecializes_stalkMap, Category.assoc,
        ← Scheme.stalkClosedPointTo_comp]
      exact (stalkSpecializes_comp_stalkClosedPointTo_congr (ξ' ≫ f) (Spec.map (CommRingCat.ofHom i) ≫ ξ) hd h₁ h₂).trans
        (stalkSpecializes_comp_stalkClosedPointTo_specMap_comp i ξ h₂ hp'')
    have := congrArg (fun φ => φ.hom s) key
    rw [← hs]
    exact this
  · rw [Scheme.stalkClosedPointTo_comp]
    rfl

/- English proof (translation)
Introduce `X X' Ω₀ Ω _ _ _ ξ ξ' f K _ J _ y N x' z w hgen htie hcpt hgen' hd hc`. Take `⟨hc1, hc2⟩` from `hc`. Use `⟨fun k => hc1 (Sum.inr k), fun k c hu => ?_⟩` and prove the remaining obligations. Establish `hyA : ∀ j : J k, addY y x' ⟨Sum.inr k, j⟩ = algebraMap Ω₀ Ω (y ⟨k, j⟩)` using `fun j => rfl`. Take `⟨hy, hv⟩` from `hc2 (Sum.inr k) c hu`.

Rewrite `hy` using `[hyA]`. Establish `hyc : y ⟨k, c⟩ ≠ 0` using `fun h0 => hy (by rw [h0, map_zero])`. Use `⟨hyc, fun j => ?_⟩` and prove the remaining obligations. Establish `hp : genPt ξ ⤳ f (centre z)` using `hgen _`. Establish `h' : genPt ξ' ⤳ centre z` using `hgen' _`.

Take `⟨c₀, hc₀ne, hc₀⟩` from `htie.cover ⟨f (centre z), hp⟩`. Establish `hx0 : (∏ k', y ⟨k', c₀ k'⟩) ≠ 0` using `hc₀ne`. Establish `hy0 : y ⟨k, c₀ k⟩ ≠ 0` using `fun h0 => hx0 (Finset.prod_eq_zero (Finset.mem_univ k) h0)`. Establish `hprod : ∀ j : J k, (∏ k', y ⟨k', Function.update c₀ k j k'⟩) * y ⟨k, c₀ k⟩ = (∏ k', y ⟨k', c₀ k'⟩) * y ⟨k, j⟩`. Introduce `j`.

Rewrite using `[← Finset.mul_prod_erase Finset.univ (fun k' => y ⟨k', Function.update c₀ k j k'⟩) (Finset.mem_univ k), ← Finset.mul_prod_erase Finset.univ (fun k' => y ⟨k', c₀ k'⟩) (Finset.mem_univ k)]`. Establish `e : ∏ x ∈ Finset.univ.erase k, y ⟨x, Function.update c₀ k j x⟩ = ∏ x ∈ Finset.univ.erase k, y ⟨x, c₀ x⟩` using `Finset.prod_congr rfl fun x hx => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]`. Simplify using `only [Function.update_self]`. Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hratio : ∀ j : J k, (∏ k', y ⟨k', Function.update c₀ k j k'⟩) / (∏ k', y ⟨k', c₀ k'⟩) = y ⟨k, j⟩ / y ⟨k, c₀ k⟩`. Introduce `j`. Rewrite using `[div_eq_div_iff hx0 hy0, hprod j, mul_comm]`. Establish `hreg : ∀ j : J k, y ⟨k, j⟩ / y ⟨k, c₀ k⟩ ∈ regAt ξ ⟨f (centre z), hp⟩` using `fun j => by`. Rewrite using `[← hratio j]`.

Conclude with `hc₀ (Function.update c₀ k j)`. Take `⟨r₂, hr₂a, hr₂b⟩` from `valAt_of_regAt hd z h' hp (hreg c)`. Take `⟨r₀, hr₀, -⟩` from `hv (c₀ k)`. Rewrite `hr₀` using `[hyA, hyA]`. Establish `hmul` using `valAt_mul hr₂b hr₀`.

Establish `hy0' : algebraMap Ω₀ Ω (y ⟨k, c₀ k⟩) ≠ 0` using `(map_ne_zero _).2 hy0`. Establish `hone : algebraMap Ω₀ Ω (y ⟨k, c⟩ / y ⟨k, c₀ k⟩) * (algebraMap Ω₀ Ω (y ⟨k, c₀ k⟩) / algebraMap Ω₀ Ω (y ⟨k, c⟩)) = 1`. Rewrite using `[map_div₀]`. Clear the denominators using the available nonvanishing facts. Rewrite `hmul` using `[hone]`.

Establish `h1 : r₂ * r₀ = 1` using `valAt_unique hcpt hmul (valAt_one h')`. Establish `hr₂ne : r₂ ≠ 0` using `left_ne_zero_of_mul_eq_one h1`. Establish `hunit` using `unitAt_of_valAt hp hr₂ne hr₂a`. Establish `hinvreg : (y ⟨k, c⟩ / y ⟨k, c₀ k⟩)⁻¹ ∈ regAt ξ ⟨f (centre z), hp⟩` using `hunit.2.2`. Establish `hregjc : y ⟨k, j⟩ / y ⟨k, c⟩ ∈ regAt ξ ⟨f (centre z), hp⟩`.

Establish `e : y ⟨k, j⟩ / y ⟨k, c⟩ = (y ⟨k, j⟩ / y ⟨k, c₀ k⟩) * (y ⟨k, c⟩ / y ⟨k, c₀ k⟩)⁻¹`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `Subring.mul_mem _ (hreg j) hinvreg`. Take `⟨r, hr1, hr2⟩` from `valAt_of_regAt hd z h' hp hregjc`.

Take `⟨r', hr', hw⟩` from `hv j`. Rewrite `hr'` using `[hyA, hyA]`. Rewrite `hr2` using `[map_div₀]`. Establish `e3 : r = r'` using `valAt_unique hcpt hr2 hr'`. Use `⟨r, hr1, ?_⟩` and prove the remaining obligations.

Rewrite using `[e3]`. Conclude with `hw`.
-/
theorem coordsAt_restrict : ∀ (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω]
    (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X)
    (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω₀) (N : ℕ) (x' : Fin (N + 1) → Ω)
    (z : Spec (CommRingCat.of ℂ) ⟶ X') (w : (Σ k, addJ J N k) → ℂ),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → IsCptGen ξ' →
    (∀ q : X', genPt ξ' ⤳ q) → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω₀ Ω) →
    CoordsAt ξ' (addY y x') z w → CoordsAt ξ y (z ≫ f) (fun p => w (addV J N p)) := by
  intro X X' Ω₀ Ω _ _ _ ξ ξ' f K _ J _ y N x' z w hgen htie hcpt hgen' hd hc
  classical
  obtain ⟨hc1, hc2⟩ := hc
  refine ⟨fun k => hc1 (Sum.inr k), fun k c hu => ?_⟩
  have hyA : ∀ j : J k, addY y x' ⟨Sum.inr k, j⟩ = algebraMap Ω₀ Ω (y ⟨k, j⟩) := fun j => rfl
  obtain ⟨hy, hv⟩ := hc2 (Sum.inr k) c hu
  rw [hyA] at hy
  have hyc : y ⟨k, c⟩ ≠ 0 := fun h0 => hy (by rw [h0, map_zero])
  refine ⟨hyc, fun j => ?_⟩
  have hp : genPt ξ ⤳ f (centre z) := hgen _
  have h' : genPt ξ' ⤳ centre z := hgen' _
  obtain ⟨c₀, hc₀ne, hc₀⟩ := htie.cover ⟨f (centre z), hp⟩
  have hx0 : (∏ k', y ⟨k', c₀ k'⟩) ≠ 0 := hc₀ne
  have hy0 : y ⟨k, c₀ k⟩ ≠ 0 := fun h0 => hx0 (Finset.prod_eq_zero (Finset.mem_univ k) h0)
  have hprod : ∀ j : J k, (∏ k', y ⟨k', Function.update c₀ k j k'⟩) * y ⟨k, c₀ k⟩ =
      (∏ k', y ⟨k', c₀ k'⟩) * y ⟨k, j⟩ := by
    intro j
    rw [← Finset.mul_prod_erase Finset.univ (fun k' => y ⟨k', Function.update c₀ k j k'⟩) (Finset.mem_univ k),
      ← Finset.mul_prod_erase Finset.univ (fun k' => y ⟨k', c₀ k'⟩) (Finset.mem_univ k)]
    have e : ∏ x ∈ Finset.univ.erase k, y ⟨x, Function.update c₀ k j x⟩ =
        ∏ x ∈ Finset.univ.erase k, y ⟨x, c₀ x⟩ :=
      Finset.prod_congr rfl fun x hx => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
    simp only [Function.update_self]
    rw [e]
    ring
  have hratio : ∀ j : J k, (∏ k', y ⟨k', Function.update c₀ k j k'⟩) / (∏ k', y ⟨k', c₀ k'⟩) =
      y ⟨k, j⟩ / y ⟨k, c₀ k⟩ := by
    intro j
    rw [div_eq_div_iff hx0 hy0, hprod j, mul_comm]
  have hreg : ∀ j : J k, y ⟨k, j⟩ / y ⟨k, c₀ k⟩ ∈ regAt ξ ⟨f (centre z), hp⟩ := fun j => by
    rw [← hratio j]
    exact hc₀ (Function.update c₀ k j)
  obtain ⟨r₂, hr₂a, hr₂b⟩ := valAt_of_regAt hd z h' hp (hreg c)
  obtain ⟨r₀, hr₀, -⟩ := hv (c₀ k)
  rw [hyA, hyA] at hr₀
  have hmul := valAt_mul hr₂b hr₀
  have hy0' : algebraMap Ω₀ Ω (y ⟨k, c₀ k⟩) ≠ 0 := (map_ne_zero _).2 hy0
  have hone : algebraMap Ω₀ Ω (y ⟨k, c⟩ / y ⟨k, c₀ k⟩) *
      (algebraMap Ω₀ Ω (y ⟨k, c₀ k⟩) / algebraMap Ω₀ Ω (y ⟨k, c⟩)) = 1 := by
    rw [map_div₀]
    field_simp
  rw [hone] at hmul
  have h1 : r₂ * r₀ = 1 := valAt_unique hcpt hmul (valAt_one h')
  have hr₂ne : r₂ ≠ 0 := left_ne_zero_of_mul_eq_one h1
  have hunit := unitAt_of_valAt hp hr₂ne hr₂a
  have hinvreg : (y ⟨k, c⟩ / y ⟨k, c₀ k⟩)⁻¹ ∈ regAt ξ ⟨f (centre z), hp⟩ := hunit.2.2
  have hregjc : y ⟨k, j⟩ / y ⟨k, c⟩ ∈ regAt ξ ⟨f (centre z), hp⟩ := by
    have e : y ⟨k, j⟩ / y ⟨k, c⟩ = (y ⟨k, j⟩ / y ⟨k, c₀ k⟩) * (y ⟨k, c⟩ / y ⟨k, c₀ k⟩)⁻¹ := by
      field_simp
    rw [e]
    exact Subring.mul_mem _ (hreg j) hinvreg
  obtain ⟨r, hr1, hr2⟩ := valAt_of_regAt hd z h' hp hregjc
  obtain ⟨r', hr', hw⟩ := hv j
  rw [hyA, hyA] at hr'
  rw [map_div₀] at hr2
  have e3 : r = r' := valAt_unique hcpt hr2 hr'
  refine ⟨r, hr1, ?_⟩
  rw [e3]
  exact hw

end GlobalTheory.CompanionTheory.Ar.FlagStep.CoordsRestrict
