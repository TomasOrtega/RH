import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {R : Type} [CommRing R] [IsLocalRing R]

/- English proof (translation)
Take `⟨h, t, rfl, rfl⟩` from `ha`. Take `⟨_, u, rfl, rfl⟩` from `hb`. Conclude with `⟨h, t * u, map_mul _ _ _, map_mul _ _ _⟩`.
-/
theorem valAt_mul {ξ : Sp Ω ⟶ X} {z : Sp R ⟶ X} {a b : Ω} {r s : R}
    (ha : ValAt ξ z a r) (hb : ValAt ξ z b s) : ValAt ξ z (a * b) (r * s) := by
  obtain ⟨h, t, rfl, rfl⟩ := ha
  obtain ⟨_, u, rfl, rfl⟩ := hb
  exact ⟨h, t * u, map_mul _ _ _, map_mul _ _ _⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨h, 1, map_one _, map_one _⟩`.
-/
theorem valAt_one {ξ : Sp Ω ⟶ X} {z : Sp R ⟶ X} (h : genPt ξ ⤳ centre z) : ValAt ξ z 1 1 :=
  ⟨h, 1, map_one _, map_one _⟩

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simpa using valAt_one h`. Consider the case `insert k S hk ih`. Rewrite using `[Finset.prod_insert hk, Finset.prod_insert hk]`. Conclude with `valAt_mul (ha k) ih`.
-/
theorem valAt_prod {ξ : Sp Ω ⟶ X} {z : Sp R ⟶ X} (h : genPt ξ ⤳ centre z) {K : Type} (S : Finset K)
    (a : K → Ω) (r : K → R) (ha : ∀ k, ValAt ξ z (a k) (r k)) :
    ValAt ξ z (∏ k ∈ S, a k) (∏ k ∈ S, r k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using valAt_one h
  | insert k S hk ih =>
    rw [Finset.prod_insert hk, Finset.prod_insert hk]
    exact valAt_mul (ha k) ih

/- English proof (translation)
Take `⟨_, s, rfl, rfl⟩` from `ha`. Take `⟨u, rfl⟩ : IsUnit s` from `(Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit s hr`. Use `⟨(u⁻¹ : (X.presheaf.stalk (centre z))ˣ).1, eq_inv_of_mul_eq_one_left ?_⟩` and prove the remaining obligations. Rewrite using `[← map_mul, Units.inv_mul, map_one]`.
-/
theorem inv_mem_regAt_of_isUnit {ξ : Sp Ω ⟶ X} {z : Sp R ⟶ X} (h : genPt ξ ⤳ centre z) {a : Ω} {r : R}
    (ha : ValAt ξ z a r) (hr : IsUnit r) : a⁻¹ ∈ regAt ξ ⟨centre z, h⟩ := by
  obtain ⟨_, s, rfl, rfl⟩ := ha
  obtain ⟨u, rfl⟩ : IsUnit s := (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit s hr
  refine ⟨(u⁻¹ : (X.presheaf.stalk (centre z))ˣ).1, eq_inv_of_mul_eq_one_left ?_⟩
  rw [← map_mul, Units.inv_mul, map_one]

/- English proof (translation)
Introduce `X Ω _ ξ K _ J _ y L _ _ w v A _ _ _ zA hq hT hle hun hC`. Establish `hmax : ∀ k, ∃ c : J k, w ⟨k, c⟩ ≠ 0 ∧ ∀ i, v (w ⟨k, i⟩) ≤ v (w ⟨k, c⟩)`. Introduce `k`. Take `⟨u, hu⟩` from `hC.1 k`. Use `haveI : Nonempty (J k) := ⟨u⟩`.

Take `⟨c, hc⟩` from `Finite.exists_max (fun i => v (w ⟨k, i⟩))`. Use `⟨c, ?_, hc⟩` and prove the remaining obligations. Establish `h0 : 0 < v (w ⟨k, u⟩)` using `FinitePlace.pos_iff.2 hu.ne_zero`. Conclude with `FinitePlace.pos_iff.1 (h0.trans_le (hc u))`. Use `choose c hc0 hcm using hmax`.

Establish `h` using `hq (centre zA)`. Use `⟨c, h, hc0, hcm, ?_⟩` and prove the remaining obligations. Use `set x : ((k : K) → J k) → Ω := fun c' => ∏ k, y ⟨k, c' k⟩ with hx`. Use `set zL : Sp L ⟶ X := spMap (algebraMap A L) ≫ zA with hzL`. Establish `hy : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k => (hC.2 k (c k) (isUnit_iff_ne_zero.2 (hc0 k))).1`.

Establish `hxc : x c ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => hy k`. Take `⟨c', hc', hreg⟩` from `hT.cover ⟨centre zA, h⟩`. Take `⟨s, hs⟩` from `hreg c`. Use `set r : A := (Scheme.stalkClosedPointTo zA).hom s with hr`. Establish `hvA : ValAt ξ zA (x c / x c') r` using `⟨h, s, hs, rfl⟩`.

Establish `hvL : ValAt ξ zL (x c / x c') (algebraMap A L r)` using `LieTangent.valAt_base hT.gen _ hvA`. Establish `hL : genPt ξ ⤳ centre zL` using `hq _`. Establish `hk : ∀ k, ∃ ρ : L, ValAt ξ zL (y ⟨k, c' k⟩ / y ⟨k, c k⟩) ρ ∧ w ⟨k, c' k⟩ = ρ * w ⟨k, c k⟩` using `fun k => (hC.2 k (c k) (isUnit_iff_ne_zero.2 (hc0 k))).2 (c' k)`. Use `choose ρ hρ hρw using hk`. Establish `hprod : ValAt ξ zL (x c' / x c) (∏ k, ρ k)`.

Establish `e : x c' / x c = ∏ k, y ⟨k, c' k⟩ / y ⟨k, c k⟩` using `(Finset.prod_div_distrib _ _).symm`. Rewrite using `[e]`. Conclude with `valAt_prod hL _ _ _ fun k => hρ k`. Establish `hone : algebraMap A L r * ∏ k, ρ k = 1`. Establish `e : x c / x c' * (x c' / x c) = 1` using `by field_simp`.

Use `valAt_mul hvL hprod` as an intermediate fact. Rewrite `this` using `[e]`. Conclude with `LieTangent.valAt_unique hT.gen this (valAt_one hL)`. Establish `hρ1 : ∀ k, v (ρ k) ≤ 1`. Introduce `k`.

Establish `e` using `congrArg v (hρw k)`. Rewrite `e` using `[map_mul]`. Establish `hp : 0 < v (w ⟨k, c k⟩)` using `FinitePlace.pos_iff.2 (hc0 k)`. Use `hcm k (c' k)` as an intermediate fact. Rewrite `this` using `[e]`.

Conclude with `le_of_mul_le_mul_right (by simpa using this) hp`. Establish `hP : v (∏ k, ρ k) ≤ 1`. Rewrite using `[map_prod]`. Conclude with `Finset.prod_le_one (fun _ _ => by positivity) fun k _ => hρ1 k`. Establish `hsize : v (algebraMap A L r) = 1`.

Establish `e` using `congrArg v hone`. Rewrite `e` using `[map_mul, map_one]`. Use `le_antisymm (hle r) ?_` and prove the remaining obligations. Establish `h0 : 0 ≤ v (algebraMap A L r)` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hinv : (x c / x c')⁻¹ ∈ regAt ξ ⟨centre zA, h⟩` using `inv_mem_regAt_of_isUnit h hvA (hun r hsize)`. Use `⟨hxc, fun d => ?_⟩` and prove the remaining obligations. Establish `e : x d / x c = x d / x c' * (x c / x c')⁻¹` using `by field_simp`. Rewrite using `[e]`. Conclude with `mul_mem (hreg d) hinv`.
-/
theorem bestChart_finite : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L)
    (v : FinitePlace L) (A : Type) [CommRing A] [IsLocalRing A] [Algebra A L] (zA : Sp A ⟶ X),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) →
    (∀ r : A, v (algebraMap A L r) ≤ 1) → (∀ r : A, v (algebraMap A L r) = 1 → IsUnit r) →
    CoordsAt ξ y (spMap (algebraMap A L) ≫ zA) w →
    ∃ (c : (k : K) → J k) (h : genPt ξ ⤳ centre zA), (∀ k, w ⟨k, c k⟩ ≠ 0) ∧
      (∀ k i, v (w ⟨k, i⟩) ≤ v (w ⟨k, c k⟩)) ∧
      InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c ⟨centre zA, h⟩ := by
  intro X Ω _ ξ K _ J _ y L _ _ w v A _ _ _ zA hq hT hle hun hC

  have hmax : ∀ k, ∃ c : J k, w ⟨k, c⟩ ≠ 0 ∧ ∀ i, v (w ⟨k, i⟩) ≤ v (w ⟨k, c⟩) := by
    intro k
    obtain ⟨u, hu⟩ := hC.1 k
    haveI : Nonempty (J k) := ⟨u⟩
    obtain ⟨c, hc⟩ := Finite.exists_max (fun i => v (w ⟨k, i⟩))
    refine ⟨c, ?_, hc⟩
    have h0 : 0 < v (w ⟨k, u⟩) := FinitePlace.pos_iff.2 hu.ne_zero
    exact FinitePlace.pos_iff.1 (h0.trans_le (hc u))
  choose c hc0 hcm using hmax
  have h := hq (centre zA)
  refine ⟨c, h, hc0, hcm, ?_⟩
  set x : ((k : K) → J k) → Ω := fun c' => ∏ k, y ⟨k, c' k⟩ with hx
  set zL : Sp L ⟶ X := spMap (algebraMap A L) ≫ zA with hzL
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hC.2 k (c k) (isUnit_iff_ne_zero.2 (hc0 k))).1
  have hxc : x c ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hy k

  obtain ⟨c', hc', hreg⟩ := hT.cover ⟨centre zA, h⟩

  obtain ⟨s, hs⟩ := hreg c
  set r : A := (Scheme.stalkClosedPointTo zA).hom s with hr
  have hvA : ValAt ξ zA (x c / x c') r := ⟨h, s, hs, rfl⟩
  have hvL : ValAt ξ zL (x c / x c') (algebraMap A L r) := LieTangent.valAt_base hT.gen _ hvA

  have hL : genPt ξ ⤳ centre zL := hq _
  have hk : ∀ k, ∃ ρ : L, ValAt ξ zL (y ⟨k, c' k⟩ / y ⟨k, c k⟩) ρ ∧ w ⟨k, c' k⟩ = ρ * w ⟨k, c k⟩ :=
    fun k => (hC.2 k (c k) (isUnit_iff_ne_zero.2 (hc0 k))).2 (c' k)
  choose ρ hρ hρw using hk
  have hprod : ValAt ξ zL (x c' / x c) (∏ k, ρ k) := by
    have e : x c' / x c = ∏ k, y ⟨k, c' k⟩ / y ⟨k, c k⟩ := (Finset.prod_div_distrib _ _).symm
    rw [e]
    exact valAt_prod hL _ _ _ fun k => hρ k
  have hone : algebraMap A L r * ∏ k, ρ k = 1 := by
    have e : x c / x c' * (x c' / x c) = 1 := by field_simp
    have := valAt_mul hvL hprod
    rw [e] at this
    exact LieTangent.valAt_unique hT.gen this (valAt_one hL)

  have hρ1 : ∀ k, v (ρ k) ≤ 1 := by
    intro k
    have e := congrArg v (hρw k)
    rw [map_mul] at e
    have hp : 0 < v (w ⟨k, c k⟩) := FinitePlace.pos_iff.2 (hc0 k)
    have := hcm k (c' k)
    rw [e] at this
    exact le_of_mul_le_mul_right (by simpa using this) hp
  have hP : v (∏ k, ρ k) ≤ 1 := by
    rw [map_prod]
    exact Finset.prod_le_one (fun _ _ => by positivity) fun k _ => hρ1 k
  have hsize : v (algebraMap A L r) = 1 := by
    have e := congrArg v hone
    rw [map_mul, map_one] at e
    refine le_antisymm (hle r) ?_
    have h0 : 0 ≤ v (algebraMap A L r) := by positivity
    nlinarith
  have hinv : (x c / x c')⁻¹ ∈ regAt ξ ⟨centre zA, h⟩ :=
    inv_mem_regAt_of_isUnit h hvA (hun r hsize)
  refine ⟨hxc, fun d => ?_⟩
  have e : x d / x c = x d / x c' * (x c / x c')⁻¹ := by field_simp
  rw [e]
  exact mul_mem (hreg d) hinv

end GlobalTheory.CompanionTheory.Ar.RootHt
