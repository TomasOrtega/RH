import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemAbLocusIff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentresStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAtStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg.Ratio

open MvPolynomial

variable {K₀ K : Type} [Fintype K₀] [Fintype K] {J₀ : K₀ → Type} {J : K → Type} [∀ k, Fintype (J₀ k)]
  [∀ k, Fintype (J k)] {Ω Ω₀ : Type} [Field Ω] [Field Ω₀]

/- English proof (translation)
Establish `h1 : ∏ k, c k ^ pullDeg bk a₀ k = ∏ k ∈ Finset.univ.image bk, c k ^ pullDeg bk a₀ k`. Use `(Finset.prod_subset (Finset.subset_univ _) fun k _ hk => ?_).symm` and prove the remaining obligations. Establish `: ¬ ∃ x, bk x = k` using `fun ⟨x, hx⟩ => hk (Finset.mem_image.2 ⟨x, Finset.mem_univ _, hx⟩)`. Simplify using `[pullDeg, Function.extend_apply' _ _ _ this]`. Rewrite using `[h1, Finset.prod_image fun _ _ _ _ h => hbk h]`.

Conclude with `Finset.prod_congr rfl fun k _ => by simp [pullDeg, hbk.extend_apply]`.
-/
theorem prod_comp_zpow {G : Type} [CommGroupWithZero G] {bk : K₀ → K} (hbk : Function.Injective bk) (c : K → G)
    (a₀ : K₀ → ℤ) : ∏ k, c (bk k) ^ a₀ k = ∏ k, c k ^ pullDeg bk a₀ k := by
  classical
  have h1 : ∏ k, c k ^ pullDeg bk a₀ k = ∏ k ∈ Finset.univ.image bk, c k ^ pullDeg bk a₀ k := by
    refine (Finset.prod_subset (Finset.subset_univ _) fun k _ hk => ?_).symm
    have : ¬ ∃ x, bk x = k := fun ⟨x, hx⟩ => hk (Finset.mem_image.2 ⟨x, Finset.mem_univ _, hx⟩)
    simp [pullDeg, Function.extend_apply' _ _ _ this]
  rw [h1, Finset.prod_image fun _ _ _ _ h => hbk h]
  exact Finset.prod_congr rfl fun k _ => by simp [pullDeg, hbk.extend_apply]

def cmpFn (i : Ω₀ →+* Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀)
    (c : (k : K) → J k) (c₀ : (k : K₀) → J₀ k) : Ω :=
  i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀) / ((∏ k, y ⟨k, c k⟩ ^ a k) * e)

def cmpVal (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (a : K → ℤ) (a₀ : K₀ → ℤ) (w : (Σ k, J k) → ℂ)
    (c : (k : K) → J k) (c₀ : (k : K₀) → J₀ k) (u : ℂ) : ℂ :=
  u * (∏ k, w ⟨k, c k⟩ ^ a k) / ∏ k, w (blkV bk bx ⟨k, c₀ k⟩) ^ a₀ k

def IsCmp (i : Ω₀ →+* Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k))
    (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀) (w : (Σ k, J k) → ℂ) (t : ℂ) : Prop :=
  ∃ (c : (k : K) → J k) (c₀ : (k : K₀) → J₀ k) (u : ℂ), (∀ k, w ⟨k, c k⟩ ≠ 0) ∧
    (∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0) ∧ u ≠ 0 ∧
    GroundTheory.Heights₂.Heights.LowerBoundFree.IsValueAt y (cmpFn i y₀ y a a₀ e e₀ c c₀) w u ∧
    t = cmpVal bk bx a a₀ w c c₀ u

/- English proof (translation)
The claim follows from `div_ne_zero (mul_ne_zero hu (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (h1 k))) (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (h2 k))`.
-/
theorem cmpVal_ne_zero {bk : K₀ → K} {bx : ∀ k, J₀ k ≃ J (bk k)} {a : K → ℤ} {a₀ : K₀ → ℤ} {w : (Σ k, J k) → ℂ}
    {c : (k : K) → J k} {c₀ : (k : K₀) → J₀ k} {u : ℂ} (h1 : ∀ k, w ⟨k, c k⟩ ≠ 0)
    (h2 : ∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0) (hu : u ≠ 0) : cmpVal bk bx a a₀ w c c₀ u ≠ 0 :=
  div_ne_zero (mul_ne_zero hu (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (h1 k)))
    (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (h2 k))

section Val

variable {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {z : Spec (CommRingCat.of ℂ) ⟶ X}

/- English proof (translation)
Establish `hp : ∀ s : Finset I, ValAt ξ z (∏ k ∈ s, f k ^ n k) (∏ k ∈ s, r k ^ n k)`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using CxVal.one hz`. Consider the case `insert k s hk ih`.

Rewrite using `[Finset.prod_insert hk, Finset.prod_insert hk]`. Conclude with `CxVal.mul (CxVal.zpow (h k) (h0 k) _) ih`. Conclude with `hp Finset.univ`.
-/
theorem valAt_prod_zpow {I : Type} [Fintype I] {f : I → Ω} {r : I → ℂ} (hz : genPt ξ ⤳ centre z)
    (h : ∀ k, ValAt ξ z (f k) (r k)) (h0 : ∀ k, r k ≠ 0) (n : I → ℤ) :
    ValAt ξ z (∏ k, f k ^ n k) (∏ k, r k ^ n k) := by
  classical
  have hp : ∀ s : Finset I, ValAt ξ z (∏ k ∈ s, f k ^ n k) (∏ k ∈ s, r k ^ n k) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using CxVal.one hz
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.prod_insert hk]
      exact CxVal.mul (CxVal.zpow (h k) (h0 k) _) ih
  exact hp Finset.univ

/- English proof (translation)
Establish `hyc : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k => (hw.2 k (c k) (IsUnit.mk0 _ (h1 k))).1`. Establish `hyc' : ∀ k, y ⟨k, c' k⟩ ≠ 0` using `fun k => (hw.2 k (c' k) (IsUnit.mk0 _ (h1' k))).1`. Establish `hyv : ∀ k, y (blkV bk bx ⟨k, c₀ k⟩) ≠ 0` using `fun k => (hw.2 (bk k) (bx k (c₀ k)) (IsUnit.mk0 _ (h2 k))).1`. Establish `hyv' : ∀ k, y (blkV bk bx ⟨k, c₀' k⟩) ≠ 0` using `fun k => (hw.2 (bk k) (bx k (c₀' k)) (IsUnit.mk0 _ (h2' k))).1`. Use `choose r hr hr' using fun k => (hw.2 k (c' k) (IsUnit.mk0 _ (h1' k))).2 (c k)`.

Use `choose q hq hq' using fun k => (hw.2 (bk k) (bx k (c₀ k)) (IsUnit.mk0 _ (h2 k))).2 (bx k (c₀' k))`. Establish `hr0 : ∀ k, r k ≠ 0` using `fun k h => h1 k (by rw [hr', h, zero_mul])`. Establish `hq0 : ∀ k, q k ≠ 0` using `fun k h => h2' k (by show w ⟨bk k, bx k (c₀' k)⟩ = 0`. Rewrite using `[hq', h, zero_mul])`. Establish `e1` using `valAt_prod_zpow hz hr hr0 a`.

Establish `e2` using `valAt_prod_zpow hz hq hq0 a₀`. Establish `hM : ∀ c₁ : (k : K₀) → J₀ k, i (∏ k, y₀ ⟨k, c₁ k⟩ ^ a₀ k) = ∏ k, y (blkV bk bx ⟨k, c₁ k⟩) ^ a₀ k`. Introduce `c₁`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[map_zpow₀]`. Use `show _ = y ⟨bk k, bx k (c₁ k)⟩ ^ a₀ k`. Rewrite using `[hy]`. Establish `key : cmpFn i y₀ y a a₀ e e₀ c' c₀' = cmpFn i y₀ y a a₀ e e₀ c c₀ * (∏ k, (y ⟨bk k, bx k (c₀' k)⟩ / y ⟨bk k, bx k (c₀ k)⟩) ^ a₀ k) * ∏ k, (y ⟨k, c k⟩ / y ⟨k, c' k⟩) ^ a k`. Simplify using `only [cmpFn, map_mul, hM, div_zpow, Finset.prod_div_distrib]`.

Establish `n1 : (∏ k, y ⟨k, c k⟩ ^ a k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hyc k)`. Establish `n2 : (∏ k, y ⟨k, c' k⟩ ^ a k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hyc' k)`. Establish `n3 : (∏ k, y ⟨bk k, bx k (c₀ k)⟩ ^ a₀ k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hyv k)`. Establish `e3 : ∀ c₁ : (k : K₀) → J₀ k, (∏ k, y (blkV bk bx ⟨k, c₁ k⟩) ^ a₀ k) = ∏ k, y ⟨bk k, bx k (c₁ k)⟩ ^ a₀ k` using `fun _ => rfl`. Rewrite using `[e3, e3]`.

Distinguish the cases in `he : e = 0`. Simplify using `[he]`. Clear the denominators using the available nonvanishing facts. Establish `hu2` using `CxVal.unique hu' (key ▸ CxVal.mul (CxVal.mul hu e2) e1)`. Establish `w1 : (∏ k, w ⟨k, c k⟩ ^ a k) = (∏ k, r k ^ a k) * ∏ k, w ⟨k, c' k⟩ ^ a k`.

Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun k _ => by rw [hr' k, mul_zpow]`. Establish `w2 : (∏ k, w (blkV bk bx ⟨k, c₀' k⟩) ^ a₀ k) = (∏ k, q k ^ a₀ k) * ∏ k, w (blkV bk bx ⟨k, c₀ k⟩) ^ a₀ k`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations.

Use `show w ⟨bk k, bx k (c₀' k)⟩ ^ a₀ k = _`. Rewrite using `[hq' k, mul_zpow]`. Both sides reduce to the same expression. Establish `n4 : (∏ k, w (blkV bk bx ⟨k, c₀ k⟩) ^ a₀ k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (h2 k)`. Establish `n5 : (∏ k, q k ^ a₀ k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hq0 k)`.

Simplify using `only [cmpVal]`. Rewrite using `[w1, w2, hu2]`. Clear the denominators using the available nonvanishing facts.
-/
theorem cmpVal_eq {i : Ω₀ →+* Ω} {y₀ : (Σ k, J₀ k) → Ω₀} {y : (Σ k, J k) → Ω} {bk : K₀ → K}
    {bx : ∀ k, J₀ k ≃ J (bk k)} {a : K → ℤ} {a₀ : K₀ → ℤ} {e : Ω} {e₀ : Ω₀} {w : (Σ k, J k) → ℂ}
    (hy : ∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w)
    {c c' : (k : K) → J k} {c₀ c₀' : (k : K₀) → J₀ k} (h1 : ∀ k, w ⟨k, c k⟩ ≠ 0) (h1' : ∀ k, w ⟨k, c' k⟩ ≠ 0)
    (h2 : ∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0) (h2' : ∀ k, w (blkV bk bx ⟨k, c₀' k⟩) ≠ 0) {u u' : ℂ}
    (hu : ValAt ξ z (cmpFn i y₀ y a a₀ e e₀ c c₀) u) (hu' : ValAt ξ z (cmpFn i y₀ y a a₀ e e₀ c' c₀') u') :
    cmpVal bk bx a a₀ w c c₀ u = cmpVal bk bx a a₀ w c' c₀' u' := by
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hw.2 k (c k) (IsUnit.mk0 _ (h1 k))).1
  have hyc' : ∀ k, y ⟨k, c' k⟩ ≠ 0 := fun k => (hw.2 k (c' k) (IsUnit.mk0 _ (h1' k))).1
  have hyv : ∀ k, y (blkV bk bx ⟨k, c₀ k⟩) ≠ 0 := fun k => (hw.2 (bk k) (bx k (c₀ k)) (IsUnit.mk0 _ (h2 k))).1
  have hyv' : ∀ k, y (blkV bk bx ⟨k, c₀' k⟩) ≠ 0 := fun k => (hw.2 (bk k) (bx k (c₀' k)) (IsUnit.mk0 _ (h2' k))).1
  choose r hr hr' using fun k => (hw.2 k (c' k) (IsUnit.mk0 _ (h1' k))).2 (c k)
  choose q hq hq' using fun k => (hw.2 (bk k) (bx k (c₀ k)) (IsUnit.mk0 _ (h2 k))).2 (bx k (c₀' k))
  have hr0 : ∀ k, r k ≠ 0 := fun k h => h1 k (by rw [hr', h, zero_mul])
  have hq0 : ∀ k, q k ≠ 0 := fun k h => h2' k (by
    show w ⟨bk k, bx k (c₀' k)⟩ = 0
    rw [hq', h, zero_mul])
  have e1 := valAt_prod_zpow hz hr hr0 a
  have e2 := valAt_prod_zpow hz hq hq0 a₀
  have hM : ∀ c₁ : (k : K₀) → J₀ k, i (∏ k, y₀ ⟨k, c₁ k⟩ ^ a₀ k) = ∏ k, y (blkV bk bx ⟨k, c₁ k⟩) ^ a₀ k := by
    intro c₁
    rw [map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_zpow₀]
    show _ = y ⟨bk k, bx k (c₁ k)⟩ ^ a₀ k
    rw [hy]
  have key : cmpFn i y₀ y a a₀ e e₀ c' c₀' = cmpFn i y₀ y a a₀ e e₀ c c₀ *
      (∏ k, (y ⟨bk k, bx k (c₀' k)⟩ / y ⟨bk k, bx k (c₀ k)⟩) ^ a₀ k) *
      ∏ k, (y ⟨k, c k⟩ / y ⟨k, c' k⟩) ^ a k := by
    simp only [cmpFn, map_mul, hM, div_zpow, Finset.prod_div_distrib]
    have n1 : (∏ k, y ⟨k, c k⟩ ^ a k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hyc k)
    have n2 : (∏ k, y ⟨k, c' k⟩ ^ a k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hyc' k)
    have n3 : (∏ k, y ⟨bk k, bx k (c₀ k)⟩ ^ a₀ k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hyv k)
    have e3 : ∀ c₁ : (k : K₀) → J₀ k, (∏ k, y (blkV bk bx ⟨k, c₁ k⟩) ^ a₀ k) = ∏ k, y ⟨bk k, bx k (c₁ k)⟩ ^ a₀ k :=
      fun _ => rfl
    rw [e3, e3]
    by_cases he : e = 0
    · simp [he]
    · field_simp
  have hu2 := CxVal.unique hu' (key ▸ CxVal.mul (CxVal.mul hu e2) e1)
  have w1 : (∏ k, w ⟨k, c k⟩ ^ a k) = (∏ k, r k ^ a k) * ∏ k, w ⟨k, c' k⟩ ^ a k := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [hr' k, mul_zpow]
  have w2 : (∏ k, w (blkV bk bx ⟨k, c₀' k⟩) ^ a₀ k) =
      (∏ k, q k ^ a₀ k) * ∏ k, w (blkV bk bx ⟨k, c₀ k⟩) ^ a₀ k := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    show w ⟨bk k, bx k (c₀' k)⟩ ^ a₀ k = _
    rw [hq' k, mul_zpow]
    rfl
  have n4 : (∏ k, w (blkV bk bx ⟨k, c₀ k⟩) ^ a₀ k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (h2 k)
  have n5 : (∏ k, q k ^ a₀ k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hq0 k)
  simp only [cmpVal]
  rw [w1, w2, hu2]
  field_simp

end Val

section Points

open GroundTheory.Heights₂.Heights.LowerBoundFree (IsValueAt)

variable {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {i : Ω₀ →+* Ω} {y₀ : (Σ k, J₀ k) → Ω₀}
  {y : (Σ k, J k) → Ω} {bk : K₀ → K} {bx : ∀ k, J₀ k ≃ J (bk k)} {a : K → ℤ} {a₀ : K₀ → ℤ} {e : Ω} {e₀ : Ω₀}
  {w : (Σ k, J k) → ℂ}

/- English proof (translation)
Take `⟨z, hz, hw⟩` from `(GlobalTheory.T.complex_points_iff_centres X Ω ξ K J y hT w).1 hm`. Take `⟨c, c₀, u, h1, h2, -, hv, rfl⟩` from `h`. Take `⟨c', c₀', u', h1', h2', -, hv', rfl⟩` from `h'`. Conclude with `cmpVal_eq hy hz hw h1 h1' h2 h2' ((GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z w hz hw _ _).2 hv) ((GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z w hz hw _ _).2 hv')`.
-/
theorem isCmp_unique (hT : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩))
    (hy : ∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) (hm : w ∈ mcPts (mCoordIdeal y)) {t t' : ℂ}
    (h : IsCmp i y₀ y bk bx a a₀ e e₀ w t) (h' : IsCmp i y₀ y bk bx a a₀ e e₀ w t') : t = t' := by
  obtain ⟨z, hz, hw⟩ := (GlobalTheory.T.complex_points_iff_centres X Ω ξ K J y hT w).1 hm
  obtain ⟨c, c₀, u, h1, h2, -, hv, rfl⟩ := h
  obtain ⟨c', c₀', u', h1', h2', -, hv', rfl⟩ := h'
  exact cmpVal_eq hy hz hw h1 h1' h2 h2' ((GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z w hz hw _ _).2 hv)
    ((GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z w hz hw _ _).2 hv')

/- English proof (translation)
Take `⟨c, c₀, u, h1, h2, hu, -, rfl⟩` from `h`. Conclude with `cmpVal_ne_zero h1 h2 hu`.
-/
theorem IsCmp.ne_zero {t : ℂ} (h : IsCmp i y₀ y bk bx a a₀ e e₀ w t) : t ≠ 0 := by
  obtain ⟨c, c₀, u, h1, h2, hu, -, rfl⟩ := h
  exact cmpVal_ne_zero h1 h2 hu

/- English proof (translation)
Take `⟨z, hz, hw⟩` from `(GlobalTheory.T.complex_points_iff_centres X Ω ξ K J y hT w).1 hm`. Establish `hw' : CoordsAt ξ y z (fun p => s p.1 * w p)` using `coordsAt_orbit hw ⟨s, hs, rfl⟩`. Use `⟨(GlobalTheory.T.complex_points_iff_centres X Ω ξ K J y hT _).2 ⟨z, hz, hw'⟩, ?_⟩` and prove the remaining obligations. Take `⟨c, c₀, u, h1, h2, hu, hv, rfl⟩` from `h`. Use `⟨c, c₀, u, fun k => mul_ne_zero (hs _) (h1 k), fun k => mul_ne_zero (hs _) (h2 k), hu, (GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z _ hz hw' _ _).1 ((GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z w hz hw _ _).2 hv), ?_⟩` and prove the remaining obligations.

Establish `n1 : (∏ k, s (bk k) ^ a₀ k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hs _)`. Establish `n2 : (∏ k, w (blkV bk bx ⟨k, c₀ k⟩) ^ a₀ k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (h2 k)`. Establish `e1 : (∏ k, (s (blkV bk bx ⟨k, c₀ k⟩).1 * w (blkV bk bx ⟨k, c₀ k⟩)) ^ a₀ k) = (∏ k, s (bk k) ^ a₀ k) * ∏ k, w (blkV bk bx ⟨k, c₀ k⟩) ^ a₀ k`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun k _ => mul_zpow _ _ _`.

Establish `e2 : (∏ k, (s k * w ⟨k, c k⟩) ^ a k) = (∏ k, s k ^ a k) * ∏ k, w ⟨k, c k⟩ ^ a k`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun k _ => mul_zpow _ _ _`. Simplify using `only [cmpVal]`. Rewrite using `[e1, e2]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem IsCmp.smul (hT : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩))
    (hm : w ∈ mcPts (mCoordIdeal y)) {t : ℂ} (h : IsCmp i y₀ y bk bx a a₀ e e₀ w t) {s : K → ℂ}
    (hs : ∀ k, s k ≠ 0) :
    (fun p => s p.1 * w p) ∈ mcPts (mCoordIdeal y) ∧
    IsCmp i y₀ y bk bx a a₀ e e₀ (fun p => s p.1 * w p)
      ((∏ k, s k ^ a k) / (∏ k, s (bk k) ^ a₀ k) * t) := by
  obtain ⟨z, hz, hw⟩ := (GlobalTheory.T.complex_points_iff_centres X Ω ξ K J y hT w).1 hm
  have hw' : CoordsAt ξ y z (fun p => s p.1 * w p) := coordsAt_orbit hw ⟨s, hs, rfl⟩
  refine ⟨(GlobalTheory.T.complex_points_iff_centres X Ω ξ K J y hT _).2 ⟨z, hz, hw'⟩, ?_⟩
  obtain ⟨c, c₀, u, h1, h2, hu, hv, rfl⟩ := h
  refine ⟨c, c₀, u, fun k => mul_ne_zero (hs _) (h1 k), fun k => mul_ne_zero (hs _) (h2 k), hu,
    (GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z _ hz hw' _ _).1 ((GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z w hz hw _ _).2 hv), ?_⟩
  have n1 : (∏ k, s (bk k) ^ a₀ k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hs _)
  have n2 : (∏ k, w (blkV bk bx ⟨k, c₀ k⟩) ^ a₀ k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (h2 k)
  have e1 : (∏ k, (s (blkV bk bx ⟨k, c₀ k⟩).1 * w (blkV bk bx ⟨k, c₀ k⟩)) ^ a₀ k) =
      (∏ k, s (bk k) ^ a₀ k) * ∏ k, w (blkV bk bx ⟨k, c₀ k⟩) ^ a₀ k := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => mul_zpow _ _ _
  have e2 : (∏ k, (s k * w ⟨k, c k⟩) ^ a k) = (∏ k, s k ^ a k) * ∏ k, w ⟨k, c k⟩ ^ a k := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => mul_zpow _ _ _
  simp only [cmpVal]
  rw [e1, e2]
  field_simp

/- English proof (translation)
Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C n => simp`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p n hp => simp only [map_mul, hp, map_X, eval_X]`.
-/
theorem eval_conj {σ : Type} (g : MvPolynomial σ ℤ) (w : σ → ℂ) :
    eval (fun p => starRingEnd ℂ (w p)) (map (Int.castRingHom ℂ) g) =
      starRingEnd ℂ (eval w (map (Int.castRingHom ℂ) g)) := by
  induction g using MvPolynomial.induction_on with
  | C n => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp => simp only [map_mul, hp, map_X, eval_X]

/- English proof (translation)
Use `⟨fun k => ?_, fun f hf => ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `hm.1 k`. Conclude with `⟨x, by simpa using hx⟩`. Rewrite using `[eval_conj, hm.2 f hf, map_zero]`.
-/
theorem conj_mem_mcPts (hm : w ∈ mcPts (mCoordIdeal y)) :
    (fun p => starRingEnd ℂ (w p)) ∈ mcPts (mCoordIdeal y) := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨x, hx⟩ := hm.1 k
    exact ⟨x, by simpa using hx⟩
  · rw [eval_conj, hm.2 f hf, map_zero]

/- English proof (translation)
Take `⟨c, c₀, u, h1, h2, hu, ⟨d, g, h, hg, hh, hy0, heq, hz0, rfl⟩, rfl⟩` from `h`. Use `⟨c, c₀, _, fun k => by simpa using h1 k, fun k => by simpa using h2 k, ?_, ⟨d, g, h, hg, hh, hy0, heq, ?_, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[eval_conj, eval_conj, ← map_div₀]`. Simplify using `using hu`. Rewrite using `[eval_conj]`.

Simplify using `using hz0`. Simplify using `only [cmpVal, map_div₀, map_mul, map_prod, map_zpow₀, eval_conj]`.
-/
theorem IsCmp.conj {t : ℂ} (h : IsCmp i y₀ y bk bx a a₀ e e₀ w t) :
    IsCmp i y₀ y bk bx a a₀ e e₀ (fun p => starRingEnd ℂ (w p)) (starRingEnd ℂ t) := by
  obtain ⟨c, c₀, u, h1, h2, hu, ⟨d, g, h, hg, hh, hy0, heq, hz0, rfl⟩, rfl⟩ := h
  refine ⟨c, c₀, _, fun k => by simpa using h1 k, fun k => by simpa using h2 k, ?_,
    ⟨d, g, h, hg, hh, hy0, heq, ?_, rfl⟩, ?_⟩
  · rw [eval_conj, eval_conj, ← map_div₀]
    simpa using hu
  · rw [eval_conj]
    simpa using hz0
  · simp only [cmpVal, map_div₀, map_mul, map_prod, map_zpow₀, eval_conj]

end Points

/- English proof (translation)
Introduce `X Ω Ω₀ _ _ ξ i K₀ K _ _ J₀ J _ _ y₀ y bk bx a a₀ e e₀ hT hall hbk hy hU`. Establish `hval : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w → ∀ (c : (k : K) → J k) (c₀ : (k : K₀) → J₀ k), (∀ k, w ⟨k, c k⟩ ≠ 0) → (∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0) → ∃ u : ℂ, u ≠ 0 ∧ ValAt ξ z (cmpFn i y₀ y a a₀ e e₀ c c₀) u ∧ IsCmp i y₀ y bk bx a a₀ e e …`. Introduce `z w hw c c₀ h1 h2`. Take `⟨u, hu, hv⟩` from `hU z w hw c c₀ h1 h2`. Conclude with `⟨u, hu, hv, c, c₀, u, h1, h2, hu, (GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z w (hall _) hw _ _).1 hv, rfl⟩`.

Establish `hex : ∀ w ∈ mcPts (mCoordIdeal y), ∃ t, IsCmp i y₀ y bk bx a a₀ e e₀ w t`. Introduce `w hm`. Take `⟨z, -, hw⟩` from `(GlobalTheory.T.complex_points_iff_centres X Ω ξ K J y hT w).1 hm`. Use `choose c hc using hw.1`. Use `choose c₀ hc₀ using restr_ne (isBlockMap_blkV bx hbk) hm.1`.

Take `⟨u, -, -, h⟩` from `hval z w hw c c₀ (fun k => (hc k).ne_zero) hc₀`. Conclude with `⟨_, h⟩`. Set `ψ : ((Σ k, J k) → ℂ) → ℂ` to `fun w => if h : ∃ t, IsCmp i y₀ y bk bx a a₀ e e₀ w t then h.choose else 1`. Establish `hψ : ∀ w ∈ mcPts (mCoordIdeal y), ∀ t, IsCmp i y₀ y bk bx a a₀ e e₀ w t → ψ w = t`. Introduce `w hm t ht`.

Establish `h : ∃ t, IsCmp i y₀ y bk bx a a₀ e e₀ w t` using `⟨t, ht⟩`. Simplify using `only [ψ, dif_pos h]`. Conclude with `isCmp_unique hT hy hm h.choose_spec ht`. Use `⟨fun w => ‖ψ w‖, fun w hm => ?_, fun w hm => ?_, fun w hm s hs => ?_, fun w hm => ?_, ?_⟩` and prove the remaining obligations. Take `⟨t, ht⟩` from `hex w hm`.

Simplify `ht.ne_zero` using `[hψ w hm t ht]`. Take `⟨t, ht⟩` from `hex w hm show ‖ψ _‖ = ‖ψ w‖`. Rewrite using `[hψ w hm t ht, hψ _ (conj_mem_mcPts hm) _ ht.conj, Complex.norm_conj]`. Take `⟨t, ht⟩` from `hex w hm`. Take `⟨hm', ht'⟩` from `ht.smul hT hm hs`.

Use `show ‖ψ _‖ = _ * ‖ψ w‖`. Establish `n : ∀ k, ‖s k‖ ≠ 0` using `fun k => norm_ne_zero_iff.2 (hs k)`. Rewrite using `[hψ w hm t ht, hψ _ hm' _ ht', norm_mul, norm_div, norm_prod, norm_prod]`. Use `congr 1`. Simplify using `only [norm_zpow, Pi.sub_apply, zpow_sub₀ (n _), Finset.prod_div_distrib]`.

Rewrite using `[prod_comp_zpow hbk (fun k => ‖s k‖) a₀]`. Take `⟨t, c, c₀, u, h1, h2, -, ⟨d, g, h, hg, hh, hy0, heq, hz0, -⟩, -⟩` from `hex w hm`. Set `G : ((Σ k, J k) → ℂ) → ℂ` to `fun x => eval x (map (Int.castRingHom ℂ) g)`. Set `H : ((Σ k, J k) → ℂ) → ℂ` to `fun x => eval x (map (Int.castRingHom ℂ) h)`. Establish `aG : AnalyticOnNhd ℂ G Set.univ` using `AnalyticOnNhd.eval_mvPolynomial _`.

Establish `aH : AnalyticOnNhd ℂ H Set.univ` using `AnalyticOnNhd.eval_mvPolynomial _`. Establish `cH : Continuous H` using `MvPolynomial.continuous_eval _`. Set `V : Set ((Σ k, J k) → ℂ)` to `{x | H x ≠ 0} ∩ ((⋂ k, {x | x ⟨k, c k⟩ ≠ 0}) ∩ ⋂ k, {x | x (blkV bk bx ⟨k, c₀ k⟩) ≠ 0})`. Establish `oV : IsOpen V`. Use `(isOpen_ne_fun cH continuous_const).inter ((isOpen_iInter_of_finite fun k => ?_).inter (isOpen_iInter_of_finite fun k => ?_))` and prove the remaining obligations.

Conclude with `isOpen_ne_fun (continuous_apply _) continuous_const`. Conclude with `isOpen_ne_fun (continuous_apply _) continuous_const`. Establish `mV : ∀ x ∈ V, H x ≠ 0 ∧ (∀ k, x ⟨k, c k⟩ ≠ 0) ∧ ∀ k, x (blkV bk bx ⟨k, c₀ k⟩) ≠ 0`. Introduce `x hx`. Conclude with `⟨hx.1, fun k => Set.mem_iInter.1 hx.2.1 k, fun k => Set.mem_iInter.1 hx.2.2 k⟩`.

Use `⟨V, fun x => cmpVal bk bx a a₀ x c c₀ (G x / H x), oV, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `⟨hz0, Set.mem_iInter.2 h1, Set.mem_iInter.2 h2⟩`. Introduce `x hx`. Take `⟨x1, x2, x3⟩` from `mV x hx`. Establish `pr1 : ∀ p : Σ k, J k, AnalyticAt ℂ (fun x : (Σ k, J k) → ℂ => x p) x` using `fun p => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Σ k, J k => ℂ) p).analyticAt x`.

Use `((((aG x (Set.mem_univ _)).fun_div (aH x (Set.mem_univ _)) x1).fun_mul (Finset.analyticAt_fun_prod _ fun k _ => ?_)).fun_div (Finset.analyticAt_fun_prod _ fun k _ => ?_) ?_)` and prove the remaining obligations. Conclude with `(pr1 _).zpow (x2 k)`. Conclude with `(pr1 _).zpow (x3 k)`. Conclude with `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (x3 k)`. Introduce and unpack `x ⟨hx, hxm⟩`.

Take `⟨x1, x2, x3⟩` from `mV x hx`. Take `⟨z, hz, hw⟩` from `(GlobalTheory.T.complex_points_iff_centres X Ω ξ K J y hT x).1 hxm`. Establish `hv : GroundTheory.Heights₂.Heights.LowerBoundFree.IsValueAt y (cmpFn i y₀ y a a₀ e e₀ c c₀) x (G x / H x)` using `⟨d, g, h, hg, hh, hy0, heq, x1, rfl⟩`. Take `⟨u, hu, hu', hc⟩` from `hval z x hw c c₀ x2 x3`. Establish `e1 : u = G x / H x` using `CxVal.unique hu' ((GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z x hz hw _ _).2 hv)`.

Rewrite `hc`, `hu` using `[e1]`. Conclude with `⟨hc.ne_zero, by show ‖ψ x‖ = _; rw [hψ x hxm _ hc]⟩`. Introduce `z w hw c c₀ h1 h2`. Establish `hm : w ∈ mcPts (mCoordIdeal y)` using `(GlobalTheory.T.complex_points_iff_centres X Ω ξ K J y hT w).2 ⟨z, hall _, hw⟩`. Take `⟨u, hu, hv, hc⟩` from `hval z w hw c c₀ h1 h2`.

Use `⟨u, hu, hv, ?_⟩` and prove the remaining obligations. Establish `n : (∏ k, ‖w (blkV bk bx ⟨k, c₀ k⟩)‖ ^ a₀ k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (h2 k))`. Use `show ‖ψ w‖ * _ = _`. Rewrite using `[hψ w hm _ hc]`. Simplify using `only [cmpVal, norm_div, norm_mul, norm_prod, norm_zpow]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem exists_isRatio : ∀ (X : Scheme.{0}) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (i : Ω₀ →+* Ω) (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ q : X, genPt ξ ⤳ q) → Function.Injective bk → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w → ∀ (c : (k : K) → J k) (c₀ : (k : K₀) → J₀ k), (∀ k, w ⟨k, c k⟩ ≠ 0) → (∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0) → ∃ u : ℂ, u ≠ 0 ∧ ValAt ξ z (i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀) / ((∏ k, y ⟨k, c k⟩ ^ a k) * e)) u) → ∃ φ : ((Σ k, J k) → ℂ) → ℝ, (∀ z ∈ mcPts (mCoordIdeal y), 0 < φ z) ∧ (∀ z ∈ mcPts (mCoordIdeal y), φ (fun p => starRingEnd ℂ (z p)) = φ z) ∧ (∀ z ∈ mcPts (mCoordIdeal y), ∀ c : K → ℂ, (∀ k, c k ≠ 0) → φ (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ (a - pullDeg bk a₀) k) * φ z) ∧ (∀ z ∈ mcPts (mCoordIdeal y), ∃ (V : Set ((Σ k, J k) → ℂ)) (F : ((Σ k, J k) → ℂ) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ F V ∧ ∀ z' ∈ V ∩ mcPts (mCoordIdeal y), F z' ≠ 0 ∧ φ z' = ‖F z'‖) ∧ IsRatio ξ y y₀ bk bx i a a₀ e e₀ φ := by
  intro X Ω Ω₀ _ _ ξ i K₀ K _ _ J₀ J _ _ y₀ y bk bx a a₀ e e₀ hT hall hbk hy hU
  classical
  have hval : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w →
      ∀ (c : (k : K) → J k) (c₀ : (k : K₀) → J₀ k), (∀ k, w ⟨k, c k⟩ ≠ 0) → (∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0) →
      ∃ u : ℂ, u ≠ 0 ∧ ValAt ξ z (cmpFn i y₀ y a a₀ e e₀ c c₀) u ∧
        IsCmp i y₀ y bk bx a a₀ e e₀ w (cmpVal bk bx a a₀ w c c₀ u) := by
    intro z w hw c c₀ h1 h2
    obtain ⟨u, hu, hv⟩ := hU z w hw c c₀ h1 h2
    exact ⟨u, hu, hv, c, c₀, u, h1, h2, hu,
      (GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z w (hall _) hw _ _).1 hv, rfl⟩
  have hex : ∀ w ∈ mcPts (mCoordIdeal y), ∃ t, IsCmp i y₀ y bk bx a a₀ e e₀ w t := by
    intro w hm
    obtain ⟨z, -, hw⟩ := (GlobalTheory.T.complex_points_iff_centres X Ω ξ K J y hT w).1 hm
    choose c hc using hw.1
    choose c₀ hc₀ using restr_ne (isBlockMap_blkV bx hbk) hm.1
    obtain ⟨u, -, -, h⟩ := hval z w hw c c₀ (fun k => (hc k).ne_zero) hc₀
    exact ⟨_, h⟩
  let ψ : ((Σ k, J k) → ℂ) → ℂ := fun w =>
    if h : ∃ t, IsCmp i y₀ y bk bx a a₀ e e₀ w t then h.choose else 1
  have hψ : ∀ w ∈ mcPts (mCoordIdeal y), ∀ t, IsCmp i y₀ y bk bx a a₀ e e₀ w t → ψ w = t := by
    intro w hm t ht
    have h : ∃ t, IsCmp i y₀ y bk bx a a₀ e e₀ w t := ⟨t, ht⟩
    simp only [ψ, dif_pos h]
    exact isCmp_unique hT hy hm h.choose_spec ht
  refine ⟨fun w => ‖ψ w‖, fun w hm => ?_, fun w hm => ?_, fun w hm s hs => ?_, fun w hm => ?_, ?_⟩
  · obtain ⟨t, ht⟩ := hex w hm
    simpa [hψ w hm t ht] using ht.ne_zero
  · obtain ⟨t, ht⟩ := hex w hm
    show ‖ψ _‖ = ‖ψ w‖
    rw [hψ w hm t ht, hψ _ (conj_mem_mcPts hm) _ ht.conj, Complex.norm_conj]
  · obtain ⟨t, ht⟩ := hex w hm
    obtain ⟨hm', ht'⟩ := ht.smul hT hm hs
    show ‖ψ _‖ = _ * ‖ψ w‖
    have n : ∀ k, ‖s k‖ ≠ 0 := fun k => norm_ne_zero_iff.2 (hs k)
    rw [hψ w hm t ht, hψ _ hm' _ ht', norm_mul, norm_div, norm_prod, norm_prod]
    congr 1
    simp only [norm_zpow, Pi.sub_apply, zpow_sub₀ (n _), Finset.prod_div_distrib]
    rw [prod_comp_zpow hbk (fun k => ‖s k‖) a₀]
  · obtain ⟨t, c, c₀, u, h1, h2, -, ⟨d, g, h, hg, hh, hy0, heq, hz0, -⟩, -⟩ := hex w hm
    let G : ((Σ k, J k) → ℂ) → ℂ := fun x => eval x (map (Int.castRingHom ℂ) g)
    let H : ((Σ k, J k) → ℂ) → ℂ := fun x => eval x (map (Int.castRingHom ℂ) h)
    have aG : AnalyticOnNhd ℂ G Set.univ := AnalyticOnNhd.eval_mvPolynomial _
    have aH : AnalyticOnNhd ℂ H Set.univ := AnalyticOnNhd.eval_mvPolynomial _
    have cH : Continuous H := MvPolynomial.continuous_eval _
    let V : Set ((Σ k, J k) → ℂ) := {x | H x ≠ 0} ∩ ((⋂ k, {x | x ⟨k, c k⟩ ≠ 0}) ∩
      ⋂ k, {x | x (blkV bk bx ⟨k, c₀ k⟩) ≠ 0})
    have oV : IsOpen V := by
      refine (isOpen_ne_fun cH continuous_const).inter ((isOpen_iInter_of_finite fun k => ?_).inter
        (isOpen_iInter_of_finite fun k => ?_))
      · exact isOpen_ne_fun (continuous_apply _) continuous_const
      · exact isOpen_ne_fun (continuous_apply _) continuous_const
    have mV : ∀ x ∈ V, H x ≠ 0 ∧ (∀ k, x ⟨k, c k⟩ ≠ 0) ∧ ∀ k, x (blkV bk bx ⟨k, c₀ k⟩) ≠ 0 := by
      intro x hx
      exact ⟨hx.1, fun k => Set.mem_iInter.1 hx.2.1 k, fun k => Set.mem_iInter.1 hx.2.2 k⟩
    refine ⟨V, fun x => cmpVal bk bx a a₀ x c c₀ (G x / H x), oV, ?_, ?_, ?_⟩
    · exact ⟨hz0, Set.mem_iInter.2 h1, Set.mem_iInter.2 h2⟩
    · intro x hx
      obtain ⟨x1, x2, x3⟩ := mV x hx
      have pr1 : ∀ p : Σ k, J k, AnalyticAt ℂ (fun x : (Σ k, J k) → ℂ => x p) x := fun p =>
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Σ k, J k => ℂ) p).analyticAt x
      refine ((((aG x (Set.mem_univ _)).fun_div (aH x (Set.mem_univ _)) x1).fun_mul
        (Finset.analyticAt_fun_prod _ fun k _ => ?_)).fun_div
        (Finset.analyticAt_fun_prod _ fun k _ => ?_) ?_)
      · exact (pr1 _).zpow (x2 k)
      · exact (pr1 _).zpow (x3 k)
      · exact Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (x3 k)
    · rintro x ⟨hx, hxm⟩
      obtain ⟨x1, x2, x3⟩ := mV x hx
      obtain ⟨z, hz, hw⟩ := (GlobalTheory.T.complex_points_iff_centres X Ω ξ K J y hT x).1 hxm
      have hv : GroundTheory.Heights₂.Heights.LowerBoundFree.IsValueAt y (cmpFn i y₀ y a a₀ e e₀ c c₀) x (G x / H x) :=
        ⟨d, g, h, hg, hh, hy0, heq, x1, rfl⟩
      obtain ⟨u, hu, hu', hc⟩ := hval z x hw c c₀ x2 x3
      have e1 : u = G x / H x :=
        CxVal.unique hu' ((GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z x hz hw _ _).2 hv)
      rw [e1] at hc hu
      exact ⟨hc.ne_zero, by show ‖ψ x‖ = _; rw [hψ x hxm _ hc]⟩
  · intro z w hw c c₀ h1 h2
    have hm : w ∈ mcPts (mCoordIdeal y) := (GlobalTheory.T.complex_points_iff_centres X Ω ξ K J y hT w).2 ⟨z, hall _, hw⟩
    obtain ⟨u, hu, hv, hc⟩ := hval z w hw c c₀ h1 h2
    refine ⟨u, hu, hv, ?_⟩
    have n : (∏ k, ‖w (blkV bk bx ⟨k, c₀ k⟩)‖ ^ a₀ k) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (h2 k))
    show ‖ψ w‖ * _ = _
    rw [hψ w hm _ hc]
    simp only [cmpVal, norm_div, norm_mul, norm_prod, norm_zpow]
    field_simp

end GlobalTheory.CompanionTheory.Ar.Chg.Ratio
