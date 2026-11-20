import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsUnitIffUnitAt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalizationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueCentreLocalHomStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeChartExistsUniquePointStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TiePoints

open AlgebraicGeometry CategoryTheory MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X}

/- English proof (translation)
Take `⟨φ, h1, _⟩` from `ValHom.exists_valAt_hom X Ω ξ R z h.1 hξ`. Take `⟨ha, e⟩` from `(h1 a r).1 h`. Take `⟨ha', e'⟩` from `(h1 a r').1 h'`. Rewrite using `[← e, ← e']`.
-/
theorem valAt_unique (hξ : IsCptGen ξ) {a : Ω} {r r' : R} (h : ValAt ξ z a r) (h' : ValAt ξ z a r') :
    r = r' := by
  obtain ⟨φ, h1, _⟩ := ValHom.exists_valAt_hom X Ω ξ R z h.1 hξ
  obtain ⟨ha, e⟩ := (h1 a r).1 h
  obtain ⟨ha', e'⟩ := (h1 a r').1 h'
  rw [← e, ← e']

/- English proof (translation)
Take `⟨φ, h1, _⟩` from `ValHom.exists_valAt_hom X Ω ξ R z h.1 hξ`. Take `⟨ha, e⟩` from `(h1 a r).1 h`. Take `⟨hb, e'⟩` from `(h1 b s).1 h'`. Use `(h1 _ _).2 ⟨mul_mem ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[← e, ← e', ← map_mul]`.

Both sides reduce to the same expression.
-/
theorem valAt_mul (hξ : IsCptGen ξ) {a b : Ω} {r s : R} (h : ValAt ξ z a r) (h' : ValAt ξ z b s) :
    ValAt ξ z (a * b) (r * s) := by
  obtain ⟨φ, h1, _⟩ := ValHom.exists_valAt_hom X Ω ξ R z h.1 hξ
  obtain ⟨ha, e⟩ := (h1 a r).1 h
  obtain ⟨hb, e'⟩ := (h1 b s).1 h'
  refine (h1 _ _).2 ⟨mul_mem ha hb, ?_⟩
  rw [← e, ← e', ← map_mul]
  rfl

/- English proof (translation)
Take `⟨φ, h1, _⟩` from `ValHom.exists_valAt_hom X Ω ξ R z h hξ`. Use `(h1 _ _).2 ⟨one_mem _, ?_⟩` and prove the remaining obligations. Conclude with `map_one φ`.
-/
theorem valAt_one (hξ : IsCptGen ξ) (h : genPt ξ ⤳ centre z) : ValAt ξ z (1 : Ω) (1 : R) := by
  obtain ⟨φ, h1, _⟩ := ValHom.exists_valAt_hom X Ω ξ R z h hξ
  refine (h1 _ _).2 ⟨one_mem _, ?_⟩
  exact map_one φ

/- English proof (translation)
Take `⟨φ, h1, _⟩` from `ValHom.exists_valAt_hom X Ω ξ R z h hξ`. Conclude with `⟨_, (h1 a _).2 ⟨ha, rfl⟩⟩`.
-/
theorem exists_valAt (hξ : IsCptGen ξ) (h : genPt ξ ⤳ centre z) {a : Ω}
    (ha : a ∈ regAt ξ ⟨centre z, h⟩) : ∃ r : R, ValAt ξ z a r := by
  obtain ⟨φ, h1, _⟩ := ValHom.exists_valAt_hom X Ω ξ R z h hξ
  exact ⟨_, (h1 a _).2 ⟨ha, rfl⟩⟩

/- English proof (translation)
Take `⟨φ, h1, h2⟩` from `ValHom.exists_valAt_hom X Ω ξ R z h.1 hξ`. Take `⟨ha, e⟩` from `(h1 a r).1 h`. Take `⟨h0, _, hinv⟩` from `(h2 ⟨a, ha⟩).1 (e ▸ hr)`. Use `⟨h0, φ ⟨a⁻¹, hinv⟩, (h1 _ _).2 ⟨hinv, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← e, ← map_mul, ← map_one φ]`.

Use `congr 1`. Conclude with `Subtype.ext (inv_mul_cancel₀ h0)`.
-/
theorem valAt_inv (hξ : IsCptGen ξ) {a : Ω} {r : R} (h : ValAt ξ z a r) (hr : IsUnit r) :
    a ≠ 0 ∧ ∃ r' : R, ValAt ξ z a⁻¹ r' ∧ r' * r = 1 := by
  obtain ⟨φ, h1, h2⟩ := ValHom.exists_valAt_hom X Ω ξ R z h.1 hξ
  obtain ⟨ha, e⟩ := (h1 a r).1 h
  obtain ⟨h0, _, hinv⟩ := (h2 ⟨a, ha⟩).1 (e ▸ hr)
  refine ⟨h0, φ ⟨a⁻¹, hinv⟩, (h1 _ _).2 ⟨hinv, rfl⟩, ?_⟩
  rw [← e, ← map_mul, ← map_one φ]
  congr 1
  exact Subtype.ext (inv_mul_cancel₀ h0)

/- English proof (translation)
The claim follows from `MvPolynomial.comp_aeval_apply (φ := ({ f with commutes' := fun n => by simp [eq_intCast] } : A →ₐ[ℤ] B)) t g`.
-/
theorem map_aeval_int {σ A B : Type} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B] (f : A →+* B) (t : σ → A)
    (g : MvPolynomial σ ℤ) : f (aeval t g) = aeval (fun i => f (t i)) g :=
  MvPolynomial.comp_aeval_apply
    (φ := ({ f with commutes' := fun n => by simp [eq_intCast] } : A →ₐ[ℤ] B)) t g

/- English proof (translation)
Establish `hc : ∀ (S : Type) [CommRing S] [Algebra ℤ S] (v s : (Σ k, J k) → S) (e : K → S), (∀ k, s ⟨k, c k⟩ = 1) → (∀ p, v p = s p * e p.1) → ∀ k, v ⟨k, c k⟩ = e k`. Introduce `S _ _ v s e h1 h2 k`. Rewrite using `[h2, h1, one_mul]`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a`.

Use `⟨C a, 0, fun S _ _ v s e _ _ => ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Consider the case `add f g hf hg`. Take `⟨F, d, hF⟩` from `hf`. Take `⟨G, d', hG⟩` from `hg`.

Use `⟨F * (∏ k, X ⟨k, c k⟩) ^ d' + G * (∏ k, X ⟨k, c k⟩) ^ d, d + d', fun S _ _ v s e h1 h2 => ?_⟩` and prove the remaining obligations. Establish `hp : ∀ n, aeval v ((∏ k, X ⟨k, c k⟩ : MvPolynomial (Σ k, J k) ℤ) ^ n) = (∏ k, e k) ^ n`. Introduce `n`. Simplify using `[map_prod, hc S v s e h1 h2]`. Rewrite using `[map_add, map_mul, map_mul, hF S v s e h1 h2, hG S v s e h1 h2, hp, hp, map_add]`.

Simplify using `only [pow_add, Finset.prod_mul_distrib, Finset.prod_pow]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul_X f p hf`. Take `⟨F, d, hF⟩` from `hf`. Use `⟨F * X p * ∏ k ∈ Finset.univ.erase p.1, X ⟨k, c k⟩, d + 1, fun S _ _ v s e h1 h2 => ?_⟩` and prove the remaining obligations.

Establish `hp : aeval v (∏ k ∈ Finset.univ.erase p.1, X ⟨k, c k⟩ : MvPolynomial (Σ k, J k) ℤ) = ∏ k ∈ Finset.univ.erase p.1, e k`. Simplify using `[map_prod, hc S v s e h1 h2]`. Rewrite using `[map_mul, map_mul, hF S v s e h1 h2, hp, aeval_X, map_mul, aeval_X, h2]`. Establish `: ∏ k, e k ^ (d + 1) = (∏ k, e k ^ d) * (e p.1 * ∏ k ∈ Finset.univ.erase p.1, e k)`. Rewrite using `[Finset.mul_prod_erase _ _ (Finset.mem_univ _)]`.

Simplify using `only [pow_succ, Finset.prod_mul_distrib]`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_homog {K : Type} [Fintype K] {J : K → Type} (c : ∀ k, J k)
    (f : MvPolynomial (Σ k, J k) ℤ) :
    ∃ (F : MvPolynomial (Σ k, J k) ℤ) (d : ℕ), ∀ (S : Type) [CommRing S] [Algebra ℤ S] (v s : (Σ k, J k) → S)
      (e : K → S), (∀ k, s ⟨k, c k⟩ = 1) → (∀ p, v p = s p * e p.1) →
        aeval v F = (∏ k, e k ^ d) * aeval s f := by
  classical
  have hc : ∀ (S : Type) [CommRing S] [Algebra ℤ S] (v s : (Σ k, J k) → S) (e : K → S), (∀ k, s ⟨k, c k⟩ = 1) →
      (∀ p, v p = s p * e p.1) → ∀ k, v ⟨k, c k⟩ = e k := by
    intro S _ _ v s e h1 h2 k
    rw [h2, h1, one_mul]
  induction f using MvPolynomial.induction_on with
  | C a =>
    refine ⟨C a, 0, fun S _ _ v s e _ _ => ?_⟩
    simp
  | add f g hf hg =>
    obtain ⟨F, d, hF⟩ := hf
    obtain ⟨G, d', hG⟩ := hg
    refine ⟨F * (∏ k, X ⟨k, c k⟩) ^ d' + G * (∏ k, X ⟨k, c k⟩) ^ d, d + d', fun S _ _ v s e h1 h2 => ?_⟩
    have hp : ∀ n, aeval v ((∏ k, X ⟨k, c k⟩ : MvPolynomial (Σ k, J k) ℤ) ^ n) = (∏ k, e k) ^ n := by
      intro n
      simp [map_prod, hc S v s e h1 h2]
    rw [map_add, map_mul, map_mul, hF S v s e h1 h2, hG S v s e h1 h2, hp, hp, map_add]
    simp only [pow_add, Finset.prod_mul_distrib, Finset.prod_pow]
    ring
  | mul_X f p hf =>
    obtain ⟨F, d, hF⟩ := hf
    refine ⟨F * X p * ∏ k ∈ Finset.univ.erase p.1, X ⟨k, c k⟩, d + 1, fun S _ _ v s e h1 h2 => ?_⟩
    have hp : aeval v (∏ k ∈ Finset.univ.erase p.1, X ⟨k, c k⟩ : MvPolynomial (Σ k, J k) ℤ) =
        ∏ k ∈ Finset.univ.erase p.1, e k := by
      simp [map_prod, hc S v s e h1 h2]
    rw [map_mul, map_mul, hF S v s e h1 h2, hp, aeval_X, map_mul, aeval_X, h2]
    have : ∏ k, e k ^ (d + 1) = (∏ k, e k ^ d) * (e p.1 * ∏ k ∈ Finset.univ.erase p.1, e k) := by
      rw [Finset.mul_prod_erase _ _ (Finset.mem_univ _)]
      simp only [pow_succ, Finset.prod_mul_distrib]
    rw [this]
    ring

/- English proof (translation)
Take `⟨F, d, hF⟩` from `exists_homog c f`. Establish `h1` using `hF R w (fun p => w p * u p.1) (fun k => w ⟨k, c k⟩) hu (fun p => ?_)`. Establish `h2` using `hF (MvPolynomial K Ω) (fun p => C (y p) * X p.1) (fun p => C (y p / y ⟨p.1, c p.1⟩)) (fun k => C (y ⟨k, c k⟩) * X k) (fun k => by simp [div_self (hy k)]) (fun p => by`. Rewrite using `[← mul_assoc, ← C_mul, div_mul_cancel₀ _ (hy p.1)])`. Establish `h3 : F ∈ mCoordIdeal y`.

Express the relevant statement in the definitionally equal form `mConeMap y F = 0`. Express the relevant statement in the definitionally equal form `aeval _ F = 0`. Rewrite using `[h2]`. Use `map_aeval_int (C : Ω →+* MvPolynomial K Ω) (fun p => y p / y ⟨p.1, c p.1⟩) f` as an intermediate fact. Rewrite using `[← this, hf]`.

Simplify using the standard rewrite rules. Establish `h4` using `hw F h3`. Rewrite `h4` using `[h1]`. Establish `hunit : IsUnit (∏ k, w ⟨k, c k⟩ ^ d)` using `Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one (fun k _ => (IsUnit.of_mul_eq_one _ (hu k)).pow d)`. Conclude with `(hunit.mul_right_eq_zero).1 h4`.

Use `hu p.1` as an intermediate fact. Rewrite using `[mul_assoc, mul_comm (u p.1), this, mul_one]`.
-/
theorem aeval_ratio_eq_zero {K : Type} [Fintype K] {J : K → Type} (y : (Σ k, J k) → Ω)
    (c : ∀ k, J k) (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) (w : (Σ k, J k) → R) (u : K → R)
    (hu : ∀ k, w ⟨k, c k⟩ * u k = 1) (hw : ∀ g ∈ mCoordIdeal y, aeval w g = 0)
    (f : MvPolynomial (Σ k, J k) ℤ) (hf : aeval (fun p => y p / y ⟨p.1, c p.1⟩) f = 0) :
    aeval (fun p => w p * u p.1) f = 0 := by
  obtain ⟨F, d, hF⟩ := exists_homog c f
  have h1 := hF R w (fun p => w p * u p.1) (fun k => w ⟨k, c k⟩) hu (fun p => ?_)
  · have h2 := hF (MvPolynomial K Ω) (fun p => C (y p) * X p.1)
      (fun p => C (y p / y ⟨p.1, c p.1⟩)) (fun k => C (y ⟨k, c k⟩) * X k)
      (fun k => by simp [div_self (hy k)])
      (fun p => by
        rw [← mul_assoc, ← C_mul, div_mul_cancel₀ _ (hy p.1)])
    have h3 : F ∈ mCoordIdeal y := by
      change mConeMap y F = 0
      change aeval _ F = 0
      rw [h2]
      have := map_aeval_int (C : Ω →+* MvPolynomial K Ω) (fun p => y p / y ⟨p.1, c p.1⟩) f
      rw [← this, hf]
      simp
    have h4 := hw F h3
    rw [h1] at h4
    have hunit : IsUnit (∏ k, w ⟨k, c k⟩ ^ d) :=
      Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one
        (fun k _ => (IsUnit.of_mul_eq_one _ (hu k)).pow d)
    exact (hunit.mul_right_eq_zero).1 h4
  · have := hu p.1
    rw [mul_assoc, mul_comm (u p.1), this, mul_one]

/- English proof (translation)
Establish `hg' : mConeMap y g = 0` using `hg`. Set `σ : MvPolynomial K Ω →+* MvPolynomial K Ω` to `eval₂Hom C (fun k => C (y ⟨k, c k⟩)⁻¹ * X k)`. Set `inc : MvPolynomial K B →+* MvPolynomial K Ω` to `MvPolynomial.map B.subtype`. Set `th : MvPolynomial K B →+* R` to `eval₂Hom φ (fun k => w ⟨k, c k⟩)`. Set `mm : MvPolynomial (Σ k, J k) ℤ → MvPolynomial K B` to `fun g => aeval (fun p => C (b p) * X p.1) g`.

Establish `h0 : inc (mm g) = 0`. Establish `e1 : inc (mm g) = σ (mConeMap y g)`. Express the relevant statement in the definitionally equal form `inc (aeval _ g) = σ (aeval _ g)`. Rewrite using `[map_aeval_int, map_aeval_int]`. Use `congr 2`.

Use function extensionality and compare the values at `p`. Simplify using `only [inc, σ, map_mul, map_C, map_X, eval₂Hom_C, eval₂Hom_X']`. Simplify using `only [Subring.subtype_apply, hb, RingHom.id_apply]`. Rewrite using `[← mul_assoc, ← C_mul]`. Use `congr 2`.

Use `hy p.1` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Rewrite using `[e1, hg', map_zero]`. Establish `h1 : mm g = 0`. Apply `MvPolynomial.map_injective B.subtype Subtype.val_injective` to reduce the goal to its premises.

Simplify `h0` using `[inc]`. Establish `h2 : aeval w g = th (mm g)`. Express the relevant statement in the definitionally equal form `_ = th (aeval _ g)`. Rewrite using `[map_aeval_int]`. Use `congr 2`.

Use function extensionality and compare the values at `p`. Simplify using `only [th, map_mul, eval₂Hom_C, eval₂Hom_X']`. Conclude with `hw p`. Rewrite using `[h2, h1, map_zero]`.
-/
theorem aeval_eq_zero_of_ratio {K : Type} [Fintype K] {J : K → Type} (y : (Σ k, J k) → Ω)
    (c : ∀ k, J k) (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) (w : (Σ k, J k) → R) (B : Subring Ω) (φ : B →+* R)
    (b : (Σ k, J k) → B) (hb : ∀ p, (b p : Ω) = y p / y ⟨p.1, c p.1⟩)
    (hw : ∀ p, w p = φ (b p) * w ⟨p.1, c p.1⟩) (g : MvPolynomial (Σ k, J k) ℤ)
    (hg : g ∈ mCoordIdeal y) : aeval w g = 0 := by
  have hg' : mConeMap y g = 0 := hg
  let σ : MvPolynomial K Ω →+* MvPolynomial K Ω :=
    eval₂Hom C (fun k => C (y ⟨k, c k⟩)⁻¹ * X k)
  let inc : MvPolynomial K B →+* MvPolynomial K Ω := MvPolynomial.map B.subtype
  let th : MvPolynomial K B →+* R := eval₂Hom φ (fun k => w ⟨k, c k⟩)
  let mm : MvPolynomial (Σ k, J k) ℤ → MvPolynomial K B :=
    fun g => aeval (fun p => C (b p) * X p.1) g
  have h0 : inc (mm g) = 0 := by
    have e1 : inc (mm g) = σ (mConeMap y g) := by
      change inc (aeval _ g) = σ (aeval _ g)
      rw [map_aeval_int, map_aeval_int]
      congr 2
      funext p
      simp only [inc, σ, map_mul, map_C, map_X, eval₂Hom_C, eval₂Hom_X']
      simp only [Subring.subtype_apply, hb, RingHom.id_apply]
      rw [← mul_assoc, ← C_mul]
      congr 2
      have := hy p.1
      field_simp
    rw [e1, hg', map_zero]
  have h1 : mm g = 0 := by
    apply MvPolynomial.map_injective B.subtype Subtype.val_injective
    simpa [inc] using h0
  have h2 : aeval w g = th (mm g) := by
    change _ = th (aeval _ g)
    rw [map_aeval_int]
    congr 2
    funext p
    simp only [th, map_mul, eval₂Hom_C, eval₂Hom_X']
    exact hw p
  rw [h2, h1, map_zero]

section Main

variable {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

/- English proof (translation)
Rewrite using `[← Finset.mul_prod_erase Finset.univ (fun l => y ⟨l, Function.update c k i l⟩) (Finset.mem_univ k), ← Finset.mul_prod_erase Finset.univ (fun l => y ⟨l, c l⟩) (Finset.mem_univ k)]`. Establish `e : ∏ l ∈ Finset.univ.erase k, y ⟨l, Function.update c k i l⟩ = ∏ l ∈ Finset.univ.erase k, y ⟨l, c l⟩` using `Finset.prod_congr rfl fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]`. Establish `h0 : ∏ l ∈ Finset.univ.erase k, y ⟨l, c l⟩ ≠ 0` using `Finset.prod_ne_zero_iff.2 fun l _ => hy l`. Establish `h1` using `hy k`. Simplify using `only [e, Function.update_self]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem ratio_update [DecidableEq K] (y : (Σ k, J k) → Ω) (c : ∀ k, J k)
    (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) (k : K) (i : J k) :
    (∏ l, y ⟨l, Function.update c k i l⟩) / (∏ l, y ⟨l, c l⟩) = y ⟨k, i⟩ / y ⟨k, c k⟩ := by
  rw [← Finset.mul_prod_erase Finset.univ (fun l => y ⟨l, Function.update c k i l⟩) (Finset.mem_univ k),
    ← Finset.mul_prod_erase Finset.univ (fun l => y ⟨l, c l⟩) (Finset.mem_univ k)]
  have e : ∏ l ∈ Finset.univ.erase k, y ⟨l, Function.update c k i l⟩ =
      ∏ l ∈ Finset.univ.erase k, y ⟨l, c l⟩ :=
    Finset.prod_congr rfl fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  have h0 : ∏ l ∈ Finset.univ.erase k, y ⟨l, c l⟩ ≠ 0 := Finset.prod_ne_zero_iff.2 fun l _ => hy l
  have h1 := hy k
  simp only [e, Function.update_self]
  field_simp

/- English proof (translation)
Establish `hξ` using `T.gen`. Take `⟨c, hc0, hc⟩` from `T.cover ⟨centre z, h⟩`. Establish `hy : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k => Finset.prod_ne_zero_iff.1 hc0 k (Finset.mem_univ k)`. Establish `ht : ∀ p : Σ k, J k, ∃ r : R, ValAt ξ z (y p / y ⟨p.1, c p.1⟩) r`. Introduce and unpack `⟨k, i⟩`.

Establish `h1 : y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ regAt ξ ⟨centre z, h⟩`. Rewrite using `[← ratio_update y c hy k i]`. Conclude with `hc (Function.update c k i)`. Conclude with `exists_valAt hξ h h1`. Use `choose w hw using ht`.

Establish `hw1 : ∀ k, w ⟨k, c k⟩ = 1` using `fun k => by`. Establish `h1 : ValAt ξ z (y ⟨k, c k⟩ / y ⟨k, c k⟩) (w ⟨k, c k⟩)` using `hw _`. Rewrite `h1` using `[div_self (hy k)]`. Conclude with `valAt_unique hξ h1 (valAt_one hξ h)`. Use `⟨w, fun k => ⟨c k, by rw [hw1]; exact isUnit_one⟩, fun k c' hu => ?_⟩` and prove the remaining obligations.

Establish `hv : ValAt ξ z (y ⟨k, c'⟩ / y ⟨k, c k⟩) (w ⟨k, c'⟩)` using `hw _`. Take `⟨h0, r', hr', hm⟩` from `valAt_inv hξ hv hu`. Establish `hy' : y ⟨k, c'⟩ ≠ 0` using `fun e => h0 (by rw [e, zero_div])`. Use `⟨hy', fun i => ⟨w ⟨k, i⟩ * r', ?_, ?_⟩⟩` and prove the remaining obligations. Establish `hv' : ValAt ξ z (y ⟨k, i⟩ / y ⟨k, c k⟩) (w ⟨k, i⟩)` using `hw _`.

Establish `h1` using `valAt_mul hξ hv' hr'`. Establish `h2 : y ⟨k, i⟩ / y ⟨k, c k⟩ * (y ⟨k, c'⟩ / y ⟨k, c k⟩)⁻¹ = y ⟨k, i⟩ / y ⟨k, c'⟩`. Use `hy k` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Rewrite `h1` using `[h2]`. Then use the resulting hypothesis.

Rewrite using `[mul_assoc, hm, mul_one]`.
-/
theorem exists_coords (T : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩))
    (h : genPt ξ ⤳ centre z) : ∃ w, CoordsAt ξ y z w := by
  classical
  have hξ := T.gen
  obtain ⟨c, hc0, hc⟩ := T.cover ⟨centre z, h⟩
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc0 k (Finset.mem_univ k)
  have ht : ∀ p : Σ k, J k, ∃ r : R, ValAt ξ z (y p / y ⟨p.1, c p.1⟩) r := by
    rintro ⟨k, i⟩
    have h1 : y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ regAt ξ ⟨centre z, h⟩ := by
      rw [← ratio_update y c hy k i]
      exact hc (Function.update c k i)
    exact exists_valAt hξ h h1
  choose w hw using ht
  have hw1 : ∀ k, w ⟨k, c k⟩ = 1 := fun k => by
    have h1 : ValAt ξ z (y ⟨k, c k⟩ / y ⟨k, c k⟩) (w ⟨k, c k⟩) := hw _
    rw [div_self (hy k)] at h1
    exact valAt_unique hξ h1 (valAt_one hξ h)
  refine ⟨w, fun k => ⟨c k, by rw [hw1]; exact isUnit_one⟩, fun k c' hu => ?_⟩
  have hv : ValAt ξ z (y ⟨k, c'⟩ / y ⟨k, c k⟩) (w ⟨k, c'⟩) := hw _
  obtain ⟨h0, r', hr', hm⟩ := valAt_inv hξ hv hu
  have hy' : y ⟨k, c'⟩ ≠ 0 := fun e => h0 (by rw [e, zero_div])
  refine ⟨hy', fun i => ⟨w ⟨k, i⟩ * r', ?_, ?_⟩⟩
  · have hv' : ValAt ξ z (y ⟨k, i⟩ / y ⟨k, c k⟩) (w ⟨k, i⟩) := hw _
    have h1 := valAt_mul hξ hv' hr'
    have h2 : y ⟨k, i⟩ / y ⟨k, c k⟩ * (y ⟨k, c'⟩ / y ⟨k, c k⟩)⁻¹ = y ⟨k, i⟩ / y ⟨k, c'⟩ := by
      have := hy k
      field_simp
    rwa [h2] at h1
  · rw [mul_assoc, hm, mul_one]

/- English proof (translation)
Use `choose c hc using hz.1`. Establish `hy : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k => (hz.2 k (c k) (hc k)).1`. Take `⟨φ, h1, _⟩` from `ValHom.exists_valAt_hom X Ω ξ R z h hξ`. Establish `hb : ∀ p : Σ k, J k, ∃ b : regAt ξ ⟨centre z, h⟩, (b : Ω) = y p / y ⟨p.1, c p.1⟩ ∧ w p = φ b * w ⟨p.1, c p.1⟩`. Introduce and unpack `⟨k, i⟩`.

Take `⟨r, hv, e⟩` from `(hz.2 k (c k) (hc k)).2 i`. Take `⟨ha, e'⟩` from `(h1 _ _).1 hv`. Conclude with `⟨⟨_, ha⟩, rfl, by rw [e, e']⟩`. Use `choose b hb1 hb2 using hb`. Conclude with `aeval_eq_zero_of_ratio y c hy w _ φ b hb1 hb2 g hg`.
-/
theorem coords_kill (hξ : IsCptGen ξ) (h : genPt ξ ⤳ centre z) {w : (Σ k, J k) → R}
    (hz : CoordsAt ξ y z w) (g : MvPolynomial (Σ k, J k) ℤ) (hg : g ∈ mCoordIdeal y) :
    aeval w g = 0 := by
  choose c hc using hz.1
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hz.2 k (c k) (hc k)).1
  obtain ⟨φ, h1, _⟩ := ValHom.exists_valAt_hom X Ω ξ R z h hξ
  have hb : ∀ p : Σ k, J k, ∃ b : regAt ξ ⟨centre z, h⟩, (b : Ω) = y p / y ⟨p.1, c p.1⟩ ∧
      w p = φ b * w ⟨p.1, c p.1⟩ := by
    rintro ⟨k, i⟩
    obtain ⟨r, hv, e⟩ := (hz.2 k (c k) (hc k)).2 i
    obtain ⟨ha, e'⟩ := (h1 _ _).1 hv
    exact ⟨⟨_, ha⟩, rfl, by rw [e, e']⟩
  choose b hb1 hb2 using hb
  exact aeval_eq_zero_of_ratio y c hy w _ φ b hb1 hb2 g hg

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hz'`. Establish `key : ∀ k, ∃ a : Rˣ, ∀ i, w' ⟨k, i⟩ = a * w ⟨k, i⟩`. Introduce `k`. Take `⟨c, hc⟩` from `hz.1 k`.

Take `⟨c', hc'⟩` from `hz'.1 k`. Take `⟨hy, hw⟩` from `hz.2 k c hc`. Take `⟨hy', hw'⟩` from `hz'.2 k c' hc'`. Take `⟨r1, v1, e1⟩` from `hw c'`. Take `⟨r2, v2, e2⟩` from `hw' c`.

Establish `hm` using `valAt_mul hξ v1 v2`. Establish `h11 : y ⟨k, c'⟩ / y ⟨k, c⟩ * (y ⟨k, c⟩ / y ⟨k, c'⟩) = 1` using `by field_simp`. Rewrite `hm` using `[h11]`. Establish `hr : r1 * r2 = 1` using `valAt_unique hξ hm (valAt_one hξ v1.1)`. Establish `hu : IsUnit (w ⟨k, c'⟩)`.

Rewrite using `[e1]`. Conclude with `(IsUnit.of_mul_eq_one _ hr).mul hc`. Take `⟨_, hw3⟩` from `hz.2 k c' hu`. Use `⟨hc'.unit * hu.unit⁻¹, fun i => ?_⟩` and prove the remaining obligations. Take `⟨r3, v3, e3⟩` from `hw3 i`.

Take `⟨r4, v4, e4⟩` from `hw' i`. Establish `e34 : r3 = r4` using `valAt_unique hξ v3 v4`. Establish `hinv : ((hu.unit⁻¹ : Rˣ) : R) * w ⟨k, c'⟩ = 1` using `hu.val_inv_mul`. Rewrite using `[e4, e3, e34, Units.val_mul, IsUnit.unit_spec]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hinv, mul_one]`. Use `_ = _ := by ring`. Use `choose a ha using key`. Conclude with `⟨a, funext fun p => ha p.1 p.2⟩`. Introduce and unpack `⟨a, e⟩`.

Substitute `e` using the available equality. Use `⟨fun k => ?_, fun k c hu => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `hz.1 k`. Conclude with `⟨c, (a k).isUnit.mul hc⟩`. Establish `hu' : IsUnit (w ⟨k, c⟩)` using `(IsUnit.mul_iff.1 hu).2`.

Take `⟨hy, hw⟩` from `hz.2 k c hu'`. Use `⟨hy, fun i => ?_⟩` and prove the remaining obligations. Take `⟨r, v, e⟩` from `hw i`. Use `⟨r, v, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(a k : R) * w ⟨k, i⟩ = r * ((a k : R) * w ⟨k, c⟩)`.

Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coords_iff (hξ : IsCptGen ξ) {w : (Σ k, J k) → R} (hz : CoordsAt ξ y z w)
    (w' : (Σ k, J k) → R) :
    CoordsAt ξ y z w' ↔ ∃ a : K → Rˣ, w' = fun p => (a p.1 : R) * w p := by
  constructor
  · intro hz'
    have key : ∀ k, ∃ a : Rˣ, ∀ i, w' ⟨k, i⟩ = a * w ⟨k, i⟩ := by
      intro k
      obtain ⟨c, hc⟩ := hz.1 k
      obtain ⟨c', hc'⟩ := hz'.1 k
      obtain ⟨hy, hw⟩ := hz.2 k c hc
      obtain ⟨hy', hw'⟩ := hz'.2 k c' hc'
      obtain ⟨r1, v1, e1⟩ := hw c'
      obtain ⟨r2, v2, e2⟩ := hw' c
      have hm := valAt_mul hξ v1 v2
      have h11 : y ⟨k, c'⟩ / y ⟨k, c⟩ * (y ⟨k, c⟩ / y ⟨k, c'⟩) = 1 := by field_simp
      rw [h11] at hm
      have hr : r1 * r2 = 1 := valAt_unique hξ hm (valAt_one hξ v1.1)
      have hu : IsUnit (w ⟨k, c'⟩) := by
        rw [e1]
        exact (IsUnit.of_mul_eq_one _ hr).mul hc
      obtain ⟨_, hw3⟩ := hz.2 k c' hu
      refine ⟨hc'.unit * hu.unit⁻¹, fun i => ?_⟩
      obtain ⟨r3, v3, e3⟩ := hw3 i
      obtain ⟨r4, v4, e4⟩ := hw' i
      have e34 : r3 = r4 := valAt_unique hξ v3 v4
      have hinv : ((hu.unit⁻¹ : Rˣ) : R) * w ⟨k, c'⟩ = 1 := hu.val_inv_mul
      rw [e4, e3, e34, Units.val_mul, IsUnit.unit_spec]
      calc r4 * w' ⟨k, c'⟩ = r4 * w' ⟨k, c'⟩ * (((hu.unit⁻¹ : Rˣ) : R) * w ⟨k, c'⟩) := by
            rw [hinv, mul_one]
        _ = _ := by ring
    choose a ha using key
    exact ⟨a, funext fun p => ha p.1 p.2⟩
  · rintro ⟨a, e⟩
    subst e
    refine ⟨fun k => ?_, fun k c hu => ?_⟩
    · obtain ⟨c, hc⟩ := hz.1 k
      exact ⟨c, (a k).isUnit.mul hc⟩
    · have hu' : IsUnit (w ⟨k, c⟩) := (IsUnit.mul_iff.1 hu).2
      obtain ⟨hy, hw⟩ := hz.2 k c hu'
      refine ⟨hy, fun i => ?_⟩
      obtain ⟨r, v, e⟩ := hw i
      refine ⟨r, v, ?_⟩
      change (a k : R) * w ⟨k, i⟩ = r * ((a k : R) * w ⟨k, c⟩)
      rw [e]
      ring

/- English proof (translation)
Establish `hmem : ∀ s : Algebra.adjoin o (Set.range fun j => x j / x c), (s : Ω) ∈ regAt ξ p` using `fun s => (T.ring c hp.1 s).1 s.2 p hp`. Set `i : Algebra.adjoin o (Set.range fun j => x j / x c) →+* regAt ξ p` to `RingHom.codRestrict ((Algebra.adjoin o (Set.range fun j => x j / x c)).val : _ →+* Ω) (regAt ξ p) hmem`. Set `M : Submonoid (Algebra.adjoin o (Set.range fun j => x j / x c))` to `Submonoid.comap ψ (IsUnit.submonoid R)`. Use `letI : Algebra (Algebra.adjoin o (Set.range fun j => x j / x c)) (regAt ξ p) := i.toAlgebra`. Establish `hM : ∀ s : M, unitAt ξ p ((s : Algebra.adjoin o (Set.range fun j => x j / x c)) : Ω)` using `fun s => (hψ s).1 s.2`.

Use `haveI hloc : IsLocalization M (regAt ξ p) := by`. Use `(isLocalization_iff M _).2 ⟨fun s => ?_, fun a => ?_, fun {a b} e => ?_⟩` and prove the remaining obligations. Take `⟨h0, _, hinv⟩` from `hM s`. Conclude with `IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ h0))`. Take `⟨s, hsA, hu, hsa⟩` from `(GlobalTheory.T.regAt_iff_chart_localization X Ω ξ o κ x T c p hp a).1 a.2`.

Use `⟨(⟨s * a, hsa⟩, ⟨⟨s, hsA⟩, (hψ ⟨s, hsA⟩).2 hu⟩), Subtype.ext ?_⟩` and prove the remaining obligations. Conclude with `mul_comm (a : Ω) s`. Establish `: a = b` using `Subtype.ext (congrArg (fun q : regAt ξ p => (q : Ω)) e)`. Conclude with `⟨1, by rw [this]⟩`. Set `φ : regAt ξ p →+* R` to `IsLocalization.lift (M := M) (g := ψ) (fun s => s.2)`.

Establish `hφ : ∀ s, φ (i s) = ψ s` using `fun s => IsLocalization.lift_eq (M := M) (g := ψ) _ s`. Use `⟨φ, ⟨fun a ha => ?_⟩, fun s hs => hφ s⟩` and prove the remaining obligations. Take `⟨⟨b, s⟩, e⟩` from `IsLocalization.surj M a`. Establish `e' : φ a * ψ s = ψ b`. Establish `h1` using `congrArg φ e`.

Rewrite `h1` using `[map_mul]`. Conclude with `(congrArg (φ a * ·) (hφ s).symm).trans (h1.trans (hφ b))`. Establish `hb : IsUnit (ψ b)` using `e' ▸ ha.mul s.2`. Take `⟨b0, _, binv⟩` from `(hψ b).1 hb`. Establish `ev : (a : Ω) * (s : Algebra.adjoin o (Set.range fun j => x j / x c)) = b` using `congrArg Subtype.val e`.

Use `IsUnit.of_mul_eq_one ⟨_, mul_mem (hmem s) binv⟩ (Subtype.ext ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(a : Ω) * (((s : Algebra.adjoin o (Set.range fun j => x j / x c)) : Ω) * (b : Ω)⁻¹) = 1`. Rewrite using `[← mul_assoc, ev, mul_inv_cancel₀ b0]`.
-/
theorem exists_local_ext {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} {x : κ → Ω}
    (T : CoordTie o ξ x) {c : κ} {p : Cpt ξ} (hp : InChart ξ x c p)
    (ψ : Algebra.adjoin o (Set.range fun j => x j / x c) →+* R)
    (hψ : ∀ s, IsUnit (ψ s) ↔ unitAt ξ p (s : Ω)) :
    ∃ φ : regAt ξ p →+* R, IsLocalHom φ ∧
      ∀ (s : Algebra.adjoin o (Set.range fun j => x j / x c)) (hs : (s : Ω) ∈ regAt ξ p),
        φ ⟨s, hs⟩ = ψ s := by
  have hmem : ∀ s : Algebra.adjoin o (Set.range fun j => x j / x c), (s : Ω) ∈ regAt ξ p :=
    fun s => (T.ring c hp.1 s).1 s.2 p hp
  let i : Algebra.adjoin o (Set.range fun j => x j / x c) →+* regAt ξ p :=
    RingHom.codRestrict ((Algebra.adjoin o (Set.range fun j => x j / x c)).val :
      _ →+* Ω) (regAt ξ p) hmem
  let M : Submonoid (Algebra.adjoin o (Set.range fun j => x j / x c)) :=
    Submonoid.comap ψ (IsUnit.submonoid R)
  letI : Algebra (Algebra.adjoin o (Set.range fun j => x j / x c)) (regAt ξ p) := i.toAlgebra
  have hM : ∀ s : M, unitAt ξ p ((s : Algebra.adjoin o (Set.range fun j => x j / x c)) : Ω) :=
    fun s => (hψ s).1 s.2
  haveI hloc : IsLocalization M (regAt ξ p) := by
    refine (isLocalization_iff M _).2 ⟨fun s => ?_, fun a => ?_, fun {a b} e => ?_⟩
    · obtain ⟨h0, _, hinv⟩ := hM s
      exact IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ h0))
    · obtain ⟨s, hsA, hu, hsa⟩ :=
        (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ o κ x T c p hp a).1 a.2
      refine ⟨(⟨s * a, hsa⟩, ⟨⟨s, hsA⟩, (hψ ⟨s, hsA⟩).2 hu⟩), Subtype.ext ?_⟩
      exact mul_comm (a : Ω) s
    · have : a = b := Subtype.ext (congrArg (fun q : regAt ξ p => (q : Ω)) e)
      exact ⟨1, by rw [this]⟩
  let φ : regAt ξ p →+* R := IsLocalization.lift (M := M) (g := ψ) (fun s => s.2)
  have hφ : ∀ s, φ (i s) = ψ s := fun s => IsLocalization.lift_eq (M := M) (g := ψ) _ s
  refine ⟨φ, ⟨fun a ha => ?_⟩, fun s hs => hφ s⟩
  obtain ⟨⟨b, s⟩, e⟩ := IsLocalization.surj M a
  have e' : φ a * ψ s = ψ b := by
    have h1 := congrArg φ e
    rw [map_mul] at h1
    exact (congrArg (φ a * ·) (hφ s).symm).trans (h1.trans (hφ b))
  have hb : IsUnit (ψ b) := e' ▸ ha.mul s.2
  obtain ⟨b0, _, binv⟩ := (hψ b).1 hb
  have ev : (a : Ω) * (s : Algebra.adjoin o (Set.range fun j => x j / x c)) = b :=
    congrArg Subtype.val e
  refine IsUnit.of_mul_eq_one ⟨_, mul_mem (hmem s) binv⟩ (Subtype.ext ?_)
  change (a : Ω) * (((s : Algebra.adjoin o (Set.range fun j => x j / x c)) : Ω) * (b : Ω)⁻¹) = 1
  rw [← mul_assoc, ev, mul_inv_cancel₀ b0]

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Establish `hξ` using `T.gen`. Use `choose c hc using hu`. Establish `hyne : ∀ p, IsUnit (w p) → y p ≠ 0`. Introduce `p hp e`. Establish `h1 : (MvPolynomial.X p : MvPolynomial (Σ k, J k) ℤ) ∈ mCoordIdeal y`.

Express the relevant statement in the definitionally equal form `mConeMap y (MvPolynomial.X p) = 0`. Simplify using `[mConeMap, e]`. Establish `h2` using `hk _ h1`. Rewrite `h2` using `[aeval_X]`. Conclude with `hp.ne_zero h2`.

Establish `hy : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k => hyne _ (hc k)`. Establish `hxc : (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => hy k`. Take `⟨x, hx⟩ : ∃ x : ((k : K) → J k) → Ω, x = fun c' => ∏ k, y ⟨k, c' k⟩` from `⟨_, rfl⟩`. Rewrite `T`, `hxc` using `[← hx]`. Set `t : (Σ k, J k) → Ω` to `fun p => y p / y ⟨p.1, c p.1⟩`.

Establish `htA : ∀ p, t p ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c)`. Introduce and unpack `⟨k, i⟩`. Establish `h1 : t ⟨k, i⟩ = x (Function.update c k i) / x c`. Rewrite using `[hx]`. Conclude with `(ratio_update y c hy k i).symm`.

Rewrite using `[h1]`. Conclude with `Algebra.subset_adjoin ⟨_, rfl⟩`. Set `π : MvPolynomial (Σ k, J k) ℤ →ₐ[ℤ] Algebra.adjoin ℤ (Set.range fun j => x j / x c)` to `aeval (fun p => ⟨t p, htA p⟩)`. Establish `hπ : ∀ f, ((π f : Algebra.adjoin ℤ (Set.range fun j => x j / x c)) : Ω) = aeval t f` using `fun f => by`. Express the relevant statement in the definitionally equal form `(Algebra.adjoin ℤ (Set.range fun j => x j / x c)).val (aeval _ f) = _`.

Rewrite using `[MvPolynomial.comp_aeval_apply]`. Both sides reduce to the same expression. Establish `hsurj : Function.Surjective π`. Introduce `a`. Establish `h1 : Algebra.adjoin ℤ (Set.range fun j => x j / x c) ≤ (aeval t : MvPolynomial (Σ k, J k) ℤ →ₐ[ℤ] Ω).range`.

Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`. Use `⟨∏ k, MvPolynomial.X ⟨k, j k⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `aeval t (∏ k, MvPolynomial.X ⟨k, j k⟩) = _`. Rewrite using `[map_prod, hx]`.

Simplify using `only [aeval_X, t]`. Conclude with `Finset.prod_div_distrib _ _`. Take `⟨f, hf⟩` from `h1 a.2`. Conclude with `⟨f, Subtype.ext ((hπ f).trans hf)⟩`. Set `u : K → R` to `fun k => (((hc k).unit⁻¹ : Rˣ) : R)`.

Establish `hu1 : ∀ k, w ⟨k, c k⟩ * u k = 1` using `fun k => (hc k).mul_val_inv`. Establish `huu : ∀ k, IsUnit (u k)` using `fun k => Units.isUnit _`. Set `s : (Σ k, J k) → R` to `fun p => w p * u p.1`. Establish `hker : ∀ f, π f = 0 → aeval s f = 0`. Introduce `f hf`.

Use `aeval_ratio_eq_zero y c hy w u hu1 hk f ?_` and prove the remaining obligations. Rewrite using `[← show _ = aeval t f from hπ f, hf]`. Both sides reduce to the same expression. Set `ψ : Algebra.adjoin ℤ (Set.range fun j => x j / x c) →+* R` to `RingHom.liftOfSurjective (π : _ →+* _) hsurj ⟨(aeval s : MvPolynomial (Σ k, J k) ℤ →ₐ[ℤ] R), fun f hf => RingHom.mem_ker.2 (hker f (RingHom.mem_ker.1 hf))⟩`. Establish `hψ : ∀ f, ψ (π f) = aeval s f` using `fun f => RingHom.liftOfRightInverse_comp_apply _ _ _ _ f`.

Establish `hψt : ∀ p, ψ ⟨t p, htA p⟩ = s p` using `fun p => by`. Establish `h1` using `hψ (MvPolynomial.X p)`. Rewrite `h1` using `[aeval_X, aeval_X]`. Then use the resulting hypothesis. Set `I : Ideal (Algebra.adjoin ℤ (Set.range fun j => x j / x c))` to `(IsLocalRing.maximalIdeal R).comap ψ`. Use `haveI hIp : I.IsPrime := Ideal.comap_isPrime ψ _`.

Establish `hI : ∀ a, a ∉ I ↔ IsUnit (ψ a)` using `fun a => by`. Simplify using `[I, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Take `⟨p, ⟨hpc, hpu⟩, hpuniq⟩` from `GlobalTheory.T.prime_chart_existsUnique_point X Ω ξ ℤ _ x T c hxc I hIp`. Establish `hψu : ∀ a, IsUnit (ψ a) ↔ unitAt ξ p (a : Ω)` using `fun a => (hI a).symm.trans (hpu a)`. Take `⟨φ, hφl, hφ⟩` from `exists_local_ext T hpc ψ hψu`.

Take `⟨z, ⟨hzc, hzv⟩, hzuniq⟩` from `GlobalTheory.T.existsUnique_centre_local_hom X Ω ξ hξ p R φ hφl`. Establish `hmem : ∀ a : Algebra.adjoin ℤ (Set.range fun j => x j / x c), (a : Ω) ∈ regAt ξ p` using `fun a => (T.ring c hxc a).1 a.2 p hpc`. Establish `hval : ∀ a : Algebra.adjoin ℤ (Set.range fun j => x j / x c), ValAt ξ z (a : Ω) (ψ a)` using `fun a => by`. Rewrite using `[← hφ a (hmem a)]`. Conclude with `hzv ⟨a, hmem a⟩`.

Establish `hvt : ∀ q, ValAt ξ z (t q) (s q)` using `fun q => by`. Rewrite using `[← hψt q]`. Conclude with `hval ⟨t q, htA q⟩`. Use `⟨z, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hzc]`.

Conclude with `p.2`. Use `⟨fun k => ⟨c k, hc k⟩, fun k c' hcu => ⟨hyne _ hcu, fun i => ?_⟩⟩` and prove the remaining obligations. Establish `hsu : IsUnit (s ⟨k, c'⟩)` using `hcu.mul (huu k)`. Take `⟨h0, r', hr', hm⟩` from `valAt_inv hξ (hvt ⟨k, c'⟩) hsu`. Use `⟨s ⟨k, i⟩ * r', ?_, ?_⟩` and prove the remaining obligations.

Establish `h1` using `valAt_mul hξ (hvt ⟨k, i⟩) hr'`. Establish `h2 : t ⟨k, i⟩ * (t ⟨k, c'⟩)⁻¹ = y ⟨k, i⟩ / y ⟨k, c'⟩`. Establish `h3` using `hy k`. Establish `h4` using `hyne _ hcu`. Simplify using `only [t]`.

Clear the denominators using the available nonvanishing facts. Rewrite `h1` using `[h2]`. Then use the resulting hypothesis. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [s]`. Expand and normalize the polynomial expressions, which then agree.

Introduce and unpack `z' ⟨h', hz'⟩`. Apply `hzuniq` to reduce the goal to its premises. Establish `hv' : ∀ q, ValAt ξ z' (t q) (s q)`. Introduce and unpack `⟨k, i⟩`. Take `⟨r, v, e⟩` from `(hz'.2 k (c k) (hc k)).2 i`.

Establish `h1 : s ⟨k, i⟩ = r`. Express the relevant statement in the definitionally equal form `w ⟨k, i⟩ * u k = r`. Rewrite using `[e, mul_assoc, hu1, mul_one]`. Rewrite using `[h1]`. Conclude with `v`.

Establish `hreg : ∀ q, t q ∈ regAt ξ ⟨centre z', h'⟩` using `fun q => by`. Take `⟨_, g, e, _⟩` from `hv' q`. Conclude with `⟨g, e⟩`. Establish `hp'c : InChart ξ x c ⟨centre z', h'⟩`. Use `⟨hxc, fun j => ?_⟩` and prove the remaining obligations.

Establish `h1 : x j / x c = ∏ k, t ⟨k, j k⟩`. Rewrite using `[hx]`. Conclude with `(Finset.prod_div_distrib _ _).symm`. Rewrite using `[h1]`. Conclude with `prod_mem fun k _ => hreg _`.

Take `⟨φ', h1, h2⟩` from `ValHom.exists_valAt_hom X Ω ξ R z' h' hξ`. Establish `hmem' : ∀ a : Algebra.adjoin ℤ (Set.range fun j => x j / x c), (a : Ω) ∈ regAt ξ ⟨centre z', h'⟩` using `fun a => (T.ring c hxc a).1 a.2 _ hp'c`. Set `i' : Algebra.adjoin ℤ (Set.range fun j => x j / x c) →+* regAt ξ ⟨centre z', h'⟩` to `RingHom.codRestrict ((Algebra.adjoin ℤ (Set.range fun j => x j / x c)).val : _ →+* Ω) _ hmem'`. Establish `hcomp : ∀ a : Algebra.adjoin ℤ (Set.range fun j => x j / x c), φ' ⟨a, hmem' a⟩ = ψ a`. Introduce `a`.

Take `⟨f, rfl⟩` from `hsurj a`. Rewrite using `[hψ]`. Establish `e1 : (φ'.comp i') (aeval (fun p => ⟨t p, htA p⟩) f) = aeval (fun q => (φ'.comp i') ⟨t q, htA q⟩) f` using `map_aeval_int _ _ f`. Establish `e2 : (fun q => (φ'.comp i') ⟨t q, htA q⟩) = s`. Use function extensionality and compare the values at `q`.

Take `⟨_, e⟩` from `(h1 _ _).1 (hv' q)`. Conclude with `e`. Rewrite `e1` using `[e2]`. Conclude with `e1`. Establish `hval' : ∀ a : Algebra.adjoin ℤ (Set.range fun j => x j / x c), ValAt ξ z' (a : Ω) (ψ a)` using `fun a => (h1 _ _).2 ⟨hmem' a, hcomp a⟩`.

Establish `hpp : (⟨centre z', h'⟩ : Cpt ξ) = p`. Use `hpuniq _ ⟨hp'c, fun a => (hI a).trans ?_⟩` and prove the remaining obligations. Rewrite using `[← hcomp a]`. Conclude with `h2 ⟨a, hmem' a⟩`. Use `⟨congrArg Subtype.val hpp, fun a => ?_⟩` and prove the remaining obligations.

Establish `ha' : (a : Ω) ∈ regAt ξ ⟨centre z', h'⟩` using `hpp ▸ a.2`. Take `⟨r, hr⟩` from `exists_valAt hξ h' ha'`. Take `⟨σ, hσA, hσu, hσa⟩` from `(GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ _ x T c p hpc a).1 a.2`. Establish `e1` using `valAt_mul hξ (hval' ⟨σ, hσA⟩) hr`. Establish `e3 : ψ ⟨σ, hσA⟩ * r = ψ ⟨σ * a, hσa⟩` using `valAt_unique hξ e1 (hval' ⟨σ * a, hσa⟩)`.

Establish `e4 : ψ ⟨σ, hσA⟩ * φ a = ψ ⟨σ * a, hσa⟩`. Rewrite using `[← hφ ⟨σ, hσA⟩ (hmem _), ← hφ ⟨σ * a, hσa⟩ (hmem _), ← map_mul]`. Both sides reduce to the same expression. Establish `hun : IsUnit (ψ ⟨σ, hσA⟩)` using `(hψu _).2 hσu`. Establish `e5 : r = φ a` using `hun.mul_left_cancel (e3.trans e4.symm)`.

Rewrite using `[← e5]`. Conclude with `hr`.
-/
theorem existsUnique_point (T : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩))
    (w : (Σ k, J k) → R) (hu : ∀ k, ∃ c, IsUnit (w ⟨k, c⟩))
    (hk : ∀ g ∈ mCoordIdeal y, aeval w g = 0) :
    ∃! z : Spec (CommRingCat.of R) ⟶ X, genPt ξ ⤳ centre z ∧ CoordsAt ξ y z w := by
  classical
  have hξ := T.gen
  choose c hc using hu
  have hyne : ∀ p, IsUnit (w p) → y p ≠ 0 := by
    intro p hp e
    have h1 : (MvPolynomial.X p : MvPolynomial (Σ k, J k) ℤ) ∈ mCoordIdeal y := by
      change mConeMap y (MvPolynomial.X p) = 0
      simp [mConeMap, e]
    have h2 := hk _ h1
    rw [aeval_X] at h2
    exact hp.ne_zero h2
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => hyne _ (hc k)
  have hxc : (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => hy k
  obtain ⟨x, hx⟩ : ∃ x : ((k : K) → J k) → Ω, x = fun c' => ∏ k, y ⟨k, c' k⟩ := ⟨_, rfl⟩
  rw [← hx] at T hxc
  let t : (Σ k, J k) → Ω := fun p => y p / y ⟨p.1, c p.1⟩
  have htA : ∀ p, t p ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) := by
    rintro ⟨k, i⟩
    have h1 : t ⟨k, i⟩ = x (Function.update c k i) / x c := by
      rw [hx]
      exact (ratio_update y c hy k i).symm
    rw [h1]
    exact Algebra.subset_adjoin ⟨_, rfl⟩
  let π : MvPolynomial (Σ k, J k) ℤ →ₐ[ℤ] Algebra.adjoin ℤ (Set.range fun j => x j / x c) :=
    aeval (fun p => ⟨t p, htA p⟩)
  have hπ : ∀ f, ((π f : Algebra.adjoin ℤ (Set.range fun j => x j / x c)) : Ω) = aeval t f :=
    fun f => by
      change (Algebra.adjoin ℤ (Set.range fun j => x j / x c)).val (aeval _ f) = _
      rw [MvPolynomial.comp_aeval_apply]
      rfl
  have hsurj : Function.Surjective π := by
    intro a
    have h1 : Algebra.adjoin ℤ (Set.range fun j => x j / x c) ≤
        (aeval t : MvPolynomial (Σ k, J k) ℤ →ₐ[ℤ] Ω).range := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨j, rfl⟩
      refine ⟨∏ k, MvPolynomial.X ⟨k, j k⟩, ?_⟩
      change aeval t (∏ k, MvPolynomial.X ⟨k, j k⟩) = _
      rw [map_prod, hx]
      simp only [aeval_X, t]
      exact Finset.prod_div_distrib _ _
    obtain ⟨f, hf⟩ := h1 a.2
    exact ⟨f, Subtype.ext ((hπ f).trans hf)⟩
  let u : K → R := fun k => (((hc k).unit⁻¹ : Rˣ) : R)
  have hu1 : ∀ k, w ⟨k, c k⟩ * u k = 1 := fun k => (hc k).mul_val_inv
  have huu : ∀ k, IsUnit (u k) := fun k => Units.isUnit _
  let s : (Σ k, J k) → R := fun p => w p * u p.1
  have hker : ∀ f, π f = 0 → aeval s f = 0 := by
    intro f hf
    refine aeval_ratio_eq_zero y c hy w u hu1 hk f ?_
    rw [← show _ = aeval t f from hπ f, hf]
    rfl
  let ψ : Algebra.adjoin ℤ (Set.range fun j => x j / x c) →+* R :=
    RingHom.liftOfSurjective (π : _ →+* _) hsurj
      ⟨(aeval s : MvPolynomial (Σ k, J k) ℤ →ₐ[ℤ] R), fun f hf => RingHom.mem_ker.2 (hker f (RingHom.mem_ker.1 hf))⟩
  have hψ : ∀ f, ψ (π f) = aeval s f := fun f =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ f
  have hψt : ∀ p, ψ ⟨t p, htA p⟩ = s p := fun p => by
    have h1 := hψ (MvPolynomial.X p)
    rwa [aeval_X, aeval_X] at h1
  let I : Ideal (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) :=
    (IsLocalRing.maximalIdeal R).comap ψ
  haveI hIp : I.IsPrime := Ideal.comap_isPrime ψ _
  have hI : ∀ a, a ∉ I ↔ IsUnit (ψ a) := fun a => by
    simp [I, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  obtain ⟨p, ⟨hpc, hpu⟩, hpuniq⟩ := GlobalTheory.T.prime_chart_existsUnique_point X Ω ξ ℤ _ x T c hxc I hIp
  have hψu : ∀ a, IsUnit (ψ a) ↔ unitAt ξ p (a : Ω) := fun a => (hI a).symm.trans (hpu a)
  obtain ⟨φ, hφl, hφ⟩ := exists_local_ext T hpc ψ hψu
  obtain ⟨z, ⟨hzc, hzv⟩, hzuniq⟩ := GlobalTheory.T.existsUnique_centre_local_hom X Ω ξ hξ p R φ hφl
  have hmem : ∀ a : Algebra.adjoin ℤ (Set.range fun j => x j / x c), (a : Ω) ∈ regAt ξ p :=
    fun a => (T.ring c hxc a).1 a.2 p hpc
  have hval : ∀ a : Algebra.adjoin ℤ (Set.range fun j => x j / x c), ValAt ξ z (a : Ω) (ψ a) :=
    fun a => by
      rw [← hφ a (hmem a)]
      exact hzv ⟨a, hmem a⟩
  have hvt : ∀ q, ValAt ξ z (t q) (s q) := fun q => by
    rw [← hψt q]
    exact hval ⟨t q, htA q⟩
  refine ⟨z, ⟨?_, ?_⟩, ?_⟩
  · rw [hzc]
    exact p.2
  · refine ⟨fun k => ⟨c k, hc k⟩, fun k c' hcu => ⟨hyne _ hcu, fun i => ?_⟩⟩
    have hsu : IsUnit (s ⟨k, c'⟩) := hcu.mul (huu k)
    obtain ⟨h0, r', hr', hm⟩ := valAt_inv hξ (hvt ⟨k, c'⟩) hsu
    refine ⟨s ⟨k, i⟩ * r', ?_, ?_⟩
    · have h1 := valAt_mul hξ (hvt ⟨k, i⟩) hr'
      have h2 : t ⟨k, i⟩ * (t ⟨k, c'⟩)⁻¹ = y ⟨k, i⟩ / y ⟨k, c'⟩ := by
        have h3 := hy k
        have h4 := hyne _ hcu
        simp only [t]
        field_simp
      rwa [h2] at h1
    · calc w ⟨k, i⟩ = w ⟨k, i⟩ * (r' * s ⟨k, c'⟩) := by rw [hm, mul_one]
        _ = s ⟨k, i⟩ * r' * w ⟨k, c'⟩ := by
          simp only [s]
          ring
  · rintro z' ⟨h', hz'⟩
    apply hzuniq
    have hv' : ∀ q, ValAt ξ z' (t q) (s q) := by
      rintro ⟨k, i⟩
      obtain ⟨r, v, e⟩ := (hz'.2 k (c k) (hc k)).2 i
      have h1 : s ⟨k, i⟩ = r := by
        change w ⟨k, i⟩ * u k = r
        rw [e, mul_assoc, hu1, mul_one]
      rw [h1]
      exact v
    have hreg : ∀ q, t q ∈ regAt ξ ⟨centre z', h'⟩ := fun q => by
      obtain ⟨_, g, e, _⟩ := hv' q
      exact ⟨g, e⟩
    have hp'c : InChart ξ x c ⟨centre z', h'⟩ := by
      refine ⟨hxc, fun j => ?_⟩
      have h1 : x j / x c = ∏ k, t ⟨k, j k⟩ := by
        rw [hx]
        exact (Finset.prod_div_distrib _ _).symm
      rw [h1]
      exact prod_mem fun k _ => hreg _
    obtain ⟨φ', h1, h2⟩ := ValHom.exists_valAt_hom X Ω ξ R z' h' hξ
    have hmem' : ∀ a : Algebra.adjoin ℤ (Set.range fun j => x j / x c),
        (a : Ω) ∈ regAt ξ ⟨centre z', h'⟩ :=
      fun a => (T.ring c hxc a).1 a.2 _ hp'c
    let i' : Algebra.adjoin ℤ (Set.range fun j => x j / x c) →+* regAt ξ ⟨centre z', h'⟩ :=
      RingHom.codRestrict ((Algebra.adjoin ℤ (Set.range fun j => x j / x c)).val : _ →+* Ω) _ hmem'
    have hcomp : ∀ a : Algebra.adjoin ℤ (Set.range fun j => x j / x c), φ' ⟨a, hmem' a⟩ = ψ a := by
      intro a
      obtain ⟨f, rfl⟩ := hsurj a
      rw [hψ]
      have e1 : (φ'.comp i') (aeval (fun p => ⟨t p, htA p⟩) f) =
          aeval (fun q => (φ'.comp i') ⟨t q, htA q⟩) f := map_aeval_int _ _ f
      have e2 : (fun q => (φ'.comp i') ⟨t q, htA q⟩) = s := by
        funext q
        obtain ⟨_, e⟩ := (h1 _ _).1 (hv' q)
        exact e
      rw [e2] at e1
      exact e1
    have hval' : ∀ a : Algebra.adjoin ℤ (Set.range fun j => x j / x c),
        ValAt ξ z' (a : Ω) (ψ a) := fun a => (h1 _ _).2 ⟨hmem' a, hcomp a⟩
    have hpp : (⟨centre z', h'⟩ : Cpt ξ) = p := by
      refine hpuniq _ ⟨hp'c, fun a => (hI a).trans ?_⟩
      rw [← hcomp a]
      exact h2 ⟨a, hmem' a⟩
    refine ⟨congrArg Subtype.val hpp, fun a => ?_⟩
    have ha' : (a : Ω) ∈ regAt ξ ⟨centre z', h'⟩ := hpp ▸ a.2
    obtain ⟨r, hr⟩ := exists_valAt hξ h' ha'
    obtain ⟨σ, hσA, hσu, hσa⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ _ x T c p hpc a).1 a.2
    have e1 := valAt_mul hξ (hval' ⟨σ, hσA⟩) hr
    have e3 : ψ ⟨σ, hσA⟩ * r = ψ ⟨σ * a, hσa⟩ := valAt_unique hξ e1 (hval' ⟨σ * a, hσa⟩)
    have e4 : ψ ⟨σ, hσA⟩ * φ a = ψ ⟨σ * a, hσa⟩ := by
      rw [← hφ ⟨σ, hσA⟩ (hmem _), ← hφ ⟨σ * a, hσa⟩ (hmem _), ← map_mul]
      rfl
    have hun : IsUnit (ψ ⟨σ, hσA⟩) := (hψu _).2 hσu
    have e5 : r = φ a := hun.mul_left_cancel (e3.trans e4.symm)
    rw [← e5]
    exact hr

end Main

end GlobalTheory.CompanionTheory.Ar.TiePoints

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

/- English proof (translation)
Introduce `X Ω _ ξ K _ J _ y T R _ _`. Conclude with `⟨fun w hu hk => TiePoints.existsUnique_point T w hu hk, fun z h => TiePoints.exists_coords T h, fun z w h hz => ⟨TiePoints.coords_kill T.gen h hz, fun w' => TiePoints.coords_iff T.gen hz w'⟩⟩`.
-/
theorem GlobalTheory.CompanionTheory.Ar.tie_points : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (R : Type) [CommRing R] [IsLocalRing R], (∀ w : (Σ k, J k) → R, (∀ k, ∃ c, IsUnit (w ⟨k, c⟩)) → (∀ g ∈ mCoordIdeal y, MvPolynomial.aeval w g = 0) → ∃! z : Spec (CommRingCat.of R) ⟶ X, genPt ξ ⤳ centre z ∧ CoordsAt ξ y z w) ∧ (∀ z : Spec (CommRingCat.of R) ⟶ X, genPt ξ ⤳ centre z → ∃ w, CoordsAt ξ y z w) ∧ ∀ (z : Spec (CommRingCat.of R) ⟶ X) w, genPt ξ ⤳ centre z → CoordsAt ξ y z w → (∀ g ∈ mCoordIdeal y, MvPolynomial.aeval w g = 0) ∧ ∀ w', CoordsAt ξ y z w' ↔ ∃ a : K → Rˣ, w' = fun p => (a p.1 : R) * w p := by
  intro X Ω _ ξ K _ J _ y T R _ _
  exact ⟨fun w hu hk => TiePoints.existsUnique_point T w hu hk, fun z h => TiePoints.exists_coords T h,
    fun z w h hz => ⟨TiePoints.coords_kill T.gen h hz, fun w' => TiePoints.coords_iff T.gen hz w'⟩⟩
