import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.Moebius

/- English proof (translation)
Introduce `ht`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Conclude with `hx isAlgebraic_zero`. Establish `ht0 : t ≠ 0`.

Introduce and unpack `rfl`. Rewrite `h` using `[zero_mul]`. Conclude with `mul_ne_zero hx0 hr h.symm`. Establish `hE : algebraMap S K r - t * algebraMap S K q ≠ 0`. Introduce `hE`.

Establish `h2 : t * algebraMap S K p = x * (algebraMap S K r - t * algebraMap S K q)`. Take the linear combination `h`. Rewrite `h2` using `[hE, mul_zero]`. Conclude with `mul_ne_zero ht0 hp h2`. Establish `hxe : x = t * algebraMap S K p * (algebraMap S K r - t * algebraMap S K q)⁻¹`.

Rewrite using `[eq_mul_inv_iff_mul_eq₀ hE]`. Take the linear combination `-h`. Apply `hx` to reduce the goal to its premises. Rewrite using `[hxe]`. Conclude with `(ht.mul (isAlgebraic_algebraMap p)).mul ((isAlgebraic_algebraMap r).sub (ht.mul (isAlgebraic_algebraMap q))).inv`.
-/
private theorem transcendental_of_mul_add_eq_mul {S K : Type*} [CommRing S] [IsDomain S] [Field K]
    [Algebra S K] {x t : K} {p q r : S} (hx : Transcendental S x)
    (hp : algebraMap S K p ≠ 0) (hr : algebraMap S K r ≠ 0)
    (h : t * (algebraMap S K p + x * algebraMap S K q) = x * algebraMap S K r) :
    Transcendental S t := by
  intro ht
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx isAlgebraic_zero
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_mul] at h
    exact mul_ne_zero hx0 hr h.symm
  have hE : algebraMap S K r - t * algebraMap S K q ≠ 0 := by
    intro hE
    have h2 : t * algebraMap S K p = x * (algebraMap S K r - t * algebraMap S K q) := by
      linear_combination h
    rw [hE, mul_zero] at h2
    exact mul_ne_zero ht0 hp h2
  have hxe : x = t * algebraMap S K p * (algebraMap S K r - t * algebraMap S K q)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hE]
    linear_combination -h
  apply hx
  rw [hxe]
  exact (ht.mul (isAlgebraic_algebraMap p)).mul
    ((isAlgebraic_algebraMap r).sub (ht.mul (isAlgebraic_algebraMap q))).inv

/- English proof (translation)
Introduce `Φ S _ _ _ _ p q r hp hr`. Establish `hinj : Function.Injective (algebraMap (Polynomial S) (FractionRing (Polynomial S)))` using `IsFractionRing.injective _ _`. Establish `hs : ∀ s : S, algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C s) = algebraMap S (FractionRing (Polynomial S)) s` using `fun s => by`. Rewrite using `[IsScalarTower.algebraMap_apply S (Polynomial S) (FractionRing (Polynomial S)), Polynomial.algebraMap_eq]`. Establish `hpoly : Polynomial.C p + Polynomial.X * Polynomial.C q ≠ 0` using `fun h => hp (by simpa using congrArg (fun f => Polynomial.coeff f 0) h)`.

Establish `hD : algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C p) + algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C q) ≠ 0`. Rewrite using `[← map_mul, ← map_add]`. Conclude with `(map_ne_zero_iff _ hinj).2 hpoly`. Take `⟨t, ht⟩ : ∃ t, t = algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C r) / (algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C p) + algebraMap (Polynomial S) (FractionRing …` from `⟨_, rfl⟩`. Establish `htD : t * (algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C p) + algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C q)) = algebraMap (Polynomial S) (FractionRing (Polyno …`.

Rewrite using `[ht]`. Conclude with `div_mul_cancel₀ _ hD`. Establish `htr : Transcendental S t`. Use `transcendental_of_mul_add_eq_mul (p := p) (q := q) (r := r) ((transcendental_algebraMap_iff hinj).2 (Polynomial.transcendental_X S)) ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[← hs]`.

Conclude with `(map_ne_zero_iff _ hinj).2 (Polynomial.C_ne_zero.2 hp)`. Rewrite using `[← hs]`. Conclude with `(map_ne_zero_iff _ hinj).2 (Polynomial.C_ne_zero.2 hr)`. Simplify `htD` using `only [hs]`. Set `φ : Polynomial Φ →+* FractionRing (Polynomial S)` to `(Polynomial.aeval t).toRingHom.comp (Polynomial.mapRingHom (algebraMap Φ S))`.

Establish `hφinj : Function.Injective φ`. Introduce `P Q hPQ`. Apply `Polynomial.map_injective _ (algebraMap Φ S).injective` to reduce the goal to its premises. Conclude with `(transcendental_iff_injective.1 htr) hPQ`. Establish `hφC : ∀ a : Φ, φ (Polynomial.C a) = algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C (algebraMap Φ S a))`.

Introduce `a`. Rewrite using `[hs]`. Simplify using `[φ]`. Establish `hφX : φ Polynomial.X = t`. Simplify using `[φ]`.

Use `⟨RatFunc.liftRingHom φ (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective φ hφinj), fun a => ?_, hD, ?_⟩` and prove the remaining obligations. Rewrite using `[RatFunc.algebraMap_eq_C, ← RatFunc.algebraMap_C, RatFunc.liftRingHom_algebraMap, hφC]`. Rewrite using `[← RatFunc.algebraMap_X, RatFunc.liftRingHom_algebraMap, hφX, htD]`.
-/
theorem exists_ratFunc_embedding_moebius : ∀ (Φ S : Type) [Field Φ] [CommRing S] [IsDomain S] [Algebra Φ S] (p q r : S), p ≠ 0 → r ≠ 0 → ∃ θ : RatFunc Φ →+* FractionRing (Polynomial S), (∀ a, θ (algebraMap Φ (RatFunc Φ) a) = algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C (algebraMap Φ S a))) ∧ algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C p) + algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C q) ≠ 0 ∧ θ RatFunc.X * (algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C p) + algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C q)) = algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C r) := by
  intro Φ S _ _ _ _ p q r hp hr
  have hinj : Function.Injective (algebraMap (Polynomial S) (FractionRing (Polynomial S))) :=
    IsFractionRing.injective _ _
  have hs : ∀ s : S, algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C s) =
      algebraMap S (FractionRing (Polynomial S)) s := fun s => by
    rw [IsScalarTower.algebraMap_apply S (Polynomial S) (FractionRing (Polynomial S)),
      Polynomial.algebraMap_eq]
  have hpoly : Polynomial.C p + Polynomial.X * Polynomial.C q ≠ 0 := fun h =>
    hp (by simpa using congrArg (fun f => Polynomial.coeff f 0) h)
  have hD : algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C p) + algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C q) ≠ 0 := by
    rw [← map_mul, ← map_add]
    exact (map_ne_zero_iff _ hinj).2 hpoly
  obtain ⟨t, ht⟩ : ∃ t, t = algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C r) /
      (algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C p) + algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C q)) := ⟨_, rfl⟩
  have htD : t * (algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C p) + algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C q)) =
      algebraMap (Polynomial S) (FractionRing (Polynomial S)) Polynomial.X * algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C r) := by
    rw [ht]
    exact div_mul_cancel₀ _ hD
  have htr : Transcendental S t := by
    refine transcendental_of_mul_add_eq_mul (p := p) (q := q) (r := r)
      ((transcendental_algebraMap_iff hinj).2 (Polynomial.transcendental_X S)) ?_ ?_ ?_
    · rw [← hs]
      exact (map_ne_zero_iff _ hinj).2 (Polynomial.C_ne_zero.2 hp)
    · rw [← hs]
      exact (map_ne_zero_iff _ hinj).2 (Polynomial.C_ne_zero.2 hr)
    · simpa only [hs] using htD
  let φ : Polynomial Φ →+* FractionRing (Polynomial S) :=
    (Polynomial.aeval t).toRingHom.comp (Polynomial.mapRingHom (algebraMap Φ S))
  have hφinj : Function.Injective φ := by
    intro P Q hPQ
    apply Polynomial.map_injective _ (algebraMap Φ S).injective
    exact (transcendental_iff_injective.1 htr) hPQ
  have hφC : ∀ a : Φ, φ (Polynomial.C a) = algebraMap (Polynomial S) (FractionRing (Polynomial S)) (Polynomial.C (algebraMap Φ S a)) := by
    intro a
    rw [hs]
    simp [φ]
  have hφX : φ Polynomial.X = t := by
    simp [φ]
  refine ⟨RatFunc.liftRingHom φ (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective φ hφinj),
    fun a => ?_, hD, ?_⟩
  · rw [RatFunc.algebraMap_eq_C, ← RatFunc.algebraMap_C, RatFunc.liftRingHom_algebraMap, hφC]
  · rw [← RatFunc.algebraMap_X, RatFunc.liftRingHom_algebraMap, hφX, htD]

end GlobalTheory.CompanionTheory.Ar.Moebius
