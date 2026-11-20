import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncSmooth

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

/- English proof (translation)
Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Break down `hx with rfl | hx` into its components or cases. Conclude with `⟨1, by simpa [hf0] using (Algebra.adjoin ℚ T).one_mem⟩`. Conclude with `⟨0, by simpa using Algebra.subset_adjoin hx⟩`.

Consider the case `algebraMap r => exact ⟨0, by simpa using (Algebra.adjoin ℚ T).algebraMap_mem r⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨n, hn⟩` from `hx`. Take `⟨m, hm⟩` from `hy`. Use `⟨n + m, ?_⟩` and prove the remaining obligations.

Establish `: (x + y) * f ^ (n + m) = x * f ^ n * f ^ m + y * f ^ m * f ^ n` using `by ring`. Rewrite using `[this]`. Conclude with `add_mem (mul_mem hn (pow_mem hf m)) (mul_mem hm (pow_mem hf n))`. Consider the case `mul x y _ _ hx hy`. Take `⟨n, hn⟩` from `hx`.

Take `⟨m, hm⟩` from `hy`. Use `⟨n + m, ?_⟩` and prove the remaining obligations. Establish `: x * y * f ^ (n + m) = x * f ^ n * (y * f ^ m)` using `by ring`. Rewrite using `[this]`. Conclude with `mul_mem hn hm`.
-/
theorem exists_mul_pow_mem (T : Set Ω) {f : Ω} (hf0 : f ≠ 0) {x : Ω}
    (hx : x ∈ Algebra.adjoin ℚ (insert f⁻¹ T)) (hf : f ∈ Algebra.adjoin ℚ T) :
    ∃ n : ℕ, x * f ^ n ∈ Algebra.adjoin ℚ T := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ⟨1, by simpa [hf0] using (Algebra.adjoin ℚ T).one_mem⟩
    · exact ⟨0, by simpa using Algebra.subset_adjoin hx⟩
  | algebraMap r => exact ⟨0, by simpa using (Algebra.adjoin ℚ T).algebraMap_mem r⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : (x + y) * f ^ (n + m) = x * f ^ n * f ^ m + y * f ^ m * f ^ n := by ring
    rw [this]
    exact add_mem (mul_mem hn (pow_mem hf m)) (mul_mem hm (pow_mem hf n))
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : x * y * f ^ (n + m) = x * f ^ n * (y * f ^ m) := by ring
    rw [this]
    exact mul_mem hn hm

/- English proof (translation)
Use `letI := (Subalgebra.inclusion hle).toRingHom.toAlgebra`. Establish `hmap : ∀ a : A, ((algebraMap A S a : S) : Ω) = a` using `fun a => rfl`. Establish `hunit : IsUnit (algebraMap A S f)`. Use `IsUnit.of_mul_eq_one (⟨(f : Ω)⁻¹, hinv⟩ : S) ?_` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[Subalgebra.coe_mul, hmap]`. Conclude with `mul_inv_cancel₀ hf0`. Use `IsLocalization.Away.mk _ hunit ?_ ?_` and prove the remaining obligations. Introduce and unpack `⟨x, hx⟩`. Take `⟨n, hn⟩` from `hs x hx`.

Use `⟨n, ⟨x * (f : Ω) ^ n, hn⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hmap, Subalgebra.coe_mul, Subalgebra.coe_pow, hmap]`. Introduce `a b hab`. Use `⟨0, ?_⟩` and prove the remaining obligations.

Establish `: (a : Ω) = b` using `by rw [← hmap a, ← hmap b, hab]`. Rewrite using `[Subtype.ext this]`.
-/
theorem isLocalization_away (A S : Subalgebra ℚ Ω) (hle : A ≤ S) (f : A) (hf0 : (f : Ω) ≠ 0)
    (hinv : (f : Ω)⁻¹ ∈ S) (hs : ∀ x ∈ S, ∃ n : ℕ, x * (f : Ω) ^ n ∈ A) :
    @IsLocalization.Away A _ f S _ (Subalgebra.inclusion hle).toRingHom.toAlgebra := by
  letI := (Subalgebra.inclusion hle).toRingHom.toAlgebra
  have hmap : ∀ a : A, ((algebraMap A S a : S) : Ω) = a := fun a => rfl
  have hunit : IsUnit (algebraMap A S f) := by
    refine IsUnit.of_mul_eq_one (⟨(f : Ω)⁻¹, hinv⟩ : S) ?_
    apply Subtype.ext
    rw [Subalgebra.coe_mul, hmap]
    exact mul_inv_cancel₀ hf0
  refine IsLocalization.Away.mk _ hunit ?_ ?_
  · rintro ⟨x, hx⟩
    obtain ⟨n, hn⟩ := hs x hx
    refine ⟨n, ⟨x * (f : Ω) ^ n, hn⟩, ?_⟩
    apply Subtype.ext
    rw [hmap, Subalgebra.coe_mul, Subalgebra.coe_pow, hmap]
  · intro a b hab
    refine ⟨0, ?_⟩
    have : (a : Ω) = b := by rw [← hmap a, ← hmap b, hab]
    rw [Subtype.ext this]

/- English proof (translation)
Set `s : Set A` to `{x | (x : Ω) ≠ 0 ∧ ∃ l, (x : Ω) = f l}`. Establish `hspan : Ideal.span s = ⊤`. Rewrite using `[Ideal.eq_top_iff_one]`. Establish `h1 : (1 : A) = ∑ l, (⟨a l, ha l⟩ : A) * (⟨f l, hf l⟩ : A)`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[Subalgebra.coe_one, ← hsum, AddSubmonoidClass.coe_finset_sum]`. Both sides reduce to the same expression. Rewrite using `[h1]`. Use `Ideal.sum_mem _ fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `h0 : f l = 0`.

Establish `: (⟨f l, hf l⟩ : A) = 0` using `Subtype.ext h0`. Rewrite using `[this, mul_zero]`. Conclude with `Ideal.zero_mem _`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨h0, l, rfl⟩)`. Rewrite using `[← RingHom.smooth_algebraMap]`.

Use `RingHom.OfLocalizationSpanTarget.ofIsLocalization RingHom.Smooth.ofLocalizationSpanTarget RingHom.Smooth.respectsIso _ s hspan ?_` and prove the remaining obligations. Introduce and unpack `⟨x, hx0, l, hl⟩`. Establish `hx0' : f l ≠ 0` using `hl ▸ hx0`. Use `letI alg := (Subalgebra.inclusion (hle l)).toRingHom.toAlgebra`. Establish `hloc : IsLocalization.Away x (S l)` using `isLocalization_away A (S l) (hle l) x hx0 (hl ▸ hinv l hx0') (hl ▸ hs l hx0')`.

Use `⟨S l, inferInstance, alg, hloc, ?_⟩` and prove the remaining obligations. Establish `hcomp : (algebraMap A (S l)).comp (algebraMap ℚ A) = algebraMap ℚ (S l)` using `Subsingleton.elim _ _`. Rewrite using `[hcomp]`. Conclude with `RingHom.smooth_algebraMap.mpr (hsm l hx0')`.
-/
theorem smooth_of_cover (A : Subalgebra ℚ Ω) {m : ℕ} (f a : Fin m → Ω) (hf : ∀ l, f l ∈ A) (ha : ∀ l, a l ∈ A)
    (hsum : ∑ l, a l * f l = 1) (S : Fin m → Subalgebra ℚ Ω) (hle : ∀ l, A ≤ S l)
    (hinv : ∀ l, f l ≠ 0 → (f l)⁻¹ ∈ S l) (hs : ∀ l, f l ≠ 0 → ∀ x ∈ S l, ∃ n : ℕ, x * f l ^ n ∈ A)
    (hsm : ∀ l, f l ≠ 0 → Algebra.Smooth ℚ (S l)) : Algebra.Smooth ℚ A := by
  let s : Set A := {x | (x : Ω) ≠ 0 ∧ ∃ l, (x : Ω) = f l}
  have hspan : Ideal.span s = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : A) = ∑ l, (⟨a l, ha l⟩ : A) * (⟨f l, hf l⟩ : A) := by
      apply Subtype.ext
      rw [Subalgebra.coe_one, ← hsum, AddSubmonoidClass.coe_finset_sum]
      rfl
    rw [h1]
    refine Ideal.sum_mem _ fun l _ => ?_
    by_cases h0 : f l = 0
    · have : (⟨f l, hf l⟩ : A) = 0 := Subtype.ext h0
      rw [this, mul_zero]
      exact Ideal.zero_mem _
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨h0, l, rfl⟩)
  rw [← RingHom.smooth_algebraMap]
  refine RingHom.OfLocalizationSpanTarget.ofIsLocalization RingHom.Smooth.ofLocalizationSpanTarget
    RingHom.Smooth.respectsIso _ s hspan ?_
  rintro ⟨x, hx0, l, hl⟩
  have hx0' : f l ≠ 0 := hl ▸ hx0
  letI alg := (Subalgebra.inclusion (hle l)).toRingHom.toAlgebra
  have hloc : IsLocalization.Away x (S l) :=
    isLocalization_away A (S l) (hle l) x hx0 (hl ▸ hinv l hx0') (hl ▸ hs l hx0')
  refine ⟨S l, inferInstance, alg, hloc, ?_⟩
  have hcomp : (algebraMap A (S l)).comp (algebraMap ℚ A) = algebraMap ℚ (S l) := Subsingleton.elim _ _
  rw [hcomp]
  exact RingHom.smooth_algebraMap.mpr (hsm l hx0')

/- English proof (translation)
Introduce `c hc`. Take `⟨m, f, a, hf, ha, hsum, hS⟩` from `h c hc`. Conclude with `smooth_of_cover _ f a hf ha hsum (fun l => Algebra.adjoin ℚ (insert (f l)⁻¹ _)) (fun l => Algebra.adjoin_mono (Set.subset_insert _ _)) (fun l _ => Algebra.subset_adjoin (Set.mem_insert _ _)) (fun l h0 x hx => exists_mul_pow_mem _ h0 hx (hf l)) (fun l h0 => (hS l h0 _ rfl).1)`.
-/
theorem smoothGenericFibreM_of_isSncModel (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type)
    [Field Ω] [Algebra ℚ Ω] (y : (Σ k, J k) → Ω) (e : ℕ) (bd : Ideal (MRing J))
    (h : Cmp.IsSncModel y e bd) : SmoothGenericFibreM y := by
  intro c hc
  obtain ⟨m, f, a, hf, ha, hsum, hS⟩ := h c hc
  exact smooth_of_cover _ f a hf ha hsum (fun l => Algebra.adjoin ℚ (insert (f l)⁻¹ _))
    (fun l => Algebra.adjoin_mono (Set.subset_insert _ _))
    (fun l _ => Algebra.subset_adjoin (Set.mem_insert _ _))
    (fun l h0 x hx => exists_mul_pow_mem _ h0 hx (hf l))
    (fun l h0 => (hS l h0 _ rfl).1)

end GlobalTheory.CompanionTheory.Ar.Cmp.SncSmooth
