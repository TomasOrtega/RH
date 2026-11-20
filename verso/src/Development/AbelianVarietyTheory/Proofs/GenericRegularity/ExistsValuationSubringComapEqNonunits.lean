import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

/- English proof (translation)
Take `⟨W, hW, hloc⟩` from `IsLocalRing.exists_factor_valuationRing (f.comp U.subtype)`. Use `⟨W, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Rewrite using `[ValuationSubring.mem_comap]`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Assume the negation of the conclusion as `hxU`. Establish `hx0 : x ≠ 0` using `fun h => hxU (h ▸ U.zero_mem)`. Establish `hinv : x⁻¹ ∈ U` using `(U.mem_or_inv_mem x).resolve_left hxU`. Establish `hnu : ¬ IsUnit (⟨x⁻¹, hinv⟩ : U)`.

Introduce `hu`. Take `⟨⟨y, hy⟩, hyx⟩` from `isUnit_iff_exists_inv.mp hu`. Establish `hyx' : x⁻¹ * y = 1` using `congrArg Subtype.val hyx`. Establish `: y = x`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `hxU (this ▸ hy)`. Apply `hnu` to reduce the goal to its premises. Apply `(hloc.map_nonunit (⟨x⁻¹, hinv⟩ : U))` to reduce the goal to its premises. Use `isUnit_iff_exists_inv.mpr ⟨⟨f x, hx⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `f x⁻¹ * f x = 1`. Rewrite using `[← map_mul, inv_mul_cancel₀ hx0, map_one]`. Introduce `hx`. Conclude with `hW ⟨x, hx⟩`. Introduce `x hx`.

Take `⟨hxU, hmax⟩` from `(ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).mp hx`. Establish `hfx : f x ∈ W` using `hW ⟨x, hxU⟩`. Establish `key : (⟨f x, hfx⟩ : W) ∈ IsLocalRing.maximalIdeal W`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`.

Apply `(IsLocalRing.mem_maximalIdeal _).mp hmax` to reduce the goal to its premises. Conclude with `hloc.map_nonunit (⟨x, hxU⟩ : U) hu`. Conclude with `(ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).mpr ⟨hfx, key⟩`.
-/
theorem exists_valuationSubring_comap_eq_nonunits {K L : Type} [Field K] [Field L] (f : K →+* L)
    (U : ValuationSubring K) :
    ∃ W : ValuationSubring L, W.comap f = U ∧ ∀ x ∈ U.nonunits, f x ∈ W.nonunits := by
  classical
  obtain ⟨W, hW, hloc⟩ := IsLocalRing.exists_factor_valuationRing (f.comp U.subtype)
  refine ⟨W, ?_, ?_⟩
  · ext x
    rw [ValuationSubring.mem_comap]
    constructor
    · intro hx
      by_contra hxU
      have hx0 : x ≠ 0 := fun h => hxU (h ▸ U.zero_mem)
      have hinv : x⁻¹ ∈ U := (U.mem_or_inv_mem x).resolve_left hxU
      have hnu : ¬ IsUnit (⟨x⁻¹, hinv⟩ : U) := by
        intro hu
        obtain ⟨⟨y, hy⟩, hyx⟩ := isUnit_iff_exists_inv.mp hu
        have hyx' : x⁻¹ * y = 1 := congrArg Subtype.val hyx
        have : y = x := by
          calc y = x * (x⁻¹ * y) := by rw [← _root_.mul_assoc, mul_inv_cancel₀ hx0, _root_.one_mul]
            _ = x := by rw [hyx', _root_.mul_one]
        exact hxU (this ▸ hy)
      apply hnu
      apply (hloc.map_nonunit (⟨x⁻¹, hinv⟩ : U))
      refine isUnit_iff_exists_inv.mpr ⟨⟨f x, hx⟩, ?_⟩
      apply Subtype.ext
      change f x⁻¹ * f x = 1
      rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
    · intro hx
      exact hW ⟨x, hx⟩
  · intro x hx
    obtain ⟨hxU, hmax⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).mp hx
    have hfx : f x ∈ W := hW ⟨x, hxU⟩
    have key : (⟨f x, hfx⟩ : W) ∈ IsLocalRing.maximalIdeal W := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      apply (IsLocalRing.mem_maximalIdeal _).mp hmax
      exact hloc.map_nonunit (⟨x, hxU⟩ : U) hu
    exact (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).mpr ⟨hfx, key⟩

/- English proof (translation)
Establish `hbot : la.asIdeal ≠ ⊥` using `la.ne_bot`. Establish `hprime : la.asIdeal.IsPrime` using `la.isPrime`. Establish `main : ∀ n : ℕ, (n : 𝓞 K) ∈ la.asIdeal → n ≠ 0 → ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ la.asIdeal`. Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`.

Consider the case `_ n ih`. Introduce `hn hn0`. Establish `hn1 : n ≠ 1`. Introduce and unpack `rfl`. Conclude with `hprime.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using hn))`.

Take `⟨p, hp, m, rfl⟩` from `Nat.exists_prime_and_dvd hn1`. Rewrite `hn` using `[Nat.cast_mul]`. Break down `hprime.mem_or_mem hn with h | h` into its components or cases. Conclude with `⟨p, hp, h⟩`. Establish `hm0 : m ≠ 0` using `by rintro rfl; simp at hn0`.

Use `ih m ?_ h hm0` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Conclude with `main _ (Ideal.absNorm_mem la.asIdeal) (by rwa [Ne, Ideal.absNorm_eq_zero_iff])`.
-/
theorem exists_prime_natCast_mem {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ la.asIdeal := by
  classical
  have hbot : la.asIdeal ≠ ⊥ := la.ne_bot
  have hprime : la.asIdeal.IsPrime := la.isPrime
  have main : ∀ n : ℕ, (n : 𝓞 K) ∈ la.asIdeal → n ≠ 0 → ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ la.asIdeal := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn hn0
      have hn1 : n ≠ 1 := by
        rintro rfl
        exact hprime.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using hn))
      obtain ⟨p, hp, m, rfl⟩ := Nat.exists_prime_and_dvd hn1
      rw [Nat.cast_mul] at hn
      rcases hprime.mem_or_mem hn with h | h
      · exact ⟨p, hp, h⟩
      · have hm0 : m ≠ 0 := by rintro rfl; simp at hn0
        refine ih m ?_ h hm0
        calc m = 1 * m := (_root_.one_mul m).symm
          _ < p * m := Nat.mul_lt_mul_of_pos_right hp.one_lt (Nat.pos_of_ne_zero hm0)
  exact main _ (Ideal.absNorm_mem la.asIdeal) (by rwa [Ne, Ideal.absNorm_eq_zero_iff])

/- English proof (translation)
Introduce `hI E _ _ _ H Dw hpq Xo l c la hgood`. Take `⟨-, hI⟩` from `hI`. Take `⟨Y, hY, -⟩` from `hI E H Dw hpq Xo`. Unfold `ModelAt`. Take `⟨p, hp, hpla⟩` from `exists_prime_natCast_mem la`.

Take `⟨W, hcomap, hnon⟩` from `exists_valuationSubring_comap_eq_nonunits c.F.val.toRingHom (la.valuation c.F).valuationSubring`. Establish `hlt : la.valuation c.F (p : c.F) < 1`. Establish `h` using `(la.valuation_lt_one_iff_mem (K := c.F) (p : 𝓞 c.F)).mpr hpla`. Conclude with `h` after adjusting the coercions. Establish `hp0 : (p : c.F) ≠ 0` using `Nat.cast_ne_zero.mpr hp.ne_zero`.

Establish `hpU : (p : c.F) ∈ (la.valuation c.F).valuationSubring.nonunits`. Rewrite using `[ValuationSubring.mem_nonunits_iff_or]`. Use `right`. Introduce `hinv`. Rewrite `hinv` using `[Valuation.mem_valuationSubring_iff, map_inv₀]`.

Establish `hpos : 0 < la.valuation c.F (p : c.F)` using `zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hp0)`. Conclude with `absurd ((inv_le_one₀ hpos).mp hinv) (not_le.mpr hlt)`. Establish `hW : (p : ℂ) ∈ W.nonunits`. Establish `h` using `hnon _ hpU`. Rewrite `h` using `[map_natCast]`. Then use the resulting hypothesis.

Set `i : Idx H p` to `⟨l, c, hgood p hp hpla⟩`. Rewrite using `[← hcomap]`. Conclude with `⟨Y p W hp hW i, ((hY p W hp hW).1.1 i).2.2.1⟩`.
-/
theorem modelAt_of_good_level : PartI → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (Xo : ∀ l : Level H, Moduli Dw l) (l : Level H) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)), (∀ p : ℕ, p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p) → ModelAt (Xo l) c la := by
  intro hI E _ _ _ H Dw hpq Xo l c la hgood
  obtain ⟨-, hI⟩ := hI
  obtain ⟨Y, hY, -⟩ := hI E H Dw hpq Xo
  unfold ModelAt
  obtain ⟨p, hp, hpla⟩ := exists_prime_natCast_mem la
  obtain ⟨W, hcomap, hnon⟩ :=
    exists_valuationSubring_comap_eq_nonunits c.F.val.toRingHom (la.valuation c.F).valuationSubring
  have hlt : la.valuation c.F (p : c.F) < 1 := by
    have h := (la.valuation_lt_one_iff_mem (K := c.F) (p : 𝓞 c.F)).mpr hpla
    exact_mod_cast h
  have hp0 : (p : c.F) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpU : (p : c.F) ∈ (la.valuation c.F).valuationSubring.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or]
    right
    intro hinv
    rw [Valuation.mem_valuationSubring_iff, map_inv₀] at hinv
    have hpos : 0 < la.valuation c.F (p : c.F) :=
      zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hp0)
    exact absurd ((inv_le_one₀ hpos).mp hinv) (not_le.mpr hlt)
  have hW : (p : ℂ) ∈ W.nonunits := by
    have h := hnon _ hpU
    rwa [map_natCast] at h
  let i : Idx H p := ⟨l, c, hgood p hp hpla⟩
  rw [← hcomap]
  exact ⟨Y p W hp hW i, ((hY p W hp hW).1.1 i).2.2.1⟩

end GlobalTheory.Reg
