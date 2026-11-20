import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.GenericMap

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.CharTie

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {q : Cpt ξ}

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.GenericMap.main h n hn`.
-/
theorem unit_natCast (h : Char0 ξ q) (n : ℕ) (hn : n ≠ 0) : unitAt ξ q (n : Ω) :=
  _root_.UpperTheory.Reformulated.B.GenericMap.main h n hn

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h d hd`. Establish `hreg : ∀ b : 𝓞 F, algebraMap (𝓞 F) Ω b ∈ regAt ξ p`. Introduce `b`. Take `⟨c, hc⟩` from `ht.cover p`.

Conclude with `(ht.ring c hc.1 _).1 (Subalgebra.algebraMap_mem _ b) p hc`. Establish `hn : Ideal.absNorm (Ideal.span {d}) ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`. Conclude with `hd`. Take `⟨d', hd'⟩` from `Ideal.mem_span_singleton.1 (Ideal.absNorm_mem (Ideal.span {d}))`.

Establish `hu` using `unit_natCast h _ hn`. Establish `e : ((Ideal.absNorm (Ideal.span {d}) : ℕ) : Ω) = algebraMap (𝓞 F) Ω d * algebraMap (𝓞 F) Ω d'`. Rewrite using `[← map_mul, ← hd', map_natCast]`. Rewrite `hu` using `[e]`. Establish `ha : algebraMap (𝓞 F) Ω d ≠ 0` using `left_ne_zero_of_mul hu.1`.

Establish `hb : algebraMap (𝓞 F) Ω d' ≠ 0` using `right_ne_zero_of_mul hu.1`. Use `⟨ha, hreg d, ?_⟩` and prove the remaining obligations. Establish `e2 : (algebraMap (𝓞 F) Ω d)⁻¹ = algebraMap (𝓞 F) Ω d' * (algebraMap (𝓞 F) Ω d * algebraMap (𝓞 F) Ω d')⁻¹`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e2]`.

Conclude with `mul_mem (hreg d') hu.2.2`. Introduce `h r hr hf`. Establish `hr0 : (r : 𝓞 F) ≠ 0` using `Nat.cast_ne_zero.2 hr.ne_zero`. Use `h _ hr0` as an intermediate fact. Rewrite `this` using `[map_natCast]`.

Conclude with `hf this`.
-/
theorem char_zero_iff_integers_units (F : Type) [Field F] [NumberField F] (Ω : Type) [Field Ω] [Algebra (𝓞 F) Ω]
    (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (κ : Type) (t : κ → Ω) (ht : CoordTie (𝓞 F) ξ t) (p : Cpt ξ) :
    Char0 ξ p ↔ ∀ d : 𝓞 F, d ≠ 0 → unitAt ξ p (algebraMap (𝓞 F) Ω d) := by
  constructor
  · intro h d hd
    have hreg : ∀ b : 𝓞 F, algebraMap (𝓞 F) Ω b ∈ regAt ξ p := by
      intro b
      obtain ⟨c, hc⟩ := ht.cover p
      exact (ht.ring c hc.1 _).1 (Subalgebra.algebraMap_mem _ b) p hc
    have hn : Ideal.absNorm (Ideal.span {d}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hd
    obtain ⟨d', hd'⟩ := Ideal.mem_span_singleton.1 (Ideal.absNorm_mem (Ideal.span {d}))
    have hu := unit_natCast h _ hn
    have e : ((Ideal.absNorm (Ideal.span {d}) : ℕ) : Ω) = algebraMap (𝓞 F) Ω d * algebraMap (𝓞 F) Ω d' := by
      rw [← map_mul, ← hd', map_natCast]
    rw [e] at hu
    have ha : algebraMap (𝓞 F) Ω d ≠ 0 := left_ne_zero_of_mul hu.1
    have hb : algebraMap (𝓞 F) Ω d' ≠ 0 := right_ne_zero_of_mul hu.1
    refine ⟨ha, hreg d, ?_⟩
    have e2 : (algebraMap (𝓞 F) Ω d)⁻¹ =
        algebraMap (𝓞 F) Ω d' * (algebraMap (𝓞 F) Ω d * algebraMap (𝓞 F) Ω d')⁻¹ := by
      field_simp
    rw [e2]
    exact mul_mem (hreg d') hu.2.2
  · intro h r hr hf
    have hr0 : (r : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 hr.ne_zero
    have := h _ hr0
    rw [map_natCast] at this
    exact hf this

end GlobalTheory.CompanionTheory.Ar.SncBase.CharTie
