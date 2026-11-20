import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SzPeriodsOfTangent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyOfForall

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PlaceRingExists

/- English proof (translation)
Establish `h1 : IsIntegral (NormedField.valuation (K` using `ℂ_[q])).integer x := hx.tower_top`. Establish `h2` using `(Valuation.integer.integers (NormedField.valuation (K := ℂ_[q]))).mem_of_integral h1`. Establish `h3 : ‖x‖₊ ≤ 1` using `h2`. Conclude with `h3` after adjusting the coercions.
-/
theorem norm_le_one_of_isIntegral_int {q : ℕ} [Fact q.Prime] {x : ℂ_[q]} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[q])).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[q]))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

/- English proof (translation)
Establish `e : ((q : ℕ) : ℂ_[q]) = ((algebraMap ℚ_[q] (PadicAlgCl q) (q : ℚ_[q]) : PadicAlgCl q) : ℂ_[q])` using `by simp`. Rewrite using `[e, PadicComplex.norm_extends', Padic.norm_p]`. Conclude with `inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : q.Prime).one_lt)`.
-/
theorem norm_prime_lt_one (q : ℕ) [Fact q.Prime] : ‖((q : ℕ) : ℂ_[q])‖ < 1 := by
  have e : ((q : ℕ) : ℂ_[q]) = ((algebraMap ℚ_[q] (PadicAlgCl q) (q : ℚ_[q]) : PadicAlgCl q) : ℂ_[q]) := by simp
  rw [e, PadicComplex.norm_extends', Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : q.Prime).one_lt)

/- English proof (translation)
Introduce `l _ lam k hk`. Use `haveI : NumberField k := { }`. Establish `hle : k ≤ algebraicClosure ℚ ℂ` using `fun x hx => mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (⟨x, hx⟩ : k)).algHom k.val)`. Set `f : k →+* ℂ_[l]` to `lam.comp (IntermediateField.inclusion hle).toRingHom`. Establish `hO : ∀ a : 𝓞 k, ‖f a‖ ≤ 1` using `fun a => norm_le_one_of_isIntegral_int (by`.

Apply the tactic sequence `convert map_isIntegral_int f (NumberField.RingOfIntegers.isIntegral_coe a) using 1 <;> first | exact Subsingleton.elim _ _ | rfl)`. Set `P : Ideal (𝓞 k)` to `{ carrier := {a | ‖f a‖ < 1} add_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq, map_add] at *`. Conclude with `lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)`. Use the proof step `zero_mem' := by simp`.

Use the proof step `smul_mem' := fun c a ha => by`. Simplify using `only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at *`. Combine the equalities or inequalities in the displayed calculation. Establish `hmemP : ∀ a, a ∈ P ↔ ‖f a‖ < 1` using `fun _ => Iff.rfl`. Establish `hPp : P.IsPrime`.

Use `⟨?_, fun {a b} hab => ?_⟩` and prove the remaining obligations. Rewrite using `[Ne, Ideal.eq_top_iff_one, hmemP]`. Simplify using the standard rewrite rules. Establish `e : ((a * b : 𝓞 k) : k) = (a : k) * b` using `rfl`. Rewrite `hab` using `[hmemP, e, map_mul, norm_mul]`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Rewrite `h` using `[hmemP, hmemP, not_lt, not_lt]`. Use polynomial arithmetic with `[hO a, hO b]`. Establish `hlP : ((l : ℕ) : 𝓞 k) ∈ P`.

Establish `e : (((l : ℕ) : 𝓞 k) : k) = ((l : ℕ) : k)` using `by simp`. Rewrite using `[hmemP, e, map_natCast]`. Conclude with `norm_prime_lt_one l`. Establish `hP0 : P ≠ ⊥`. Introduce `h`.

Rewrite `hlP` using `[h, Ideal.mem_bot, Nat.cast_eq_zero]`. Conclude with `(Fact.out : l.Prime).ne_zero hlP`. Establish `hS : P.primeCompl ≤ nonZeroDivisors (𝓞 k)` using `Ideal.primeCompl_le_nonZeroDivisors _`. Set `A` to `Localization.subalgebra.ofField k P.primeCompl hS`. Use `haveI : IsLocalization.AtPrime A P := Localization.subalgebra.isLocalization_ofField k _ hS`.

Use `haveI : IsDiscreteValuationRing A := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 k) hP0 A`. Use `haveI : IsFractionRing A k := Localization.subalgebra.isFractionRing_ofField k _ hS`. Establish `hS1 : ∀ s : 𝓞 k, s ∈ P.primeCompl → ‖f s‖ = 1` using `fun s hs => le_antisymm (hO s) (not_lt.1 hs)`. Establish `hA : ∀ x : k, x ∈ A ↔ ‖f x‖ ≤ 1`. Introduce `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, s, hs, rfl⟩`. Rewrite using `[map_mul, map_inv₀, norm_mul, norm_inv]`. Express the relevant statement in the definitionally equal form `‖f (r : k)‖ * ‖f (s : k)‖⁻¹ ≤ 1`. Rewrite using `[hS1 s hs, inv_one, _root_.mul_one]`.

Conclude with `hO r`. Introduce `hx`. Distinguish the cases in `hx0 : x = 0`. Rewrite using `[hx0]`. Conclude with `zero_mem A`.

Break down `ValuationRing.isInteger_or_isInteger A x with ⟨a, ha⟩ | ⟨a, ha⟩` into its components or cases. Rewrite using `[← ha]`. Conclude with `a.2`. Take `⟨r, s, hs, hrs⟩` from `a.2`. Establish `ha' : (a : k) = x⁻¹` using `ha`.

Rewrite `hrs` using `[ha']`. Establish `hs0 : (s : k) ≠ 0`. Introduce `h0`. Apply `hs` to reduce the goal to its premises. Rewrite using `[show s = 0 from RingOfIntegers.coe_eq_zero_iff.1 h0]`.

Conclude with `P.zero_mem`. Establish `hr0 : (r : k) ≠ 0`. Introduce `h0`. Establish `h0' : algebraMap (𝓞 k) k r = 0` using `h0`. Rewrite `hrs` using `[h0', zero_mul, inv_eq_zero]`.

Conclude with `hx0 hrs`. Establish `hxe : x = (s : k) * (r : k)⁻¹`. Rewrite using `[← inv_inv x, hrs, mul_inv, inv_inv, mul_comm]`. Establish `hr1 : ‖f r‖ = 1`. Use `le_antisymm (hO r) ?_` and prove the remaining obligations.

Use `hx` as an intermediate fact. Rewrite `this` using `[hxe, map_mul, map_inv₀, norm_mul, norm_inv]`. Express the relevant statement in the definitionally equal form `‖f (s : k)‖ * ‖f (r : k)‖⁻¹ ≤ 1 at this`. Rewrite `this` using `[hS1 s hs, _root_.one_mul]`. Establish `hpos : 0 < ‖f (r : k)‖` using `norm_pos_iff.2 ((map_ne_zero f).2 hr0)`.

Rewrite `this` using `[inv_le_one₀ hpos]`. Then use the resulting hypothesis. Conclude with `⟨s, r, fun h => by have h' := (hmemP r).1 h; rw [hr1] at h'; exact lt_irrefl _ h', hxe⟩`. Set `g : k →+* ℂ` to `k.val.toRingHom`. Set `R : Subring ℂ` to `A.toSubring.map g`. Set `e : A.toSubring ≃+* R` to `Subring.equivMapOfInjective A.toSubring g g.injective`.

Use `haveI : IsDiscreteValuationRing A.toSubring := inferInstanceAs (IsDiscreteValuationRing A)`. Use `haveI : IsDiscreteValuationRing R := IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e`. Use `⟨R, this, ?_, ?_⟩` and prove the remaining obligations. Introduce `z hz`. Take `⟨x, hxA, rfl⟩` from `Subring.mem_map.1 hz`.

Use `⟨hle x.2, ?_⟩` and prove the remaining obligations. Rewrite using `[Real.rpow_zero]`. Conclude with `(hA x).1 hxA`. Introduce and unpack `z hz ⟨h, hn⟩`. Rewrite `hn` using `[Real.rpow_zero]`.

Conclude with `Subring.mem_map.2 ⟨⟨z, hz⟩, (hA _).2 hn, rfl⟩`.
-/
theorem exists_isPlaceOver : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (k : IntermediateField ℚ ℂ), FiniteDimensional ℚ k →
    ∃ R : Subring ℂ, IsPlaceOver l lam k R := by
  intro l _ lam k hk
  haveI : NumberField k := { }
  have hle : k ≤ algebraicClosure ℚ ℂ := fun x hx =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (⟨x, hx⟩ : k)).algHom k.val)
  let f : k →+* ℂ_[l] := lam.comp (IntermediateField.inclusion hle).toRingHom
  have hO : ∀ a : 𝓞 k, ‖f a‖ ≤ 1 := fun a =>
    norm_le_one_of_isIntegral_int (by
      convert map_isIntegral_int f (NumberField.RingOfIntegers.isIntegral_coe a) using 1 <;>
        first | exact Subsingleton.elim _ _ | rfl)
  let P : Ideal (𝓞 k) :=
    { carrier := {a | ‖f a‖ < 1}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add] at *
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c a ha => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at *
        calc ‖f c‖ * ‖f a‖ ≤ 1 * ‖f a‖ := by gcongr; exact hO c
          _ < 1 := by simpa using ha }
  have hmemP : ∀ a, a ∈ P ↔ ‖f a‖ < 1 := fun _ => Iff.rfl
  have hPp : P.IsPrime := by
    refine ⟨?_, fun {a b} hab => ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one, hmemP]; simp
    · have e : ((a * b : 𝓞 k) : k) = (a : k) * b := rfl
      rw [hmemP, e, map_mul, norm_mul] at hab
      by_contra h
      push_neg at h
      rw [hmemP, hmemP, not_lt, not_lt] at h
      nlinarith [hO a, hO b]
  have hlP : ((l : ℕ) : 𝓞 k) ∈ P := by
    have e : (((l : ℕ) : 𝓞 k) : k) = ((l : ℕ) : k) := by simp
    rw [hmemP, e, map_natCast]; exact norm_prime_lt_one l
  have hP0 : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at hlP
    exact (Fact.out : l.Prime).ne_zero hlP
  have hS : P.primeCompl ≤ nonZeroDivisors (𝓞 k) := Ideal.primeCompl_le_nonZeroDivisors _
  let A := Localization.subalgebra.ofField k P.primeCompl hS
  haveI : IsLocalization.AtPrime A P := Localization.subalgebra.isLocalization_ofField k _ hS
  haveI : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 k) hP0 A
  haveI : IsFractionRing A k := Localization.subalgebra.isFractionRing_ofField k _ hS
  have hS1 : ∀ s : 𝓞 k, s ∈ P.primeCompl → ‖f s‖ = 1 := fun s hs =>
    le_antisymm (hO s) (not_lt.1 hs)
  have hA : ∀ x : k, x ∈ A ↔ ‖f x‖ ≤ 1 := by
    intro x
    constructor
    · rintro ⟨r, s, hs, rfl⟩
      rw [map_mul, map_inv₀, norm_mul, norm_inv]
      change ‖f (r : k)‖ * ‖f (s : k)‖⁻¹ ≤ 1
      rw [hS1 s hs, inv_one, _root_.mul_one]; exact hO r
    · intro hx
      by_cases hx0 : x = 0
      · rw [hx0]; exact zero_mem A
      rcases ValuationRing.isInteger_or_isInteger A x with ⟨a, ha⟩ | ⟨a, ha⟩
      · rw [← ha]; exact a.2
      · obtain ⟨r, s, hs, hrs⟩ := a.2
        have ha' : (a : k) = x⁻¹ := ha
        rw [ha'] at hrs
        have hs0 : (s : k) ≠ 0 := by
          intro h0; apply hs; rw [show s = 0 from RingOfIntegers.coe_eq_zero_iff.1 h0]; exact P.zero_mem
        have hr0 : (r : k) ≠ 0 := by
          intro h0
          have h0' : algebraMap (𝓞 k) k r = 0 := h0
          rw [h0', zero_mul, inv_eq_zero] at hrs; exact hx0 hrs
        have hxe : x = (s : k) * (r : k)⁻¹ := by
          rw [← inv_inv x, hrs, mul_inv, inv_inv, mul_comm]
        have hr1 : ‖f r‖ = 1 := by
          refine le_antisymm (hO r) ?_
          have := hx
          rw [hxe, map_mul, map_inv₀, norm_mul, norm_inv] at this
          change ‖f (s : k)‖ * ‖f (r : k)‖⁻¹ ≤ 1 at this
          rw [hS1 s hs, _root_.one_mul] at this
          have hpos : 0 < ‖f (r : k)‖ := norm_pos_iff.2 ((map_ne_zero f).2 hr0)
          rwa [inv_le_one₀ hpos] at this
        exact ⟨s, r, fun h => by have h' := (hmemP r).1 h; rw [hr1] at h'; exact lt_irrefl _ h', hxe⟩

  let g : k →+* ℂ := k.val.toRingHom
  let R : Subring ℂ := A.toSubring.map g
  let e : A.toSubring ≃+* R := Subring.equivMapOfInjective A.toSubring g g.injective
  haveI : IsDiscreteValuationRing A.toSubring := inferInstanceAs (IsDiscreteValuationRing A)
  haveI : IsDiscreteValuationRing R := IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  refine ⟨R, this, ?_, ?_⟩
  · intro z hz
    obtain ⟨x, hxA, rfl⟩ := Subring.mem_map.1 hz
    refine ⟨hle x.2, ?_⟩
    rw [Real.rpow_zero]
    exact (hA x).1 hxA
  · rintro z hz ⟨h, hn⟩
    rw [Real.rpow_zero] at hn
    exact Subring.mem_map.2 ⟨⟨z, hz⟩, (hA _).2 hn, rfl⟩

end GlobalTheory.PlaceRingExists
