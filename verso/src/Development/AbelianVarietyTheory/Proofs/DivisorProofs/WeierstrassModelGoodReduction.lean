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
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumUnramifiedAlmostAll

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PlaceRingCurve

/- English proof (translation)
Introduce `l _ lam k hk`. Use `haveI : NumberField k := { }`. Establish `hle : k ≤ algebraicClosure ℚ ℂ` using `fun x hx => mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (⟨x, hx⟩ : k)).algHom k.val)`. Set `f : k →+* ℂ_[l]` to `lam.comp (IntermediateField.inclusion hle).toRingHom`. Establish `hO : ∀ a : 𝓞 k, ‖f a‖ ≤ 1` using `fun a => GlobalTheory.PlaceRingExists.norm_le_one_of_isIntegral_int (by`.

Apply the tactic sequence `convert map_isIntegral_int f (NumberField.RingOfIntegers.isIntegral_coe a) using 1 <;> first | exact Subsingleton.elim _ _ | rfl)`. Set `P : Ideal (𝓞 k)` to `{ carrier := {a | ‖f a‖ < 1} add_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq, map_add] at *`. Conclude with `lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)`. Use the proof step `zero_mem' := by simp`.

Use the proof step `smul_mem' := fun c a ha => by`. Simplify using `only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at *`. Combine the equalities or inequalities in the displayed calculation. Establish `hmemP : ∀ a, a ∈ P ↔ ‖f a‖ < 1` using `fun _ => Iff.rfl`. Establish `hPp : P.IsPrime`.

Use `⟨?_, fun {a b} hab => ?_⟩` and prove the remaining obligations. Rewrite using `[Ne, Ideal.eq_top_iff_one, hmemP]`. Simplify using the standard rewrite rules. Establish `e : ((a * b : 𝓞 k) : k) = (a : k) * b` using `rfl`. Rewrite `hab` using `[hmemP, e, map_mul, norm_mul]`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Rewrite `h` using `[hmemP, hmemP, not_lt, not_lt]`. Use polynomial arithmetic with `[hO a, hO b]`. Establish `hlP : ((l : ℕ) : 𝓞 k) ∈ P`.

Establish `e : (((l : ℕ) : 𝓞 k) : k) = ((l : ℕ) : k)` using `by simp`. Rewrite using `[hmemP, e, map_natCast]`. Conclude with `GlobalTheory.PlaceRingExists.norm_prime_lt_one l`. Establish `hP0 : P ≠ ⊥`. Introduce `h`.

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

Use `haveI : IsDiscreteValuationRing A.toSubring := inferInstanceAs (IsDiscreteValuationRing A)`. Use `haveI : IsDiscreteValuationRing R := IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e`. Use `⟨R, ⟨this, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `z hz`. Take `⟨x, hxA, rfl⟩` from `Subring.mem_map.1 hz`.

Use `⟨hle x.2, ?_⟩` and prove the remaining obligations. Rewrite using `[Real.rpow_zero]`. Conclude with `(hA x).1 hxA`. Introduce and unpack `z hz ⟨h, hn⟩`. Rewrite `hn` using `[Real.rpow_zero]`.

Conclude with `Subring.mem_map.2 ⟨⟨z, hz⟩, (hA _).2 hn, rfl⟩`. Introduce `z hz`. Take `⟨x, -, rfl⟩` from `Subring.mem_map.1 hz`. Conclude with `x.2`.
-/
theorem exists_isPlaceOver_le : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (k : IntermediateField ℚ ℂ),
    FiniteDimensional ℚ k → ∃ R : Subring ℂ, IsPlaceOver l lam k R ∧ ∀ x ∈ R, x ∈ k := by
  intro l _ lam k hk
  haveI : NumberField k := { }
  have hle : k ≤ algebraicClosure ℚ ℂ := fun x hx =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (⟨x, hx⟩ : k)).algHom k.val)
  let f : k →+* ℂ_[l] := lam.comp (IntermediateField.inclusion hle).toRingHom
  have hO : ∀ a : 𝓞 k, ‖f a‖ ≤ 1 := fun a =>
    GlobalTheory.PlaceRingExists.norm_le_one_of_isIntegral_int (by
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
    rw [hmemP, e, map_natCast]; exact GlobalTheory.PlaceRingExists.norm_prime_lt_one l
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
  refine ⟨R, ⟨this, ?_, ?_⟩, ?_⟩
  · intro z hz
    obtain ⟨x, hxA, rfl⟩ := Subring.mem_map.1 hz
    refine ⟨hle x.2, ?_⟩
    rw [Real.rpow_zero]
    exact (hA x).1 hxA
  · rintro z hz ⟨h, hn⟩
    rw [Real.rpow_zero] at hn
    exact Subring.mem_map.2 ⟨⟨z, hz⟩, (hA _).2 hn, rfl⟩
  · intro z hz
    obtain ⟨x, -, rfl⟩ := Subring.mem_map.1 hz
    exact x.2

/- English proof (translation)
Establish `e : ((n : ℕ) : ℂ_[l]) = ((algebraMap ℚ_[l] (PadicAlgCl l) (n : ℚ_[l]) : PadicAlgCl l) : ℂ_[l])` using `by simp`. Rewrite using `[e, PadicComplex.norm_extends', Padic.norm_natCast_eq_one_iff]`. Conclude with `h`.
-/
theorem norm_natCast_eq_one {l : ℕ} [Fact l.Prime] {n : ℕ} (h : l.Coprime n) : ‖((n : ℕ) : ℂ_[l])‖ = 1 := by
  have e : ((n : ℕ) : ℂ_[l]) = ((algebraMap ℚ_[l] (PadicAlgCl l) (n : ℚ_[l]) : PadicAlgCl l) : ℂ_[l]) := by simp
  rw [e, PadicComplex.norm_extends', Padic.norm_natCast_eq_one_iff]
  exact h

/- English proof (translation)
The claim follows from `IsUltrametricDist.norm_natCast_le_one _ n`.
-/
theorem norm_natCast_le {l : ℕ} [Fact l.Prime] (n : ℕ) : ‖((n : ℕ) : ℂ_[l])‖ ≤ 1 :=
  IsUltrametricDist.norm_natCast_le_one _ n

/- English proof (translation)
Rewrite using `[IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]`.
-/
theorem norm_add_of_lt {l : ℕ} [Fact l.Prime] {x y : ℂ_[l]} (h : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

/- English proof (translation)
Establish `h3 : ‖(3 : ℂ_[l])‖ = 1`. Conclude with `norm_natCast_eq_one (l := l) (n := 3) ((Nat.coprime_primes Fact.out Nat.prime_three).2 hl)` after adjusting the coercions. Establish `h24 : ‖(-24 : ℂ_[l])‖ ≤ 1` using `by rw [norm_neg]; exact_mod_cast norm_natCast_le (l := l) 24`. Establish `h27 : ‖(27 : ℂ_[l])‖ = 1` using `by rw [show (27 : ℂ_[l]) = 3 ^ 3 by norm_num, norm_pow, h3, one_pow]`. Establish `hn` using `congrArg norm h`.

Rewrite `hn` using `[mul_pow, norm_mul, norm_mul, norm_pow (a ^ 3 - 24)]`. Prove the components needed by the constructor for the conclusion. Assume the negation of the conclusion as `ha`. Establish `ht : 1 < ‖a ^ 3‖` using `by rw [norm_pow]; exact one_lt_pow₀ (not_le.1 ha) (by norm_num)`. Establish `e1 : ‖a ^ 3 - 24‖ = ‖a ^ 3‖` using `by rw [sub_eq_add_neg]; exact norm_add_of_lt (h24.trans_lt ht)`.

Establish `e2 : ‖a ^ 3 - 27‖ = ‖a ^ 3‖`. Rewrite using `[sub_eq_add_neg]; exact norm_add_of_lt (by rw [norm_neg, h27]; exact ht)`. Rewrite `hn` using `[e1, e2]`. Establish `h1 : 1 < ‖a ^ 3‖ ^ 3` using `one_lt_pow₀ ht (by norm_num)`. Use the polynomial consequences of the given equalities and inequalities.

Assume the negation of the conclusion as `hd`. Establish `hd` using `not_le.1 hd`. Establish `e1 : ‖a ^ 3 - 24‖ = 1`. Rewrite using `[show a ^ 3 - 24 = 3 + (a ^ 3 - 27) by ring, norm_add_of_lt (by rw [h3]; exact hd), h3]`. Establish `e2 : ‖a ^ 3‖ = 1`.

Rewrite using `[show a ^ 3 = 27 + (a ^ 3 - 27) by ring, norm_add_of_lt (by rw [h27]; exact hd), h27]`. Rewrite `hn` using `[e1, e2]`. Use polynomial arithmetic with `[norm_nonneg j, norm_nonneg (a ^ 3 - 27)]`.
-/
theorem deuring_norm {l : ℕ} [Fact l.Prime] (hl : l ≠ 3) {a j : ℂ_[l]} (hj : ‖j‖ ≤ 1)
    (h : (a * (a ^ 3 - 24)) ^ 3 = j * (a ^ 3 - 27)) : ‖a‖ ≤ 1 ∧ 1 ≤ ‖a ^ 3 - 27‖ := by
  have h3 : ‖(3 : ℂ_[l])‖ = 1 := by
    exact_mod_cast norm_natCast_eq_one (l := l) (n := 3) ((Nat.coprime_primes Fact.out Nat.prime_three).2 hl)
  have h24 : ‖(-24 : ℂ_[l])‖ ≤ 1 := by rw [norm_neg]; exact_mod_cast norm_natCast_le (l := l) 24
  have h27 : ‖(27 : ℂ_[l])‖ = 1 := by rw [show (27 : ℂ_[l]) = 3 ^ 3 by norm_num, norm_pow, h3, one_pow]
  have hn := congrArg norm h
  rw [mul_pow, norm_mul, norm_mul, norm_pow (a ^ 3 - 24)] at hn
  constructor
  · by_contra ha
    have ht : 1 < ‖a ^ 3‖ := by rw [norm_pow]; exact one_lt_pow₀ (not_le.1 ha) (by norm_num)
    have e1 : ‖a ^ 3 - 24‖ = ‖a ^ 3‖ := by rw [sub_eq_add_neg]; exact norm_add_of_lt (h24.trans_lt ht)
    have e2 : ‖a ^ 3 - 27‖ = ‖a ^ 3‖ := by
      rw [sub_eq_add_neg]; exact norm_add_of_lt (by rw [norm_neg, h27]; exact ht)
    rw [e1, e2] at hn
    have h1 : 1 < ‖a ^ 3‖ ^ 3 := one_lt_pow₀ ht (by norm_num)
    nlinarith
  · by_contra hd
    have hd := not_le.1 hd
    have e1 : ‖a ^ 3 - 24‖ = 1 := by
      rw [show a ^ 3 - 24 = 3 + (a ^ 3 - 27) by ring, norm_add_of_lt (by rw [h3]; exact hd), h3]
    have e2 : ‖a ^ 3‖ = 1 := by
      rw [show a ^ 3 = 27 + (a ^ 3 - 27) by ring, norm_add_of_lt (by rw [h27]; exact hd), h27]
    rw [e1, e2] at hn
    nlinarith [norm_nonneg j, norm_nonneg (a ^ 3 - 27)]

/- English proof (translation)
Establish `h2 : ‖(2 : ℂ_[l])‖ = 1`. Conclude with `norm_natCast_eq_one (l := l) (n := 2) ((Nat.coprime_primes Fact.out Nat.prime_two).2 hl)` after adjusting the coercions. Establish `h16 : ‖(16 : ℂ_[l])‖ = 1` using `by rw [show (16 : ℂ_[l]) = 2 ^ 4 by norm_num, norm_pow, h2, one_pow]`. Establish `hn` using `congrArg norm h`. Simplify using `only [norm_pow, norm_mul (16 : ℂ_[l]), norm_mul j, h16, _root_.one_mul] at hn ⊢`.

Use `set b := a * (a - 1) with hb`. Prove the components needed by the constructor for the conclusion. Assume the negation of the conclusion as `ha`. Establish `ha` using `not_le.1 ha`. Establish `e0 : ‖a - 1‖ = ‖a‖` using `by rw [sub_eq_add_neg]; exact norm_add_of_lt (by rw [norm_neg, norm_one]; exact ha)`.

Establish `ht : 1 < ‖b‖` using `by rw [hb, norm_mul, e0]; nlinarith`. Rewrite `hn` using `[norm_add_of_lt (by rw [norm_one]; exact ht)]`. Establish `h1 : 0 < ‖b‖ ^ 2` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Assume the negation of the conclusion as `hd`.

Establish `hd` using `not_le.1 hd`. Establish `hb1 : ‖b‖ < 1`. Assume the negation of the conclusion as `h'`. Conclude with `absurd hd (not_lt.2 (one_le_pow₀ (not_lt.1 h')))`. Rewrite `hn` using `[add_comm, norm_add_of_lt (by rw [norm_one]; exact hb1), norm_one]`.

Use polynomial arithmetic with `[norm_nonneg j, sq_nonneg ‖b‖]`.
-/
theorem legendre_norm {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) {a j : ℂ_[l]} (hj : ‖j‖ ≤ 1)
    (h : (16 * (a * (a - 1) + 1)) ^ 3 = j * (16 * (a * (a - 1)) ^ 2)) :
    ‖a‖ ≤ 1 ∧ 1 ≤ ‖16 * (a * (a - 1)) ^ 2‖ := by
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by
    exact_mod_cast norm_natCast_eq_one (l := l) (n := 2) ((Nat.coprime_primes Fact.out Nat.prime_two).2 hl)
  have h16 : ‖(16 : ℂ_[l])‖ = 1 := by rw [show (16 : ℂ_[l]) = 2 ^ 4 by norm_num, norm_pow, h2, one_pow]
  have hn := congrArg norm h
  simp only [norm_pow, norm_mul (16 : ℂ_[l]), norm_mul j, h16, _root_.one_mul] at hn ⊢
  set b := a * (a - 1) with hb
  constructor
  · by_contra ha
    have ha := not_le.1 ha
    have e0 : ‖a - 1‖ = ‖a‖ := by rw [sub_eq_add_neg]; exact norm_add_of_lt (by rw [norm_neg, norm_one]; exact ha)
    have ht : 1 < ‖b‖ := by rw [hb, norm_mul, e0]; nlinarith
    rw [norm_add_of_lt (by rw [norm_one]; exact ht)] at hn
    have h1 : 0 < ‖b‖ ^ 2 := by positivity
    nlinarith
  · by_contra hd
    have hd := not_le.1 hd
    have hb1 : ‖b‖ < 1 := by
      by_contra h'
      exact absurd hd (not_lt.2 (one_le_pow₀ (not_lt.1 h')))
    rw [add_comm, norm_add_of_lt (by rw [norm_one]; exact hb1), norm_one] at hn
    nlinarith [norm_nonneg j, sq_nonneg ‖b‖]

/- English proof (translation)
Set `S : Set ℂ` to `{(V.a₁ : ℂ), (V.a₂ : ℂ), (V.a₃ : ℂ), (V.a₄ : ℂ), (V.a₆ : ℂ)}`. Use `haveI : Finite S := (Set.toFinite S).to_subtype`. Establish `hi : ∀ x : algebraicClosure ℚ ℂ, IsIntegral ℚ (x : ℂ)` using `fun x => (mem_algebraicClosure_iff.1 x.2).isIntegral`. Establish `hk : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S)` using `IntermediateField.finiteDimensional_adjoin (by`. Apply the tactic sequence `rintro x (rfl | rfl | rfl | rfl | rfl) <;> exact hi _)`.

Take `⟨R, hR, hRk⟩` from `exists_isPlaceOver_le l lam _ hk`. Establish `hm : ∀ x : algebraicClosure ℚ ℂ, (x : ℂ) ∈ IntermediateField.adjoin ℚ S → ‖lam x‖ ≤ 1 → (x : ℂ) ∈ R` using `fun x hx hn => hR.2.2 _ hx ⟨x.2, by rw [Real.rpow_zero]; exact hn⟩`. Establish `hs : ∀ x ∈ S, x ∈ IntermediateField.adjoin ℚ S` using `fun x hx => IntermediateField.subset_adjoin ℚ S hx`. Set `W : WeierstrassCurve R` to `⟨⟨_, hm _ (hs _ (by simp [S])) h₁⟩, ⟨_, hm _ (hs _ (by simp [S])) h₂⟩, ⟨_, hm _ (hs _ (by simp [S])) h₃⟩, ⟨_, hm _ (hs _ (by simp [S])) h₄⟩, ⟨_, hm _ (hs _ (by simp [S])) h₆⟩⟩`. Establish `hW : W.map R.subtype = V.map (algebraMap (algebraicClosure ℚ ℂ) ℂ)` using `rfl`.

Establish `eΔ : ((W.Δ : R) : ℂ) = (V.Δ : ℂ)`. Use `congrArg WeierstrassCurve.Δ hW` as an intermediate fact. Rewrite `this` using `[WeierstrassCurve.map_Δ, WeierstrassCurve.map_Δ]`. Then use the resulting hypothesis. Establish `ec : ((W.c₄ : R) : ℂ) = (V.c₄ : ℂ)`. Use `congrArg WeierstrassCurve.c₄ hW` as an intermediate fact.

Rewrite `this` using `[WeierstrassCurve.map_c₄, WeierstrassCurve.map_c₄]`. Then use the resulting hypothesis. Establish `h0 : V.Δ ≠ 0`. Introduce `h; rw [h, map_zero, norm_zero] at hΔ; exact absurd hΔ (by norm_num)`. Use `⟨_, R, W, hk, hR, hRk, ?_, ?_⟩` and prove the remaining obligations. Establish `hmem : ((V.Δ⁻¹ : algebraicClosure ℚ ℂ) : ℂ) ∈ R`.

Use `hm _ ?_ ?_` and prove the remaining obligations. Rewrite using `[IntermediateField.coe_inv, ← eΔ]`. Conclude with `inv_mem (hRk _ W.Δ.2)`. Rewrite using `[map_inv₀, norm_inv]`. Conclude with `inv_le_one_of_one_le₀ hΔ`.

Use `IsUnit.of_mul_eq_one ⟨_, hmem⟩ (Subtype.ext ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((W.Δ : R) : ℂ) * ((V.Δ⁻¹ : algebraicClosure ℚ ℂ) : ℂ) = 1`. Rewrite using `[eΔ, ← IntermediateField.coe_mul, mul_inv_cancel₀ h0]`. Both sides reduce to the same expression. Rewrite using `[eΔ, ec]`.

Conclude with `congrArg (fun x : algebraicClosure ℚ ℂ => (x : ℂ)) hc` after adjusting the coercions.
-/
theorem descend (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (j : algebraicClosure ℚ ℂ)
    (V : WeierstrassCurve (algebraicClosure ℚ ℂ)) (h₁ : ‖lam V.a₁‖ ≤ 1) (h₂ : ‖lam V.a₂‖ ≤ 1) (h₃ : ‖lam V.a₃‖ ≤ 1)
    (h₄ : ‖lam V.a₄‖ ≤ 1) (h₆ : ‖lam V.a₆‖ ≤ 1) (hΔ : 1 ≤ ‖lam V.Δ‖) (hc : V.c₄ ^ 3 = j * V.Δ) :
    ∃ (k₁ : IntermediateField ℚ ℂ) (R₁ : Subring ℂ) (W : WeierstrassCurve R₁), FiniteDimensional ℚ k₁ ∧
      IsPlaceOver l lam k₁ R₁ ∧ (∀ x ∈ R₁, x ∈ k₁) ∧ IsUnit W.Δ ∧
      ((W.c₄ : R₁) : ℂ) ^ 3 = (j : ℂ) * ((W.Δ : R₁) : ℂ) := by
  let S : Set ℂ := {(V.a₁ : ℂ), (V.a₂ : ℂ), (V.a₃ : ℂ), (V.a₄ : ℂ), (V.a₆ : ℂ)}
  haveI : Finite S := (Set.toFinite S).to_subtype
  have hi : ∀ x : algebraicClosure ℚ ℂ, IsIntegral ℚ (x : ℂ) := fun x => (mem_algebraicClosure_iff.1 x.2).isIntegral
  have hk : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) :=
    IntermediateField.finiteDimensional_adjoin (by
      rintro x (rfl | rfl | rfl | rfl | rfl) <;> exact hi _)
  obtain ⟨R, hR, hRk⟩ := exists_isPlaceOver_le l lam _ hk
  have hm : ∀ x : algebraicClosure ℚ ℂ, (x : ℂ) ∈ IntermediateField.adjoin ℚ S → ‖lam x‖ ≤ 1 → (x : ℂ) ∈ R :=
    fun x hx hn => hR.2.2 _ hx ⟨x.2, by rw [Real.rpow_zero]; exact hn⟩
  have hs : ∀ x ∈ S, x ∈ IntermediateField.adjoin ℚ S := fun x hx => IntermediateField.subset_adjoin ℚ S hx
  let W : WeierstrassCurve R :=
    ⟨⟨_, hm _ (hs _ (by simp [S])) h₁⟩, ⟨_, hm _ (hs _ (by simp [S])) h₂⟩, ⟨_, hm _ (hs _ (by simp [S])) h₃⟩,
      ⟨_, hm _ (hs _ (by simp [S])) h₄⟩, ⟨_, hm _ (hs _ (by simp [S])) h₆⟩⟩
  have hW : W.map R.subtype = V.map (algebraMap (algebraicClosure ℚ ℂ) ℂ) := rfl
  have eΔ : ((W.Δ : R) : ℂ) = (V.Δ : ℂ) := by
    have := congrArg WeierstrassCurve.Δ hW
    rwa [WeierstrassCurve.map_Δ, WeierstrassCurve.map_Δ] at this
  have ec : ((W.c₄ : R) : ℂ) = (V.c₄ : ℂ) := by
    have := congrArg WeierstrassCurve.c₄ hW
    rwa [WeierstrassCurve.map_c₄, WeierstrassCurve.map_c₄] at this
  have h0 : V.Δ ≠ 0 := by
    intro h; rw [h, map_zero, norm_zero] at hΔ; exact absurd hΔ (by norm_num)
  refine ⟨_, R, W, hk, hR, hRk, ?_, ?_⟩
  · have hmem : ((V.Δ⁻¹ : algebraicClosure ℚ ℂ) : ℂ) ∈ R := by
      refine hm _ ?_ ?_
      · rw [IntermediateField.coe_inv, ← eΔ]; exact inv_mem (hRk _ W.Δ.2)
      · rw [map_inv₀, norm_inv]; exact inv_le_one_of_one_le₀ hΔ
    refine IsUnit.of_mul_eq_one ⟨_, hmem⟩ (Subtype.ext ?_)
    change ((W.Δ : R) : ℂ) * ((V.Δ⁻¹ : algebraicClosure ℚ ℂ) : ℂ) = 1
    rw [eΔ, ← IntermediateField.coe_mul, mul_inv_cancel₀ h0]; rfl
  · rw [eΔ, ec]; exact_mod_cast congrArg (fun x : algebraicClosure ℚ ℂ => (x : ℂ)) hc

open Polynomial in

/- English proof (translation)
Introduce `l _ lam J hJ`. Use `haveI : IsAlgClosed (algebraicClosure ℚ ℂ) := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed`. Establish `hJQ : IsIntegral ℚ J` using `hJ.tower_top`. Set `j : algebraicClosure ℚ ℂ` to `⟨J, mem_algebraicClosure_iff.2 hJQ.isAlgebraic⟩`. Establish `hjZ : IsIntegral ℤ j` using `(isIntegral_algHom_iff ((algebraicClosure ℚ ℂ).val.toRingHom.toIntAlgHom) Subtype.val_injective).1 hJ`.

Establish `hj : ‖lam j‖ ≤ 1` using `GlobalTheory.PlaceRingExists.norm_le_one_of_isIntegral_int (by`. Apply the tactic sequence `convert map_isIntegral_int lam hjZ using 1 <;> first | exact Subsingleton.elim _ _ | rfl)`. Distinguish the cases in `hl : l = 3`. Establish `hd : ((C 16 * (X * (X - C 1) + C 1)) ^ 3 - C j * (C 16 * (X * (X - C 1)) ^ 2) : (algebraicClosure ℚ ℂ)[X]).degree = 6` using `by compute_degree!`. Take `⟨α, hα⟩` from `IsAlgClosed.exists_root _ (hd.trans_ne (by decide))`.

Establish `hα' : (16 * (α * (α - 1) + 1)) ^ 3 = j * (16 * (α * (α - 1)) ^ 2)`. Simplify `hα` using `[sub_eq_zero]`. Establish `hn` using `legendre_norm (l := l) (by omega) hj (a := lam α) (by simpa [map_ofNat] using congrArg lam hα')`. Set `V : WeierstrassCurve (algebraicClosure ℚ ℂ)` to `⟨0, -(1 + α), 0, α, 0⟩`. Establish `eΔ : V.Δ = 16 * (α * (α - 1)) ^ 2`.

Simplify using `only [V, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]`. Expand and normalize the polynomial expressions, which then agree. Establish `ec : V.c₄ = 16 * (α * (α - 1) + 1)`. Simplify using `only [V, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]`. Expand and normalize the polynomial expressions, which then agree.

Use `descend l lam j V (by simp [V]) ?_ (by simp [V]) hn.1 (by simp [V]) ?_ (by rw [eΔ, ec, hα'])` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `‖lam (-(1 + α))‖ ≤ 1`. Rewrite using `[map_neg, norm_neg, map_add, map_one]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simp) hn.1)`. Rewrite using `[eΔ]`.

Simplify `hn.2` using `only [map_mul, map_pow, map_sub, map_one, map_ofNat]`. Establish `hd : ((X * (X ^ 3 - C 24)) ^ 3 - C j * (X ^ 3 - C 27) : (algebraicClosure ℚ ℂ)[X]).degree = 12` using `by compute_degree!`. Take `⟨α, hα⟩` from `IsAlgClosed.exists_root _ (hd.trans_ne (by decide))`. Establish `hα' : (α * (α ^ 3 - 24)) ^ 3 = j * (α ^ 3 - 27)`. Simplify `hα` using `[sub_eq_zero]`.

Establish `hn` using `deuring_norm (l := l) hl hj (a := lam α) (by simpa [map_ofNat] using congrArg lam hα')`. Set `V : WeierstrassCurve (algebraicClosure ℚ ℂ)` to `⟨α, 0, 1, 0, 0⟩`. Establish `eΔ : V.Δ = α ^ 3 - 27`. Simplify using `only [V, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]`. Expand and normalize the polynomial expressions, which then agree.

Establish `ec : V.c₄ = α * (α ^ 3 - 24)`. Simplify using `only [V, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]`. Expand and normalize the polynomial expressions, which then agree. Use `descend l lam j V hn.1 (by simp [V]) (by simp [V]) (by simp [V]) (by simp [V]) ?_ (by rw [eΔ, ec, hα'])` and prove the remaining obligations. Rewrite using `[eΔ]`.

Simplify `hn.2` using `only [map_mul, map_pow, map_sub, map_ofNat]`.
-/
theorem exists_curve : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (J : ℂ), IsIntegral ℤ J →
    ∃ (k₁ : IntermediateField ℚ ℂ) (R₁ : Subring ℂ) (W : WeierstrassCurve R₁), FiniteDimensional ℚ k₁ ∧
      IsPlaceOver l lam k₁ R₁ ∧ (∀ x ∈ R₁, x ∈ k₁) ∧ IsUnit W.Δ ∧ ((W.c₄ : R₁) : ℂ) ^ 3 = J * ((W.Δ : R₁) : ℂ) := by
  intro l _ lam J hJ
  haveI : IsAlgClosed (algebraicClosure ℚ ℂ) := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  have hJQ : IsIntegral ℚ J := hJ.tower_top
  let j : algebraicClosure ℚ ℂ := ⟨J, mem_algebraicClosure_iff.2 hJQ.isAlgebraic⟩
  have hjZ : IsIntegral ℤ j :=
    (isIntegral_algHom_iff ((algebraicClosure ℚ ℂ).val.toRingHom.toIntAlgHom) Subtype.val_injective).1 hJ
  have hj : ‖lam j‖ ≤ 1 := GlobalTheory.PlaceRingExists.norm_le_one_of_isIntegral_int (by
    convert map_isIntegral_int lam hjZ using 1 <;> first | exact Subsingleton.elim _ _ | rfl)
  by_cases hl : l = 3
  · have hd : ((C 16 * (X * (X - C 1) + C 1)) ^ 3 - C j * (C 16 * (X * (X - C 1)) ^ 2) :
        (algebraicClosure ℚ ℂ)[X]).degree = 6 := by compute_degree!
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ (hd.trans_ne (by decide))
    have hα' : (16 * (α * (α - 1) + 1)) ^ 3 = j * (16 * (α * (α - 1)) ^ 2) := by
      simpa [sub_eq_zero] using hα
    have hn := legendre_norm (l := l) (by omega) hj (a := lam α) (by simpa [map_ofNat] using congrArg lam hα')
    let V : WeierstrassCurve (algebraicClosure ℚ ℂ) := ⟨0, -(1 + α), 0, α, 0⟩
    have eΔ : V.Δ = 16 * (α * (α - 1)) ^ 2 := by
      simp only [V, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring
    have ec : V.c₄ = 16 * (α * (α - 1) + 1) := by
      simp only [V, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
      ring
    refine descend l lam j V (by simp [V]) ?_ (by simp [V]) hn.1 (by simp [V]) ?_ (by rw [eΔ, ec, hα'])
    · change ‖lam (-(1 + α))‖ ≤ 1
      rw [map_neg, norm_neg, map_add, map_one]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simp) hn.1)
    · rw [eΔ]; simpa only [map_mul, map_pow, map_sub, map_one, map_ofNat] using hn.2
  · have hd : ((X * (X ^ 3 - C 24)) ^ 3 - C j * (X ^ 3 - C 27) : (algebraicClosure ℚ ℂ)[X]).degree = 12 := by
      compute_degree!
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ (hd.trans_ne (by decide))
    have hα' : (α * (α ^ 3 - 24)) ^ 3 = j * (α ^ 3 - 27) := by
      simpa [sub_eq_zero] using hα
    have hn := deuring_norm (l := l) hl hj (a := lam α) (by simpa [map_ofNat] using congrArg lam hα')
    let V : WeierstrassCurve (algebraicClosure ℚ ℂ) := ⟨α, 0, 1, 0, 0⟩
    have eΔ : V.Δ = α ^ 3 - 27 := by
      simp only [V, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring
    have ec : V.c₄ = α * (α ^ 3 - 24) := by
      simp only [V, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
      ring
    refine descend l lam j V hn.1 (by simp [V]) (by simp [V]) (by simp [V]) (by simp [V]) ?_ (by rw [eΔ, ec, hα'])
    rw [eΔ]; simpa only [map_mul, map_pow, map_sub, map_ofNat] using hn.2

end GlobalTheory.PlaceRingCurve
