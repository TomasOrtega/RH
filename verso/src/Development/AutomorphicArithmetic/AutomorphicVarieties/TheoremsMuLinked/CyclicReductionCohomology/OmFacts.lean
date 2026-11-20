import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

/- English proof (translation)
Introduce `l hl O _ _ _ hO _`. Take `⟨-, hf, hc⟩` from `hO`. Establish `hlm : (l : O) ∈ maximalIdeal O`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_natCast]`. Conclude with `CharP.cast_eq_zero _ l`.

Establish `hpow : ∀ m : ℕ, ((l : Om O m)) ^ m = 0` using `fun m => by`. Rewrite using `[← map_natCast (Ideal.Quotient.mk (maximalIdeal O ^ m)), ← map_pow]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hlm m)`. Use `⟨fun h2 => ?_, fun m => ⟨?_, ?_, fun x => ?_, fun a ha => ?_, fun Γ _ f hf => hf m⟩⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hu`.

Establish `h : (2 : O) ∈ maximalIdeal O` using `hu`. Rewrite `h` using `[← IsLocalRing.residue_eq_zero_iff, map_ofNat]`. Establish `h' : ((2 : ℕ) : ResidueField O) = 0` using `by exact_mod_cast h`. Rewrite `h'` using `[CharP.cast_eq_zero_iff (ResidueField O) l]`. Conclude with `h2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 h')`.

Use `haveI : Finite (O ⧸ maximalIdeal O) := hf`. Conclude with `Ideal.finite_quotient_pow (IsNoetherian.noetherian _) m`. Use `cardQuot_pow_of_prime (IsDiscreteValuationRing.not_a_field O) (i := m)` as an intermediate fact. Rewrite `this` using `[Submodule.cardQuot_apply, Submodule.cardQuot_apply]`. Conclude with `this`.

Rewrite using `[nsmul_eq_mul, Nat.cast_pow, hpow, zero_mul]`. Establish `h : a - 1 ∈ RingHom.ker (PadicInt.toZModPow (p` using `l) m) := by`. Rewrite using `[RingHom.mem_ker, map_sub, ha, map_one, sub_self]`. Rewrite `h` using `[PadicInt.ker_toZModPow, Ideal.mem_span_singleton']`. Take `⟨b, hb⟩` from `h`.

Establish `e : a = 1 + b * (l : ℤ_[l]) ^ m` using `by rw [hb]; ring`. Rewrite using `[e]`. Simplify using `only [map_add, map_one, map_mul, map_pow, map_natCast, hpow, mul_zero, add_zero]`.
-/
theorem UpperTheory.V.Th.omFacts :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O], (l ≠ 2 → IsUnit (2 : O)) ∧ ∀ m : ℕ, Finite (Om O m) ∧ Nat.card (Om O m) = Nat.card (ResidueField O) ^ m ∧ (∀ x : Om O m, l ^ m • x = 0) ∧ (∀ a : ℤ_[l], PadicInt.toZModPow m a = 1 → algebraMap O (Om O m) (algebraMap ℤ_[l] O a) = 1) ∧ ∀ (Γ : Type) [TopologicalSpace Γ] (f : Γ → O), AdicCont (maximalIdeal O) f → IsLocallyConstant fun g => algebraMap O (Om O m) (f g) := by
  intro l hl O _ _ _ hO _
  obtain ⟨-, hf, hc⟩ := hO
  have hlm : (l : O) ∈ maximalIdeal O := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero _ l
  have hpow : ∀ m : ℕ, ((l : Om O m)) ^ m = 0 := fun m => by
    rw [← map_natCast (Ideal.Quotient.mk (maximalIdeal O ^ m)), ← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hlm m)
  refine ⟨fun h2 => ?_, fun m => ⟨?_, ?_, fun x => ?_, fun a ha => ?_, fun Γ _ f hf => hf m⟩⟩
  · by_contra hu
    have h : (2 : O) ∈ maximalIdeal O := hu
    rw [← IsLocalRing.residue_eq_zero_iff, map_ofNat] at h
    have h' : ((2 : ℕ) : ResidueField O) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (ResidueField O) l] at h'
    exact h2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 h')
  · haveI : Finite (O ⧸ maximalIdeal O) := hf
    exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) m
  · have := cardQuot_pow_of_prime (IsDiscreteValuationRing.not_a_field O) (i := m)
    rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply] at this
    exact this
  · rw [nsmul_eq_mul, Nat.cast_pow, hpow, zero_mul]
  · have h : a - 1 ∈ RingHom.ker (PadicInt.toZModPow (p := l) m) := by
      rw [RingHom.mem_ker, map_sub, ha, map_one, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at h
    obtain ⟨b, hb⟩ := h
    have e : a = 1 + b * (l : ℤ_[l]) ^ m := by rw [hb]; ring
    rw [e]
    simp only [map_add, map_one, map_mul, map_pow, map_natCast, hpow, mul_zero, add_zero]
