import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.DegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.ImportsBis
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.CarryPrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt

open NumberField IsDedekindDomain UpperTheory.V.Kum UpperTheory.V.Stick
open scoped nonZeroDivisors

/- English proof (translation)
Introduce `M _ K _ _ _ c a b`. Use `set S : Set (HeightOneSpectrum (𝓞 K)) := {v | v.asIdeal ∣ Ideal.span {((M : ℕ) : 𝓞 K)}}`. Establish `hM0 : Ideal.span {((M : ℕ) : 𝓞 K)} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `NeZero.ne M` after adjusting the coercions.

Establish `hS : S.Finite` using `Ideal.finite_factors hM0`. Take `⟨v, hvS, hprime, hvc⟩` from `degOne K S hS c`. Use `haveI : Fact (Ideal.absNorm v.asIdeal).Prime := ⟨hprime⟩`. Take `⟨π, hπ⟩` from `(red K (Ideal.absNorm v.asIdeal) v.asIdeal).1 rfl`. Establish `hpv` using `((red K (Ideal.absNorm v.asIdeal) v.asIdeal).2 π hπ).2.2.2`.

Establish `hcop : (Ideal.absNorm v.asIdeal).Coprime M`. Rewrite using `[Nat.Prime.coprime_iff_not_dvd hprime]`. Introduce and unpack `⟨k, hk⟩`. Apply `hvS` to reduce the goal to its premises. Use `show v.asIdeal ∣ _`.

Rewrite using `[Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem, hk, Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ hpv`. Rewrite using `[← hvc]`. Conclude with `carryPrime M K _ π hcop v hπ a b`.
-/
theorem UpperTheory.V.Stick.carryAll :
    ∀ (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (c : ClassGroup (𝓞 K)) (a b : ZMod M),
    ∏ t : (ZMod M)ˣ, clMap (sg M K t)⁻¹.toRingEquiv c ^ carry M (a * t) (b * t) = 1 := by
  intro M _ K _ _ _ c a b
  set S : Set (HeightOneSpectrum (𝓞 K)) := {v | v.asIdeal ∣ Ideal.span {((M : ℕ) : 𝓞 K)}}
  have hM0 : Ideal.span {((M : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast NeZero.ne M
  have hS : S.Finite := Ideal.finite_factors hM0
  obtain ⟨v, hvS, hprime, hvc⟩ := degOne K S hS c
  haveI : Fact (Ideal.absNorm v.asIdeal).Prime := ⟨hprime⟩
  obtain ⟨π, hπ⟩ := (red K (Ideal.absNorm v.asIdeal) v.asIdeal).1 rfl
  have hpv := ((red K (Ideal.absNorm v.asIdeal) v.asIdeal).2 π hπ).2.2.2
  have hcop : (Ideal.absNorm v.asIdeal).Coprime M := by
    rw [Nat.Prime.coprime_iff_not_dvd hprime]
    rintro ⟨k, hk⟩
    apply hvS
    show v.asIdeal ∣ _
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem, hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hpv
  rw [← hvc]
  exact carryPrime M K _ π hcop v hπ a b
