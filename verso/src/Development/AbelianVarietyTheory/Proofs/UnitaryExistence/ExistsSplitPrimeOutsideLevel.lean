import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ _ H l`. Establish `hM : 0 < l.M'` using `Nat.lcm_pos (by have := l.three_le; omega) l.A_pos`. Use `set c : ℕ := 2 * l.M' with hc`. Establish `hd` using `H.d_prime.pos`. Establish `hn : c ^ 2 * H.d + 1 ≠ 1`.

Establish `: 0 < c ^ 2 * H.d` using `by positivity`. Use linear arithmetic over natural numbers and integers. Take `⟨p, hp, hpn⟩` from `Nat.exists_prime_and_dvd hn`. Establish `hpc : ¬ p ∣ c` using `fun h => by`. Establish `h1 : p ∣ c ^ 2 * H.d` using `(h.trans (dvd_pow_self c two_ne_zero)).mul_right _`.

Conclude with `hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h1).1 hpn))`. Establish `hp2 : ¬ p ∣ 2` using `fun h => hpc (h.mul_right _)`. Establish `hpM : ¬ p ∣ l.M'` using `fun h => hpc (h.mul_left _)`. Establish `hpZ : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.1 hp`. Use `haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal ((Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ) (by simpa using hp.ne_zero)`.

Take `⟨Q, hQ, hQc⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) (Ideal.span {(p : ℤ)}) (by`. Rewrite using `[(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 E)).injective_int]`. Conclude with `bot_le)`. Establish `hpQ : (p : 𝓞 E) ∈ Q`. Establish `: (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E))`.

Rewrite using `[hQc]`. Conclude with `Ideal.mem_span_singleton_self _`. Simplify `this` using `[Ideal.mem_comap]`. Use `⟨Q, p, hQ, ?_, hp, hpQ, hpM⟩` and prove the remaining obligations. Establish `hprod : (1 + (c : 𝓞 E) * H.rt) * (1 - (c : 𝓞 E) * H.rt) ∈ Q`.

Take `⟨k, hk⟩` from `hpn`. Establish `h1 : (1 + (c : 𝓞 E) * H.rt) * (1 - (c : 𝓞 E) * H.rt) = (p : 𝓞 E) * (k : 𝓞 E)`. Establish `h2 : (c : 𝓞 E) ^ 2 * (H.d : 𝓞 E) + 1 = (p : 𝓞 E) * (k : 𝓞 E)`. Conclude with `congrArg (Nat.cast : ℕ → 𝓞 E) hk` after adjusting the coercions. Take the linear combination `h2 - (c : 𝓞 E) ^ 2 * H.rt_sq`.

Rewrite using `[h1]`. Conclude with `Q.mul_mem_right _ hpQ`. Establish `key : ∀ β ∈ Q, β + H.bar β = 2 → Q ⊔ Q.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤`. Introduce `β hβ h2`. Establish `hm2 : (2 : 𝓞 E) ∈ Q ⊔ Q.map (H.bar : 𝓞 E →+* 𝓞 E)`.

Rewrite using `[← h2]`. Conclude with `Ideal.add_mem _ (Ideal.mem_sup_left hβ) (Ideal.mem_sup_right (Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hβ))`. Establish `hcop : IsCoprime (p : 𝓞 E) ((2 : ℕ) : 𝓞 E)` using `Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hp).2 hp2)`. Take `⟨a, b, hab⟩` from `hcop`. Rewrite using `[Ideal.eq_top_iff_one, ← hab]`.

Use `Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mem_sup_left hpQ)) (Ideal.mul_mem_left _ _ ?_)` and prove the remaining obligations. Simplify using `using hm2`. Break down `hQ.isPrime.mem_or_mem hprod with h | h` into its components or cases. Use `key _ h ?_` and prove the remaining obligations. Rewrite using `[map_add, map_mul, map_one, map_natCast, HostModel.bar_rt]`.

Expand and normalize the polynomial expressions, which then agree. Use `key _ h ?_` and prove the remaining obligations. Rewrite using `[map_sub, map_mul, map_one, map_natCast, HostModel.bar_rt]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_split_prime_outside_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H), ∃ (𝔓 : Ideal (𝓞 E)) (p : ℕ), 𝔓.IsMaximal ∧ 𝔓 ⊔ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ ∧ p.Prime ∧ (p : 𝓞 E) ∈ 𝔓 ∧ ¬ p ∣ l.M' := by
  intro E _ _ _ H l
  have hM : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  set c : ℕ := 2 * l.M' with hc
  have hd := H.d_prime.pos
  have hn : c ^ 2 * H.d + 1 ≠ 1 := by
    have : 0 < c ^ 2 * H.d := by positivity
    omega
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn
  have hpc : ¬ p ∣ c := fun h => by
    have h1 : p ∣ c ^ 2 * H.d := (h.trans (dvd_pow_self c two_ne_zero)).mul_right _
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h1).1 hpn))
  have hp2 : ¬ p ∣ 2 := fun h => hpc (h.mul_right _)
  have hpM : ¬ p ∣ l.M' := fun h => hpc (h.mul_left _)
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal ((Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ)
      (by simpa using hp.ne_zero)
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E)
    (Ideal.span {(p : ℤ)}) (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 E)).injective_int]
      exact bot_le)
  have hpQ : (p : 𝓞 E) ∈ Q := by
    have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := by
      rw [hQc]; exact Ideal.mem_span_singleton_self _
    simpa [Ideal.mem_comap] using this
  refine ⟨Q, p, hQ, ?_, hp, hpQ, hpM⟩
  have hprod : (1 + (c : 𝓞 E) * H.rt) * (1 - (c : 𝓞 E) * H.rt) ∈ Q := by
    obtain ⟨k, hk⟩ := hpn
    have h1 : (1 + (c : 𝓞 E) * H.rt) * (1 - (c : 𝓞 E) * H.rt) = (p : 𝓞 E) * (k : 𝓞 E) := by
      have h2 : (c : 𝓞 E) ^ 2 * (H.d : 𝓞 E) + 1 = (p : 𝓞 E) * (k : 𝓞 E) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → 𝓞 E) hk
      linear_combination h2 - (c : 𝓞 E) ^ 2 * H.rt_sq
    rw [h1]
    exact Q.mul_mem_right _ hpQ
  have key : ∀ β ∈ Q, β + H.bar β = 2 →
      Q ⊔ Q.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ := by
    intro β hβ h2
    have hm2 : (2 : 𝓞 E) ∈ Q ⊔ Q.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [← h2]
      exact Ideal.add_mem _ (Ideal.mem_sup_left hβ)
        (Ideal.mem_sup_right (Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hβ))
    have hcop : IsCoprime (p : 𝓞 E) ((2 : ℕ) : 𝓞 E) :=
      Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hp).2 hp2)
    obtain ⟨a, b, hab⟩ := hcop
    rw [Ideal.eq_top_iff_one, ← hab]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mem_sup_left hpQ))
      (Ideal.mul_mem_left _ _ ?_)
    simpa using hm2
  rcases hQ.isPrime.mem_or_mem hprod with h | h
  · refine key _ h ?_
    rw [map_add, map_mul, map_one, map_natCast, HostModel.bar_rt]; ring
  · refine key _ h ?_
    rw [map_sub, map_mul, map_one, map_natCast, HostModel.bar_rt]; ring

end GlobalTheory
