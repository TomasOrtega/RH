import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
import GroundTheory.GlobalFields.TateThesis.Chebotarev
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CycInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.UnramIff

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

/- English proof (translation)
Introduce `K H _ _ _ _ _ _ _ p hp`. Rewrite using `[UpperTheory.V.CF.unramIff.1 K p hp]`. Prove the components needed by the constructor for the conclusion. Introduce `h w hw`. Establish `hv : (p : 𝓞 K) ∈ w.asIdeal.under (𝓞 K)`.

Simplify `hw` using `[Ideal.under, Ideal.mem_comap, map_natCast]`. Set `v : HeightOneSpectrum (𝓞 K)` to `⟨w.asIdeal.under (𝓞 K), inferInstance, fun hb => by`. Rewrite `hv` using `[hb]`. Conclude with `(Nat.cast_ne_zero.mpr hp.ne_zero) ((Ideal.mem_bot).mp hv)⟩`. Rewrite using `[← Subgroup.map_eq_bot_iff, UpperTheory.V.CF.ineMap ℚ K H w]`.

Conclude with `h v hv`. Introduce `h v hv`. Establish `hle : Ideal.comap (algebraMap (𝓞 K) (𝓞 H)) ⊥ ≤ v.asIdeal`. Introduce `x hx`. Rewrite `hx` using `[Ideal.mem_comap, Ideal.mem_bot]`.

Establish `hx0 : x = 0` using `FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 H) (by rw [hx, map_zero])`. Rewrite using `[hx0]`. Conclude with `v.asIdeal.zero_mem`. Take `⟨Q, -, hQ, hQv⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal ⊥ hle`. Establish `hpQ : (p : 𝓞 H) ∈ Q`.

Establish `hc : (p : 𝓞 K) ∈ Q.comap (algebraMap (𝓞 K) (𝓞 H))` using `hQv ▸ hv`. Simplify `hc` using `[Ideal.mem_comap, map_natCast]`. Set `w : HeightOneSpectrum (𝓞 H)` to `⟨Q, hQ, fun hb => by`. Rewrite `hpQ` using `[hb]`. Conclude with `(Nat.cast_ne_zero.mpr hp.ne_zero) ((Ideal.mem_bot).mp hpQ)⟩`.

Establish `h1` using `h w hpQ`. Rewrite `h1` using `[← Subgroup.map_eq_bot_iff, UpperTheory.V.CF.ineMap ℚ K H w]`. Establish `hw : Ideal.under (𝓞 K) w.asIdeal = v.asIdeal` using `hQv`. Rewrite `h1` using `[hw]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.V.CF.ineFixQ :
    ∀ (K H : Type) [Field K] [NumberField K] [Field H] [NumberField H] [Algebra K H] [IsGalois ℚ K] [IsGalois ℚ H] (p : ℕ), p.Prime → (UnramAt K p ↔ ∀ w : HeightOneSpectrum (𝓞 H), (p : 𝓞 H) ∈ w.asIdeal → w.asIdeal.inertia Gal(H/ℚ) ≤ (resTo ℚ K H).ker) := by
  intro K H _ _ _ _ _ _ _ p hp
  rw [UpperTheory.V.CF.unramIff.1 K p hp]
  constructor
  · intro h w hw
    have hv : (p : 𝓞 K) ∈ w.asIdeal.under (𝓞 K) := by
      simpa [Ideal.under, Ideal.mem_comap, map_natCast] using hw
    let v : HeightOneSpectrum (𝓞 K) := ⟨w.asIdeal.under (𝓞 K), inferInstance, fun hb => by
      rw [hb] at hv
      exact (Nat.cast_ne_zero.mpr hp.ne_zero) ((Ideal.mem_bot).mp hv)⟩
    rw [← Subgroup.map_eq_bot_iff, UpperTheory.V.CF.ineMap ℚ K H w]
    exact h v hv
  · intro h v hv
    have hle : Ideal.comap (algebraMap (𝓞 K) (𝓞 H)) ⊥ ≤ v.asIdeal := by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot] at hx
      have hx0 : x = 0 := FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 H) (by rw [hx, map_zero])
      rw [hx0]
      exact v.asIdeal.zero_mem
    obtain ⟨Q, -, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal ⊥ hle
    have hpQ : (p : 𝓞 H) ∈ Q := by
      have hc : (p : 𝓞 K) ∈ Q.comap (algebraMap (𝓞 K) (𝓞 H)) := hQv ▸ hv
      simpa [Ideal.mem_comap, map_natCast] using hc
    let w : HeightOneSpectrum (𝓞 H) := ⟨Q, hQ, fun hb => by
      rw [hb] at hpQ
      exact (Nat.cast_ne_zero.mpr hp.ne_zero) ((Ideal.mem_bot).mp hpQ)⟩
    have h1 := h w hpQ
    rw [← Subgroup.map_eq_bot_iff, UpperTheory.V.CF.ineMap ℚ K H w] at h1
    have hw : Ideal.under (𝓞 K) w.asIdeal = v.asIdeal := hQv
    rwa [hw] at h1
