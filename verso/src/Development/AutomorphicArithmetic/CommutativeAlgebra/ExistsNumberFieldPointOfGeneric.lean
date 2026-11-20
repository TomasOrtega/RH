import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
open UpperTheory.Gal.Int.Geo
open NumberField

/- English proof (translation)
Establish `hd : Module.finrank ℤ (𝓞 F) ≠ 0` using `Module.finrank_pos.ne'`. Establish `hn` using `congrArg (Algebra.norm ℤ) h`. Establish `e : ∀ k : ℕ, (k : 𝓞 F) = algebraMap ℤ (𝓞 F) (k : ℤ)` using `fun k => by simp`. Rewrite `hn` using `[map_mul, e n, e m, Algebra.norm_algebraMap, Algebra.norm_algebraMap]`. Establish `hdvd : (n : ℤ) ^ Module.finrank ℤ (𝓞 F) ∣ (m : ℤ) ^ Module.finrank ℤ (𝓞 F)` using `⟨_, hn.symm⟩`.

Conclude with `Int.natCast_dvd_natCast.1 ((Int.pow_dvd_pow_iff hd).1 hdvd)`.
-/
private lemma natDvd_of_eq_mul {F : Type} [Field F] [NumberField F] {n m : ℕ} {x : 𝓞 F}
    (h : (n : 𝓞 F) * x = (m : 𝓞 F)) : n ∣ m := by
  have hd : Module.finrank ℤ (𝓞 F) ≠ 0 := Module.finrank_pos.ne'
  have hn := congrArg (Algebra.norm ℤ) h
  have e : ∀ k : ℕ, (k : 𝓞 F) = algebraMap ℤ (𝓞 F) (k : ℤ) := fun k => by simp
  rw [map_mul, e n, e m, Algebra.norm_algebraMap, Algebra.norm_algebraMap] at hn
  have hdvd : (n : ℤ) ^ Module.finrank ℤ (𝓞 F) ∣ (m : ℤ) ^ Module.finrank ℤ (𝓞 F) :=
    ⟨_, hn.symm⟩
  exact Int.natCast_dvd_natCast.1 ((Int.pow_dvd_pow_iff hd).1 hdvd)

/- English proof (translation)
Introduce `hG p _ D E _ _ gb w q _ r 𝔴 𝔫 S N hN`. Use `⟨fun hmem => ?_, fun c a t h => ?_⟩` and prove the remaining obligations. Rewrite `hmem` using `[S.lev]`. Take `⟨x, hx, hxe⟩` from `Ideal.mem_span_singleton_mul.1 hmem`. Establish `hNa : (N : 𝓞 D.F) ∈ S.𝔞` using `hxe ▸ Ideal.mul_mem_left _ _ hx`.

Take `⟨a, ha⟩` from `(hG (𝓞 D.F) S.𝔞 N hN).1 hNa`. Take `⟨c, hc⟩` from `natDvd_of_eq_mul hxe`. Conclude with `⟨c, a, hc, ha⟩`. Conclude with `⟨by rw [h.1, mul_assoc], (hG (𝓞 D.F) S.𝔞 N hN).2 a t h.2⟩`.
-/
theorem UpperTheory.exists_number_field_point_of_generic :
    GenEx → NumEx := by
  intro hG p _ D E _ _ gb w q _ r 𝔴 𝔫 S N hN
  refine ⟨fun hmem => ?_, fun c a t h => ?_⟩
  · rw [S.lev] at hmem
    obtain ⟨x, hx, hxe⟩ := Ideal.mem_span_singleton_mul.1 hmem
    have hNa : (N : 𝓞 D.F) ∈ S.𝔞 := hxe ▸ Ideal.mul_mem_left _ _ hx
    obtain ⟨a, ha⟩ := (hG (𝓞 D.F) S.𝔞 N hN).1 hNa
    obtain ⟨c, hc⟩ := natDvd_of_eq_mul hxe
    exact ⟨c, a, hc, ha⟩
  · exact ⟨by rw [h.1, mul_assoc], (hG (𝓞 D.F) S.𝔞 N hN).2 a t h.2⟩
