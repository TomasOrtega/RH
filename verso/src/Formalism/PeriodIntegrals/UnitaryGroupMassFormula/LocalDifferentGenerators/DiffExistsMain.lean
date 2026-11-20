import Mathlib
import Formalism.PeriodIntegrals.DiffGenLoc

noncomputable section

namespace PI.DiffGenLoc.UnitaryGroupMassFormula

open NumberField IsDedekindDomain WithZero

/- English proof (translation)
Use `first`. Consider the case `exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : F)).trans (HeightOneSpectrum.valuation_of_algebraMap v x)`. Consider the case `(rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]; rfl)`. Consider the case `simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]`. Consider the case `simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation, HeightOneSpectrum.valuation_of_algebraMap]`.

Consider the case `(rw [HeightOneSpectrum.adicCompletion.algebraMap_eq_coe, HeightOneSpectrum.valuedAdicCompletion_eq_valuation, HeightOneSpectrum.valuation_of_algebraMap])`.
-/
theorem val_alg {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) :
    Valued.v (algebraMap F (Fv F v) (x : F)) = v.intValuation x := by
  first
    | exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : F)).trans
        (HeightOneSpectrum.valuation_of_algebraMap v x)
    | (rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]; rfl)
    | simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
    | simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation, HeightOneSpectrum.valuation_of_algebraMap]
    | (rw [HeightOneSpectrum.adicCompletion.algebraMap_eq_coe, HeightOneSpectrum.valuedAdicCompletion_eq_valuation,
        HeightOneSpectrum.valuation_of_algebraMap])

/- English proof (translation)
Establish `hI : differentIdeal ℤ (𝓞 F) ≠ ⊥` using `differentIdeal_ne_bot`. Take `⟨y, hyI, hy0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hI`. Establish `hne : ∀ x : 𝓞 F, x ≠ 0 → v.intValuation x ≠ 0` using `fun x hx => by first`. Consider the case `exact v.intValuation_ne_zero x hx`. Consider the case `exact v.intValuation_ne_zero' x hx`.

Consider the case `exact (map_ne_zero _).2 hx`. Consider the case `simpa using hx`. Set `f : 𝓞 F → ℕ` to `fun x => if hx : x = 0 then 0 else (-(Multiplicative.toAdd (WithZero.unzero (hne x hx)))).toNat`. Establish `hfdef : ∀ z (hz : z ≠ 0), f z = (-(Multiplicative.toAdd (WithZero.unzero (hne z hz)))).toNat` using `fun z hz => dif_neg hz`. Establish `key : ∀ z : 𝓞 F, ∀ hz : z ≠ 0, v.intValuation z = ((Multiplicative.ofAdd (-(f z : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))`.

Introduce `z hz`. Establish `hu : ((WithZero.unzero (hne z hz) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = v.intValuation z` using `WithZero.coe_unzero _`. Establish `hle : Multiplicative.toAdd (WithZero.unzero (hne z hz)) ≤ 0`. Establish `h1 : ((WithZero.unzero (hne z hz) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤ ((1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ))`. Rewrite using `[hu, WithZero.coe_one]`.

Conclude with `v.intValuation_le_one z`. Rewrite `h1` using `[WithZero.coe_le_coe]`. Establish `h2` using `Multiplicative.toAdd_le.2 h1`. Simplify using `using h2`. Rewrite using `[hfdef z hz, Int.toNat_of_nonneg (by linarith), neg_neg, ofAdd_toAdd, hu]`.

Establish `hP : ∃ n, ∃ x ∈ differentIdeal ℤ (𝓞 F), x ≠ 0 ∧ f x = n` using `⟨_, y, hyI, hy0, rfl⟩`. Take `⟨x₀, hx₀I, hx₀0, hfx₀⟩` from `Nat.find_spec hP`. Use `⟨algebraMap F (Fv F v) (x₀ : F), ?_, ?_, x₀, hx₀I, rfl⟩` and prove the remaining obligations. Introduce `h`. Apply `hx₀0` to reduce the goal to its premises.

Establish `h1 : ((x₀ : F)) = 0` using `(algebraMap F (Fv F v)).injective (h.trans (map_zero _).symm)`. Conclude with `h1` after adjusting the coercions. Introduce `x hxI`. Rewrite using `[val_alg, val_alg]`. Distinguish the cases in `hx : x = 0`.

Simplify using `[hx]`. Establish `hmin : Nat.find hP ≤ f x` using `Nat.find_min' hP ⟨x, hxI, hx, rfl⟩`. Rewrite using `[key x hx, key x₀ hx₀0, WithZero.coe_le_coe, Multiplicative.ofAdd_le, neg_le_neg_iff, Nat.cast_le, hfx₀]`. Conclude with `hmin`.
-/
theorem diffExists_main {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : DiffExists v := by
  classical
  have hI : differentIdeal ℤ (𝓞 F) ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨y, hyI, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hne : ∀ x : 𝓞 F, x ≠ 0 → v.intValuation x ≠ 0 := fun x hx => by
    first
      | exact v.intValuation_ne_zero x hx
      | exact v.intValuation_ne_zero' x hx
      | exact (map_ne_zero _).2 hx
      | simpa using hx
  let f : 𝓞 F → ℕ := fun x =>
    if hx : x = 0 then 0 else (-(Multiplicative.toAdd (WithZero.unzero (hne x hx)))).toNat
  have hfdef : ∀ z (hz : z ≠ 0), f z = (-(Multiplicative.toAdd (WithZero.unzero (hne z hz)))).toNat :=
    fun z hz => dif_neg hz
  have key : ∀ z : 𝓞 F, ∀ hz : z ≠ 0,
      v.intValuation z = ((Multiplicative.ofAdd (-(f z : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro z hz
    have hu : ((WithZero.unzero (hne z hz) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = v.intValuation z :=
      WithZero.coe_unzero _
    have hle : Multiplicative.toAdd (WithZero.unzero (hne z hz)) ≤ 0 := by
      have h1 : ((WithZero.unzero (hne z hz) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤
          ((1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
        rw [hu, WithZero.coe_one]
        exact v.intValuation_le_one z
      rw [WithZero.coe_le_coe] at h1
      have h2 := Multiplicative.toAdd_le.2 h1
      simpa using h2
    rw [hfdef z hz, Int.toNat_of_nonneg (by linarith), neg_neg, ofAdd_toAdd, hu]
  have hP : ∃ n, ∃ x ∈ differentIdeal ℤ (𝓞 F), x ≠ 0 ∧ f x = n := ⟨_, y, hyI, hy0, rfl⟩
  obtain ⟨x₀, hx₀I, hx₀0, hfx₀⟩ := Nat.find_spec hP
  refine ⟨algebraMap F (Fv F v) (x₀ : F), ?_, ?_, x₀, hx₀I, rfl⟩
  · intro h
    apply hx₀0
    have h1 : ((x₀ : F)) = 0 := (algebraMap F (Fv F v)).injective (h.trans (map_zero _).symm)
    exact_mod_cast h1
  · intro x hxI
    rw [val_alg, val_alg]
    by_cases hx : x = 0
    · simp [hx]
    have hmin : Nat.find hP ≤ f x := Nat.find_min' hP ⟨x, hxI, hx, rfl⟩
    rw [key x hx, key x₀ hx₀0, WithZero.coe_le_coe, Multiplicative.ofAdd_le, neg_le_neg_iff, Nat.cast_le, hfx₀]
    exact hmin

end PI.DiffGenLoc.UnitaryGroupMassFormula
