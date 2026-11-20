import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdSubOfDvdSubX
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.TameFrob

open Polynomial

attribute [local instance] algK isFractionRing

/- English proof (translation)
Introduce `l _ a _ E hmon hdeg hdiv ⟨w, hw⟩`. Establish `hP : (Ideal.span {(l : Wq l a)}).IsPrime`. Rewrite using `[← WittVector.ker_constantCoeff]`. Conclude with `RingHom.ker_isPrime _`. Establish `hl0 : (l : Wq l a) ≠ 0` using `fun h => by`.

Use `congrArg (iotaO l a) h` as an intermediate fact. Rewrite `this` using `[map_natCast, map_zero]`. Conclude with `(Fact.out : l.Prime).ne_zero (by exact_mod_cast this)`. Establish `hW : Irreducible E`. Use `Polynomial.IsEisensteinAt.irreducible ⟨?_, ?_, ?_⟩ hP hmon.isPrimitive hdeg` and prove the remaining obligations.

Rewrite using `[hmon.leadingCoeff]`. Conclude with `fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h)`. Introduce `n hn`. Conclude with `Ideal.mem_span_singleton.2 (hdiv n hn)`. Rewrite using `[hw, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`.

Introduce and unpack `⟨c, hc⟩`. Establish `h1 : (l : Wq l a) * ((w : Wq l a) - l * c) = 0` using `by linear_combination hc`. Establish `h2 : (w : Wq l a) = l * c`. Use `(mul_eq_zero.1 h1).resolve_left hl0` as an intermediate fact. Take the linear combination `this`.

Establish `h3` using `congrArg WittVector.constantCoeff h2`. Rewrite `h3` using `[map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]`. Conclude with `(w.isUnit.map WittVector.constantCoeff).ne_zero h3`. Establish `h` using `(hmon.irreducible_iff_irreducible_map_fraction_map (K := ↥(Kunr l a))).1 hW`. Conclude with `h`.
-/
theorem irreducible_map_iota_of_eisenstein : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (E : Polynomial (Wq l a)), E.Monic → 0 < E.natDegree →
    (∀ i < E.natDegree, (l : Wq l a) ∣ E.coeff i) → (∃ w : (Wq l a)ˣ, E.coeff 0 = (l : Wq l a) * w) →
    Irreducible (E.map (GlobalTheory.TameFrob.iota l a)) := by
  intro l _ a _ E hmon hdeg hdiv ⟨w, hw⟩
  have hP : (Ideal.span {(l : Wq l a)}).IsPrime := by
    rw [← WittVector.ker_constantCoeff]; exact RingHom.ker_isPrime _
  have hl0 : (l : Wq l a) ≠ 0 := fun h => by
    have := congrArg (iotaO l a) h
    rw [map_natCast, map_zero] at this
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast this)
  have hW : Irreducible E := by
    refine Polynomial.IsEisensteinAt.irreducible ⟨?_, ?_, ?_⟩ hP hmon.isPrimitive hdeg
    · rw [hmon.leadingCoeff]
      exact fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h)
    · intro n hn
      exact Ideal.mem_span_singleton.2 (hdiv n hn)
    · rw [hw, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      rintro ⟨c, hc⟩
      have h1 : (l : Wq l a) * ((w : Wq l a) - l * c) = 0 := by linear_combination hc
      have h2 : (w : Wq l a) = l * c := by
        have := (mul_eq_zero.1 h1).resolve_left hl0
        linear_combination this
      have h3 := congrArg WittVector.constantCoeff h2
      rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul] at h3
      exact (w.isUnit.map WittVector.constantCoeff).ne_zero h3
  have h := (hmon.irreducible_iff_irreducible_map_fraction_map (K := ↥(Kunr l a))).1 hW
  exact h

end GlobalTheory.TameFrob
