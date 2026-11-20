import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ConeBall
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
Set `: Algebra K L` to `σ.toAlgebra`. Set `: Algebra (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) L)` to `algebraMvPolynomial`. Establish `: Module.Free K L` using `Module.Free.of_divisionRing K L`. Establish `: Module.Flat (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) L)` using `Module.Flat.isBaseChange K (MvPolynomial (Fin n) K) L (MvPolynomial (Fin n) L) Algebra.IsPushout.out`. Establish `halg : algebraMap (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) L) = MvPolynomial.map σ`.

Both sides reduce to the same expression. Take `⟨⟨hWp, hIW⟩, hmin⟩` from `hW`. Use `hWp` as an intermediate fact. Establish `hIP : I ≤ W.comap (MvPolynomial.map σ)` using `Ideal.map_le_iff_le_comap.mp hIW`. Establish `: (W.comap (MvPolynomial.map σ)).IsPrime` using `Ideal.comap_isPrime _ W`.

Establish `: W.LiesOver (W.comap (MvPolynomial.map σ))` using `⟨by rw [Ideal.under_def, halg]⟩`. Take `⟨W', hW'W, hW'p, hW'I⟩` from `Ideal.exists_ideal_le_liesOver_of_le (p := I) W hIP`. Establish `hI' : I = W'.comap (MvPolynomial.map σ)` using `by rw [hW'I.over, Ideal.under_def, halg]`. Establish `hIW' : I.map (MvPolynomial.map σ) ≤ W'` using `Ideal.map_le_iff_le_comap.mpr hI'.le`. Establish `hWW' : W ≤ W'` using `hmin ⟨hW'p, hIW'⟩ hW'W`.

Rewrite using `[hI', le_antisymm hW'W hWW']`.
-/
theorem BaseChangeAvoid.comap_eq_of_mem_minimalPrimes {K L : Type*} [Field K] [Field L] {n : ℕ}
    (σ : K →+* L) (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    {W : Ideal (MvPolynomial (Fin n) L)} (hW : W ∈ (I.map (MvPolynomial.map σ)).minimalPrimes) :
    W.comap (MvPolynomial.map σ) = I := by
  let : Algebra K L := σ.toAlgebra
  let : Algebra (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) L) := algebraMvPolynomial
  have : Module.Free K L := Module.Free.of_divisionRing K L
  have : Module.Flat (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) L) :=
    Module.Flat.isBaseChange K (MvPolynomial (Fin n) K) L (MvPolynomial (Fin n) L)
      Algebra.IsPushout.out
  have halg : algebraMap (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) L) = MvPolynomial.map σ :=
    rfl
  obtain ⟨⟨hWp, hIW⟩, hmin⟩ := hW
  have := hWp
  have hIP : I ≤ W.comap (MvPolynomial.map σ) := Ideal.map_le_iff_le_comap.mp hIW
  have : (W.comap (MvPolynomial.map σ)).IsPrime := Ideal.comap_isPrime _ W
  have : W.LiesOver (W.comap (MvPolynomial.map σ)) := ⟨by rw [Ideal.under_def, halg]⟩
  obtain ⟨W', hW'W, hW'p, hW'I⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := I) W hIP
  have hI' : I = W'.comap (MvPolynomial.map σ) := by rw [hW'I.over, Ideal.under_def, halg]
  have hIW' : I.map (MvPolynomial.map σ) ≤ W' := Ideal.map_le_iff_le_comap.mpr hI'.le
  have hWW' : W ≤ W' := hmin ⟨hW'p, hIW'⟩ hW'W
  rw [hI', le_antisymm hW'W hWW']

/- English proof (translation)
Introduce `K _ _ n I u σ hI hu W hW h`. Establish `hW' : W ∈ relComps (I.map (MvPolynomial.map σ))`. Assume the negation of the conclusion as `hn`. Rewrite `hW` using `[Finsupp.mem_support_iff]`. Conclude with `hW (by simp [fundCycle, Finsupp.onFinset_apply, hn])`.

Use `hI.isPrime` as an intermediate fact. Establish `hc` using `BaseChangeAvoid.comap_eq_of_mem_minimalPrimes σ I hW'.1`. Apply `hu` to reduce the goal to its premises. Rewrite using `[← hc, Ideal.mem_comap]`. Use `h using 1` and compare the differences between its conclusion and the goal.

Simplify using `[linForm, map_sum]`.
-/
theorem BaseChangeAvoid.proof : BaseChangeAvoid.Statement := by
  intro K _ _ n I u σ hI hu W hW h
  have hW' : W ∈ relComps (I.map (MvPolynomial.map σ)) := by
    by_contra hn
    rw [Finsupp.mem_support_iff] at hW
    exact hW (by simp [fundCycle, Finsupp.onFinset_apply, hn])
  have := hI.isPrime
  have hc := BaseChangeAvoid.comap_eq_of_mem_minimalPrimes σ I hW'.1
  apply hu
  rw [← hc, Ideal.mem_comap]
  convert h using 1
  simp [linForm, map_sum]

end GroundTheory.Heights₂.Heights
