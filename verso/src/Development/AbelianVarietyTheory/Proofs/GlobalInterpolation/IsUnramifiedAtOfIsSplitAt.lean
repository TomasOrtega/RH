import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
open NumberField IsDedekindDomain GlobalTheory.UnitaryBC

namespace GlobalTheory.SplitUnram

set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce `L _ _ _ w hw`. Take `⟨u, hne, hu⟩` from `hw`. Use `set K := maximalRealSubfield L`. Use `set p : Ideal (𝓞 K) := w.asIdeal.under (𝓞 K) with hpdef`. Establish `hup : u.asIdeal.under (𝓞 K) = p`.

Use `congrArg HeightOneSpectrum.asIdeal hu` as an intermediate fact. Conclude with `this`. Use `haveI : w.asIdeal.LiesOver p := ⟨rfl⟩`. Use `haveI : u.asIdeal.LiesOver p := ⟨hup.symm⟩`. Establish `hp0 : p ≠ ⊥` using `(w.under (𝓞 K)).ne_bot`.

Use `haveI hpm : p.IsMaximal := (w.under (𝓞 K)).isMaximal`. Establish `hwmem : w.asIdeal ∈ IsDedekindDomain.primesOverFinset p (𝓞 L)` using `(IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 L)).2 ⟨w.isPrime, inferInstance⟩`. Establish `humem : u.asIdeal ∈ IsDedekindDomain.primesOverFinset p (𝓞 L)` using `(IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 L)).2 ⟨u.isPrime, inferInstance⟩`. Establish `hneI : u.asIdeal ≠ w.asIdeal` using `fun h => hne (HeightOneSpectrum.ext h)`. Establish `hsum` using `Ideal.sum_ramification_inertia (𝓞 L) K L (p := p) hp0`.

Rewrite `hsum` using `[Algebra.IsQuadraticExtension.finrank_eq_two K L]`. Establish `hterm : ∀ P ∈ IsDedekindDomain.primesOverFinset p (𝓞 L), 1 ≤ p.ramificationIdx' P * p.inertiaDeg' P`. Introduce `P hP`. Take `⟨hPp, hPl⟩` from `(IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 L)).1 hP`. Use `haveI := hPp`.

Use `haveI := hPl`. Establish `h1 : 0 < p.ramificationIdx' P`. Rewrite using `[Ideal.ramificationIdx'_eq_ramificationIdx p P hp0]`. Conclude with `Ideal.ramificationIdx_pos P (𝓞 K)`. Establish `h2 : 0 < p.inertiaDeg' P` using `Ideal.inertiaDeg'_pos p P`.

Conclude with `Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero h1.ne' h2.ne')`. Establish `hpair : ({w.asIdeal, u.asIdeal} : Finset (Ideal (𝓞 L))) ⊆ IsDedekindDomain.primesOverFinset p (𝓞 L)`. Introduce `P hP`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hP`. Break down `hP with rfl | rfl` into its components or cases.

Conclude with `hwmem`. Conclude with `humem`. Establish `hle` using `Finset.sum_le_sum_of_subset (f := fun P => p.ramificationIdx' P * p.inertiaDeg' P) hpair`. Rewrite `hle` using `[Finset.sum_pair hneI.symm, hsum]`. Establish `hu1` using `hterm _ humem`.

Establish `hw1 : p.ramificationIdx' w.asIdeal * p.inertiaDeg' w.asIdeal = 1`. Use `hterm _ hwmem` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `he : p.ramificationIdx' w.asIdeal = 1` using `Nat.eq_one_of_mul_eq_one_right hw1`. Rewrite `he` using `[Ideal.ramificationIdx'_eq_ramificationIdx p w.asIdeal hp0]`.

Conclude with `(Algebra.isUnramifiedAt_iff_of_isDedekindDomain).2 he`.
-/
theorem isUnramifiedAt_of_isSplitAt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L]
    (w : HeightOneSpectrum (𝓞 L)), IsSplitAt w →
    Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal := by
  intro L _ _ _ w hw
  obtain ⟨u, hne, hu⟩ := hw
  set K := maximalRealSubfield L
  set p : Ideal (𝓞 K) := w.asIdeal.under (𝓞 K) with hpdef
  have hup : u.asIdeal.under (𝓞 K) = p := by
    have := congrArg HeightOneSpectrum.asIdeal hu
    exact this
  haveI : w.asIdeal.LiesOver p := ⟨rfl⟩
  haveI : u.asIdeal.LiesOver p := ⟨hup.symm⟩
  have hp0 : p ≠ ⊥ := (w.under (𝓞 K)).ne_bot
  haveI hpm : p.IsMaximal := (w.under (𝓞 K)).isMaximal
  have hwmem : w.asIdeal ∈ IsDedekindDomain.primesOverFinset p (𝓞 L) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 L)).2 ⟨w.isPrime, inferInstance⟩
  have humem : u.asIdeal ∈ IsDedekindDomain.primesOverFinset p (𝓞 L) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 L)).2 ⟨u.isPrime, inferInstance⟩
  have hneI : u.asIdeal ≠ w.asIdeal := fun h => hne (HeightOneSpectrum.ext h)
  have hsum := Ideal.sum_ramification_inertia (𝓞 L) K L (p := p) hp0
  rw [Algebra.IsQuadraticExtension.finrank_eq_two K L] at hsum
  have hterm : ∀ P ∈ IsDedekindDomain.primesOverFinset p (𝓞 L), 1 ≤ p.ramificationIdx' P * p.inertiaDeg' P := by
    intro P hP
    obtain ⟨hPp, hPl⟩ := (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 L)).1 hP
    haveI := hPp; haveI := hPl
    have h1 : 0 < p.ramificationIdx' P := by
      rw [Ideal.ramificationIdx'_eq_ramificationIdx p P hp0]
      exact Ideal.ramificationIdx_pos P (𝓞 K)
    have h2 : 0 < p.inertiaDeg' P := Ideal.inertiaDeg'_pos p P
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero h1.ne' h2.ne')
  have hpair : ({w.asIdeal, u.asIdeal} : Finset (Ideal (𝓞 L))) ⊆ IsDedekindDomain.primesOverFinset p (𝓞 L) := by
    intro P hP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with rfl | rfl
    · exact hwmem
    · exact humem
  have hle := Finset.sum_le_sum_of_subset (f := fun P => p.ramificationIdx' P * p.inertiaDeg' P) hpair
  rw [Finset.sum_pair hneI.symm, hsum] at hle
  have hu1 := hterm _ humem
  have hw1 : p.ramificationIdx' w.asIdeal * p.inertiaDeg' w.asIdeal = 1 := by
    have := hterm _ hwmem
    omega
  have he : p.ramificationIdx' w.asIdeal = 1 := Nat.eq_one_of_mul_eq_one_right hw1
  rw [Ideal.ramificationIdx'_eq_ramificationIdx p w.asIdeal hp0] at he
  exact (Algebra.isUnramifiedAt_iff_of_isDedekindDomain).2 he

end GlobalTheory.SplitUnram
