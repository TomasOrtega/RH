import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StOneComponentGeneralPoint
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVanishNearPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

/- English proof (translation)
Introduce `n I W hW`. Establish `hWp : W.IsPrime` using `hW.1.1`. Establish `hfin : I.minimalPrimes.Finite` using `Ideal.finite_minimalPrimes_of_isNoetherianRing _ I`. Establish `hsep : ∀ W' ∈ I.minimalPrimes, W' ≠ W → ∃ g ∈ W', g ∉ W`. Introduce `W' hW' hne`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hne (le_antisymm h (hW.2 hW'.1 h))`. Use `choose! g hgW' hgW using hsep`. Use `set S := hfin.toFinset.erase W with hS`.

Use `set f : MvPolynomial (Fin n) ℂ := ∏ W' ∈ S, g W' with hfdef`. Establish `hf : f ∉ W`. Introduce `hmem`. Take `⟨W', hW'S, hgm⟩` from `(Ideal.IsPrime.prod_mem_iff (p := W)).1 hmem`. Rewrite `hW'S` using `[Finset.mem_erase, Set.Finite.mem_toFinset]`.

Conclude with `hgW W' hW'S.2 hW'S.1 hgm`. Establish `hUo : IsOpen {x : Fin n → ℂ | eval x f ≠ 0}` using `isOpen_ne_fun (MvPolynomial.continuous_eval (p := f)) continuous_const`. Use `⟨{x | eval x f ≠ 0}, hUo, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Rewrite using `[mem_closure_iff_nhds]`.

Introduce `t ht`. Assume the negation of the conclusion as `hempty`. Rewrite `hempty` using `[Set.not_nonempty_iff_eq_empty]`. Apply `hf` to reduce the goal to its premises. Use `hV n W f x hWp hx ?_` and prove the remaining obligations.

Use `filter_upwards [ht] with y hyt hyW`. Assume the negation of the conclusion as `hne`. Establish `hy : y ∈ t ∩ (GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ {x | eval x f ≠ 0})` using `⟨hyt, hyW, hne⟩`. Rewrite `hy` using `[hempty]`. Conclude with `hy`.

Introduce and unpack `x ⟨-, hxf⟩`. Use `⟨{x | eval x f ≠ 0}, hUo.mem_nhds hxf, ?_⟩` and prove the remaining obligations. Introduce and unpack `y ⟨hyI, hyf⟩`. Establish `: (RingHom.ker (eval y : MvPolynomial (Fin n) ℂ →+* ℂ)).IsPrime` using `RingHom.ker_isPrime _`. Establish `hker : I ≤ RingHom.ker (eval y : MvPolynomial (Fin n) ℂ →+* ℂ)` using `fun q hq => RingHom.mem_ker.2 (hyI q hq)`.

Take `⟨W', hW', hle⟩` from `Ideal.exists_minimalPrimes_le hker`. Distinguish the cases in `hne : W' = W`. Rewrite `hle` using `[hne]`. Introduce `q hq`. Conclude with `RingHom.mem_ker.1 (hle hq)`.

It suffices to derive a contradiction. Apply `hyf` to reduce the goal to its premises. Establish `hmem : W' ∈ S`. Rewrite using `[hS, Finset.mem_erase, Set.Finite.mem_toFinset]`. Conclude with `⟨hne, hW'⟩`.

Use `show eval y (∏ W' ∈ S, g W') = 0`. Rewrite using `[map_prod]`. Conclude with `Finset.prod_eq_zero hmem (RingHom.mem_ker.1 (hle (hgW' W' hW' hne)))`.
-/
theorem OneComponentGeneralPoint.proof (hV : VanishNearPoint.Statement) :
    OneComponentGeneralPoint.Statement := by
  classical
  intro n I W hW
  have hWp : W.IsPrime := hW.1.1
  have hfin : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ I

  have hsep : ∀ W' ∈ I.minimalPrimes, W' ≠ W → ∃ g ∈ W', g ∉ W := by
    intro W' hW' hne
    by_contra h
    push Not at h
    exact hne (le_antisymm h (hW.2 hW'.1 h))
  choose! g hgW' hgW using hsep
  set S := hfin.toFinset.erase W with hS
  set f : MvPolynomial (Fin n) ℂ := ∏ W' ∈ S, g W' with hfdef
  have hf : f ∉ W := by
    intro hmem
    obtain ⟨W', hW'S, hgm⟩ := (Ideal.IsPrime.prod_mem_iff (p := W)).1 hmem
    rw [Finset.mem_erase, Set.Finite.mem_toFinset] at hW'S
    exact hgW W' hW'S.2 hW'S.1 hgm
  have hUo : IsOpen {x : Fin n → ℂ | eval x f ≠ 0} :=
    isOpen_ne_fun (MvPolynomial.continuous_eval (p := f)) continuous_const
  refine ⟨{x | eval x f ≠ 0}, hUo, ?_, ?_⟩
  ·
    intro x hx
    rw [mem_closure_iff_nhds]
    intro t ht
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    apply hf
    refine hV n W f x hWp hx ?_
    filter_upwards [ht] with y hyt hyW
    by_contra hne
    have hy : y ∈ t ∩ (GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ {x | eval x f ≠ 0}) :=
      ⟨hyt, hyW, hne⟩
    rw [hempty] at hy
    exact hy
  ·
    rintro x ⟨-, hxf⟩
    refine ⟨{x | eval x f ≠ 0}, hUo.mem_nhds hxf, ?_⟩
    rintro y ⟨hyI, hyf⟩
    have : (RingHom.ker (eval y : MvPolynomial (Fin n) ℂ →+* ℂ)).IsPrime := RingHom.ker_isPrime _
    have hker : I ≤ RingHom.ker (eval y : MvPolynomial (Fin n) ℂ →+* ℂ) :=
      fun q hq => RingHom.mem_ker.2 (hyI q hq)
    obtain ⟨W', hW', hle⟩ := Ideal.exists_minimalPrimes_le hker
    by_cases hne : W' = W
    · rw [hne] at hle
      intro q hq
      exact RingHom.mem_ker.1 (hle hq)
    · exfalso
      apply hyf
      have hmem : W' ∈ S := by
        rw [hS, Finset.mem_erase, Set.Finite.mem_toFinset]
        exact ⟨hne, hW'⟩
      show eval y (∏ W' ∈ S, g W') = 0
      rw [map_prod]
      exact Finset.prod_eq_zero hmem (RingHom.mem_ker.1 (hle (hgW' W' hW' hne)))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
