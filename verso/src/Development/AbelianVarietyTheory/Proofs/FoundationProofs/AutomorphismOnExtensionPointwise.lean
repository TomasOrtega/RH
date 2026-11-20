import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
open GlobalTheory.K5 Polynomial
open scoped NNReal

namespace GlobalTheory

/- English proof (translation)
Introduce `Ω L K _ _ _ _ _ _ _ _ _ j s hs x`. Use `haveI : IsAlgClosure K L := ⟨‹_›, ‹_›⟩`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic`. Establish `hint : IsIntegral K (j x)` using `Algebra.IsIntegral.isIntegral _`.

Establish `hxint : IsIntegral ℚ x` using `Algebra.IsIntegral.isIntegral _`. Establish `hcomp : j.comp (algebraMap ℚ Ω) = (algebraMap K L).comp (algebraMap ℚ K)` using `RingHom.ext_rat _ _`. Use `set Q : Polynomial Ω := (minpoly ℚ x).map (algebraMap ℚ Ω) with hQ`. Establish `hQ0 : Q ≠ 0` using `Polynomial.map_ne_zero (minpoly.ne_zero hxint)`. Establish `hQj : Q.map j = ((minpoly ℚ x).map (algebraMap ℚ K)).map (algebraMap K L)`.

Rewrite using `[hQ, Polynomial.map_map, Polynomial.map_map, hcomp]`. Establish `hdvd : minpoly K (j x) ∣ (minpoly ℚ x).map (algebraMap ℚ K)`. Apply `minpoly.dvd` to reduce the goal to its premises. Rewrite using `[aeval_def, ← eval_map, ← hQj, eval_map, eval₂_at_apply, hQ, eval_map, ← aeval_def, minpoly.aeval, map_zero]`. Use `set P : L[X] := (minpoly K (j x)).map (algebraMap K L) with hP`.

Establish `hPm : P.Monic` using `(minpoly.monic hint).map _`. Establish `hPQ : P ∣ Q.map j`. Rewrite using `[hQj]`. Conclude with `Polynomial.map_dvd _ hdvd`. Establish `hroots : ∀ r ∈ P.roots, r ∈ Set.range j`.

Introduce `r hr`. Establish `h1 : r ∈ (Q.map j).roots` using `Multiset.mem_of_le (roots.le_of_dvd (Polynomial.map_ne_zero hQ0) hPQ) hr`. Rewrite `h1` using `[(IsAlgClosed.splits Q).roots_map j]`. Take `⟨a, -, ha⟩` from `Multiset.mem_map.1 h1`. Conclude with `⟨a, ha⟩`.

Establish `hlift : P ∈ lifts j`. Rewrite using `[(IsAlgClosed.splits P).eq_prod_roots_of_monic hPm]`. Use `Subsemiring.multiset_prod_mem _ _ ?_` and prove the remaining obligations. Introduce `q hq`. Take `⟨r, hr, rfl⟩` from `Multiset.mem_map.1 hq`.

Take `⟨a, rfl⟩` from `hroots r hr`. Conclude with `(mem_lifts _).2 ⟨X - C a, by simp⟩`. Take `⟨M, hM⟩` from `(mem_lifts _).1 hlift`. Establish `hMs : M.map (s : Ω →+* Ω) = M`. Use extensionality with `n`.

Rewrite using `[coeff_map]`. Use `hs _ ⟨(minpoly K (j x)).coeff n, ?_⟩` and prove the remaining obligations. Rewrite using `[← coeff_map, ← coeff_map, hM]`. Establish `hMx : M.eval x = 0`. Apply `j.injective` to reduce the goal to its premises.

Rewrite using `[← eval₂_at_apply, ← eval_map, hM, hP, eval_map, ← aeval_def, minpoly.aeval, map_zero]`. Establish `hMsx : M.eval (s x) = 0`. Establish `h` using `eval₂_at_apply (p := M) (s : Ω →+* Ω) x`. Rewrite `h` using `[← eval_map, hMs, hMx, map_zero]`. Conclude with `h`.

Establish `hroot : aeval (j (s x)) (minpoly K (j x)) = 0`. Rewrite using `[aeval_def, ← eval_map, ← hP, ← hM, eval_map, eval₂_at_apply, hMsx, map_zero]`. Conclude with `(isConjRoot_of_aeval_eq_zero hint hroot).symm.exists_algEquiv`.
-/
theorem exists_algEquiv_apply_eq_of_fixes_preimage_base :
    ∀ (Ω L K : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [Field L] [IsAlgClosed L] [Field K] [CharZero K] [Algebra K L] [Algebra.IsAlgebraic K L] (j : Ω →+* L) (s : Ω ≃ₐ[ℚ] Ω), (∀ a : Ω, j a ∈ Set.range (algebraMap K L) → s a = a) → ∀ x : Ω, ∃ g : L ≃ₐ[K] L, g (j x) = j (s x) := by
  intro Ω L K _ _ _ _ _ _ _ _ _ j s hs x
  classical
  haveI : IsAlgClosure K L := ⟨‹_›, ‹_›⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hint : IsIntegral K (j x) := Algebra.IsIntegral.isIntegral _
  have hxint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral _
  have hcomp : j.comp (algebraMap ℚ Ω) = (algebraMap K L).comp (algebraMap ℚ K) :=
    RingHom.ext_rat _ _
  set Q : Polynomial Ω := (minpoly ℚ x).map (algebraMap ℚ Ω) with hQ
  have hQ0 : Q ≠ 0 := Polynomial.map_ne_zero (minpoly.ne_zero hxint)
  have hQj : Q.map j = ((minpoly ℚ x).map (algebraMap ℚ K)).map (algebraMap K L) := by
    rw [hQ, Polynomial.map_map, Polynomial.map_map, hcomp]
  have hdvd : minpoly K (j x) ∣ (minpoly ℚ x).map (algebraMap ℚ K) := by
    apply minpoly.dvd
    rw [aeval_def, ← eval_map, ← hQj, eval_map, eval₂_at_apply, hQ, eval_map, ← aeval_def,
      minpoly.aeval, map_zero]
  set P : L[X] := (minpoly K (j x)).map (algebraMap K L) with hP
  have hPm : P.Monic := (minpoly.monic hint).map _
  have hPQ : P ∣ Q.map j := by
    rw [hQj]; exact Polynomial.map_dvd _ hdvd
  have hroots : ∀ r ∈ P.roots, r ∈ Set.range j := by
    intro r hr
    have h1 : r ∈ (Q.map j).roots :=
      Multiset.mem_of_le (roots.le_of_dvd (Polynomial.map_ne_zero hQ0) hPQ) hr
    rw [(IsAlgClosed.splits Q).roots_map j] at h1
    obtain ⟨a, -, ha⟩ := Multiset.mem_map.1 h1
    exact ⟨a, ha⟩
  have hlift : P ∈ lifts j := by
    rw [(IsAlgClosed.splits P).eq_prod_roots_of_monic hPm]
    refine Subsemiring.multiset_prod_mem _ _ ?_
    intro q hq
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hq
    obtain ⟨a, rfl⟩ := hroots r hr
    exact (mem_lifts _).2 ⟨X - C a, by simp⟩
  obtain ⟨M, hM⟩ := (mem_lifts _).1 hlift
  have hMs : M.map (s : Ω →+* Ω) = M := by
    ext n
    rw [coeff_map]
    refine hs _ ⟨(minpoly K (j x)).coeff n, ?_⟩
    rw [← coeff_map, ← coeff_map, hM]
  have hMx : M.eval x = 0 := by
    apply j.injective
    rw [← eval₂_at_apply, ← eval_map, hM, hP, eval_map, ← aeval_def, minpoly.aeval, map_zero]
  have hMsx : M.eval (s x) = 0 := by
    have h := eval₂_at_apply (p := M) (s : Ω →+* Ω) x
    rw [← eval_map, hMs, hMx, map_zero] at h
    exact h
  have hroot : aeval (j (s x)) (minpoly K (j x)) = 0 := by
    rw [aeval_def, ← eval_map, ← hP, ← hM, eval_map, eval₂_at_apply, hMsx, map_zero]
  exact (isConjRoot_of_aeval_eq_zero hint hroot).symm.exists_algEquiv

end GlobalTheory
