import Development.EtaleCohomology.DivisorCycles.OpenCoset

namespace LateralTheory.DivDb.SpecPtPf

/- English proof (translation)
Introduce `C R σ _ _ _ _ _ _ x G hG hx`. Set `I : Ideal (MvPolynomial σ C)` to `RingHom.ker (MvPolynomial.aeval (R := C) x)`. Establish `hI : I.IsPrime` using `RingHom.ker_isPrime _`. Set `P : MvPolynomial σ C` to `∏ g ∈ hG.toFinset, g`. Establish `hP : MvPolynomial.aeval x P ≠ 0`.

Simplify using `only [P, map_prod]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun g hg => hx g (hG.mem_toFinset.mp hg)`. Establish `hPI : P ∉ I.radical`. Rewrite using `[hI.radical]`. Conclude with `hP`.

Rewrite `hPI` using `[← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := C), MvPolynomial.mem_vanishingIdeal_iff]`. Use `push Not at hPI`. Take `⟨y, hy, hyP⟩` from `hPI`. Rewrite `hy` using `[MvPolynomial.mem_zeroLocus_iff]`. Use `⟨y, fun f hf => ?_, fun g hg => ?_⟩` and prove the remaining obligations.

Use `hy f (RingHom.mem_ker.mpr hf)` as an intermediate fact. Simplify `this` using `[MvPolynomial.coe_aeval_eq_eval]`. Simplify using `only [P, map_prod] at hyP`. Conclude with `(Finset.prod_ne_zero_iff.mp hyP) g (hG.mem_toFinset.mpr hg)`.
-/
theorem SpecPt_of : LateralTheory.DivDb.SpecPt := by
  intro C R σ _ _ _ _ _ _ x G hG hx
  classical
  let I : Ideal (MvPolynomial σ C) := RingHom.ker (MvPolynomial.aeval (R := C) x)
  have hI : I.IsPrime := RingHom.ker_isPrime _
  let P : MvPolynomial σ C := ∏ g ∈ hG.toFinset, g
  have hP : MvPolynomial.aeval x P ≠ 0 := by
    simp only [P, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun g hg => hx g (hG.mem_toFinset.mp hg)
  have hPI : P ∉ I.radical := by
    rw [hI.radical]; exact hP
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := C), MvPolynomial.mem_vanishingIdeal_iff] at hPI
  push Not at hPI
  obtain ⟨y, hy, hyP⟩ := hPI
  rw [MvPolynomial.mem_zeroLocus_iff] at hy
  refine ⟨y, fun f hf => ?_, fun g hg => ?_⟩
  · have := hy f (RingHom.mem_ker.mpr hf)
    simpa [MvPolynomial.coe_aeval_eq_eval] using this
  · simp only [P, map_prod] at hyP
    exact (Finset.prod_ne_zero_iff.mp hyP) g (hG.mem_toFinset.mpr hg)

end LateralTheory.DivDb.SpecPtPf
