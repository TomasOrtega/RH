import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IntToFracInjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_apply (𝓞 K) (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v), parToFrac, IsLocalization.lift_eq, kToFrac, IsFractionRing.lift_algebraMap, RingHom.comp_apply, MvPolynomial.algebraMap_eq]`.
-/
theorem parToFrac_algebraMap {K : Type*} [Field K] [NumberField K] (e n : ℕ)
    (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    parToFrac e n v (algebraMap (𝓞 K) (ParDVR e n v) x) = kToFrac K e n (algebraMap (𝓞 K) K x) := by
  rw [IsScalarTower.algebraMap_apply (𝓞 K) (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v), parToFrac,
    IsLocalization.lift_eq, kToFrac, IsFractionRing.lift_algebraMap, RingHom.comp_apply,
    MvPolynomial.algebraMap_eq]

/- English proof (translation)
Simplify using `only [secLin, linForm, map_sum, map_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `h1 : (Ideal.Quotient.mk (secIdeal Q y) (C (w j))) = algebraMap R (SecAlg Q y) (w j)` using `rfl`. Establish `h2 : (Ideal.Quotient.mk (secIdeal Q' y') (C (c (w j)))) = algebraMap S (SecAlg Q' y') (c (w j))`. Both sides reduce to the same expression.

Rewrite using `[h1, h2, hr]`. Conclude with `congrArg _ (hc j)`.
-/
theorem map_secLin {R S : Type*} [CommRing R] [CommRing S] {n e : ℕ}
    {Q : Ideal (MvPolynomial (Fin n) R)} {y : Par e n → R} {Q' : Ideal (MvPolynomial (Fin n) S)}
    {y' : Par e n → S} (ψ : SecAlg Q y →+* SecAlg Q' y') (c : R →+* S)
    (hc : ∀ j, ψ (secCoord Q y j) = secCoord Q' y' j)
    (hr : ∀ r : R, ψ (algebraMap R _ r) = algebraMap S _ (c r)) (w : Fin n → R) :
    ψ (secLin Q y w) = secLin Q' y' (fun j => c (w j)) := by
  simp only [secLin, linForm, map_sum, map_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : (Ideal.Quotient.mk (secIdeal Q y) (C (w j))) = algebraMap R (SecAlg Q y) (w j) := rfl
  have h2 : (Ideal.Quotient.mk (secIdeal Q' y') (C (c (w j)))) = algebraMap S (SecAlg Q' y') (c (w j)) :=
    rfl
  rw [h1, h2, hr]
  exact congrArg _ (hc j)

/- English proof (translation)
Introduce `K _ _ n e I f u v hI hf hu`. Take `⟨φ, hφc, hφr, hloc⟩` from `h1 K n e I v hI`. Set `_ : Algebra (SecB e I v) (SecAlg (idealF e I) (parYF K e n))` to `φ.toAlgebra`. Establish `hφinj : Function.Injective φ`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `b hb`. Take `⟨⟨m, hm⟩, hmb⟩` from `(IsLocalization.map_eq_zero_iff (Algebra.algebraMapSubmonoid (SecB e I v) (nonZeroDivisors (ParDVR e n v))) (SecAlg (idealF e I) (parYF K e n)) b).mp hb`. Take `⟨r, hr, rfl⟩` from `hm`. Conclude with `h2 K n e I v hI r b (nonZeroDivisors.ne_zero hr) ((Algebra.smul_def r b).trans hmb)`. Set `_` to `(kToFrac K e n).toAlgebra`.

Establish `hnzd` using `h3 K (ParFrac K e n) n e I f (parYF K e n) (fun j => (u j : K)) (h4 K e n) hI hf hu`. Establish `hmap : φ (secLin (modelR e I v) (parY e n v) fun j => algebraMap (𝓞 K) (ParDVR e n v) (u j)) = secLin (idealF e I) (parYF K e n) (fun j => kToFrac K e n (u j : K))`. Rewrite using `[map_secLin φ (parToFrac e n v) hφc hφr]`. Simplify using `only [parToFrac_algebraMap]`. Introduce `b c hbc`.

Apply `hφinj` to reduce the goal to its premises. Establish `h` using `congrArg φ hbc`. Simplify using `only [map_mul, hmap] at h`. Conclude with `(mul_cancel_left_mem_nonZeroDivisors hnzd).mp h`.
-/
theorem SecBLinInj.proof (h1 : SecBGeneric.Statement) (h2 : SecBTorsionFree.Statement)
    (h3 : SecLinNZD.Statement) (h4 : ParAlgIndep.Statement) : SecBLinInj.Statement := by
  intro K _ _ n e I f u v hI hf hu
  obtain ⟨φ, hφc, hφr, hloc⟩ := h1 K n e I v hI
  let _ : Algebra (SecB e I v) (SecAlg (idealF e I) (parYF K e n)) := φ.toAlgebra
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    obtain ⟨⟨m, hm⟩, hmb⟩ := (IsLocalization.map_eq_zero_iff
      (Algebra.algebraMapSubmonoid (SecB e I v) (nonZeroDivisors (ParDVR e n v)))
      (SecAlg (idealF e I) (parYF K e n)) b).mp hb
    obtain ⟨r, hr, rfl⟩ := hm
    exact h2 K n e I v hI r b (nonZeroDivisors.ne_zero hr) ((Algebra.smul_def r b).trans hmb)
  let _ := (kToFrac K e n).toAlgebra
  have hnzd := h3 K (ParFrac K e n) n e I f (parYF K e n) (fun j => (u j : K)) (h4 K e n) hI hf hu
  have hmap : φ (secLin (modelR e I v) (parY e n v) fun j => algebraMap (𝓞 K) (ParDVR e n v) (u j)) =
      secLin (idealF e I) (parYF K e n) (fun j => kToFrac K e n (u j : K)) := by
    rw [map_secLin φ (parToFrac e n v) hφc hφr]
    simp only [parToFrac_algebraMap]
  intro b c hbc
  apply hφinj
  have h := congrArg φ hbc
  simp only [map_mul, hmap] at h
  exact (mul_cancel_left_mem_nonZeroDivisors hnzd).mp h

end

end GroundTheory.Heights₂.Heights.Vertical
