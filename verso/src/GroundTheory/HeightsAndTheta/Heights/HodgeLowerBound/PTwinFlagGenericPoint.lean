import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.HypLineTer
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.GenericComplexPoint
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Cardinal

/- English proof (translation)
Introduce `K _ ι _ P d hP`. Take `⟨_, ⟨hprime, -, hrel⟩, hhor, -⟩` from `hP`. Use `hprime` as an intermediate fact. Set `Q` to `MRing ι ⧸ P`. Set `F` to `FractionRing Q`.

Establish `hQ : Function.Injective (algebraMap ℤ Q)`. Establish `e : algebraMap ℤ Q = (Ideal.Quotient.mk P).comp C` using `RingHom.ext_int _ _`. Rewrite using `[e, injective_iff_map_eq_zero]`. Introduce `n hn`. Establish `hn0 : (C n : MRing ι) ∈ P` using `Ideal.Quotient.eq_zero_iff_mem.mp hn`.

Establish `hn' : n ∈ P.comap (C : ℤ →+* MRing ι)` using `hn0`. Rewrite `hhor` using `[IsHorizontal]`. Rewrite `hn'` using `[hhor]`. Conclude with `(Ideal.mem_bot).mp hn'`. Establish `: CharZero Q` using `charZero_of_injective_algebraMap hQ`.

Establish `: CharZero F` using `charZero_of_injective_algebraMap (R := Q) (IsFractionRing.injective Q F)`. Establish `hcard : #F ≤ 𝔠`. Rewrite using `[Cardinal.mk_fractionRing]`. Use `(Cardinal.mk_le_of_surjective (Ideal.Quotient.mk_surjective (I := P))).trans ?_` and prove the remaining obligations. Use `MvPolynomial.cardinalMk_le_max.trans ?_` and prove the remaining obligations.

Conclude with `max_le (max_le (mk_int.le.trans aleph0_le_continuum) (Cardinal.mk_le_aleph0.trans aleph0_le_continuum)) aleph0_le_continuum`. Take `⟨ψ⟩` from `HilbertSamuel.exists_ringHom_complex_of_charZero F hcard`. Set `φ : MRing ι →+* ℂ` to `(ψ.comp (algebraMap Q F)).comp (Ideal.Quotient.mk P)`. Establish `hker : ∀ f, φ f = 0 ↔ f ∈ P`. Introduce `f`.

Establish `hi : Function.Injective (ψ.comp (algebraMap Q F))` using `ψ.injective.comp (IsFractionRing.injective Q F)`. Rewrite using `[show φ f = (ψ.comp (algebraMap Q F)) (Ideal.Quotient.mk P f) from rfl, map_eq_zero_iff _ hi, Ideal.Quotient.eq_zero_iff_mem]`. Set `z : (Σ k, ι k) → ℂ` to `fun p => φ (X p)`. Establish `hev : ∀ f : MRing ι, eval z (map (Int.castRingHom ℂ) f) = φ f`. Introduce `f`.

Establish `h : (eval z).comp (map (Int.castRingHom ℂ)) = φ`. Use `MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)` and prove the remaining obligations. Conclude with `RingHom.congr_fun (RingHom.ext_int (((eval z).comp (map (Int.castRingHom ℂ))).comp C) (φ.comp C)) r`. Simplify using `[z]`. Conclude with `RingHom.congr_fun h f`.

Use `⟨z, ⟨fun k => ?_, fun f hf => ?_⟩, fun f hf => ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `hrel k`. Conclude with `⟨i, fun h => hi ((hker _).mp h)⟩`. Rewrite using `[hev]`. Conclude with `(hker f).mpr hf`.

Conclude with `(hker f).mp (by rw [← hev]; exact hf)`.
-/
theorem FlagGenericPoint.proof : FlagGenericPoint.Statement := by
  intro K _ ι _ P d hP
  obtain ⟨_, ⟨hprime, -, hrel⟩, hhor, -⟩ := hP
  have := hprime
  let Q := MRing ι ⧸ P
  let F := FractionRing Q
  have hQ : Function.Injective (algebraMap ℤ Q) := by
    have e : algebraMap ℤ Q = (Ideal.Quotient.mk P).comp C := RingHom.ext_int _ _
    rw [e, injective_iff_map_eq_zero]
    intro n hn
    have hn0 : (C n : MRing ι) ∈ P := Ideal.Quotient.eq_zero_iff_mem.mp hn
    have hn' : n ∈ P.comap (C : ℤ →+* MRing ι) := hn0
    rw [IsHorizontal] at hhor
    rw [hhor] at hn'
    exact (Ideal.mem_bot).mp hn'
  have : CharZero Q := charZero_of_injective_algebraMap hQ
  have : CharZero F := charZero_of_injective_algebraMap (R := Q) (IsFractionRing.injective Q F)
  have hcard : #F ≤ 𝔠 := by
    rw [Cardinal.mk_fractionRing]
    refine (Cardinal.mk_le_of_surjective (Ideal.Quotient.mk_surjective (I := P))).trans ?_
    refine MvPolynomial.cardinalMk_le_max.trans ?_
    exact max_le (max_le (mk_int.le.trans aleph0_le_continuum)
      (Cardinal.mk_le_aleph0.trans aleph0_le_continuum)) aleph0_le_continuum
  obtain ⟨ψ⟩ := HilbertSamuel.exists_ringHom_complex_of_charZero F hcard
  let φ : MRing ι →+* ℂ := (ψ.comp (algebraMap Q F)).comp (Ideal.Quotient.mk P)
  have hker : ∀ f, φ f = 0 ↔ f ∈ P := by
    intro f
    have hi : Function.Injective (ψ.comp (algebraMap Q F)) :=
      ψ.injective.comp (IsFractionRing.injective Q F)
    rw [show φ f = (ψ.comp (algebraMap Q F)) (Ideal.Quotient.mk P f) from rfl,
      map_eq_zero_iff _ hi, Ideal.Quotient.eq_zero_iff_mem]
  let z : (Σ k, ι k) → ℂ := fun p => φ (X p)
  have hev : ∀ f : MRing ι, eval z (map (Int.castRingHom ℂ) f) = φ f := by
    intro f
    have h : (eval z).comp (map (Int.castRingHom ℂ)) = φ := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
      · exact RingHom.congr_fun
          (RingHom.ext_int (((eval z).comp (map (Int.castRingHom ℂ))).comp C) (φ.comp C)) r
      · simp [z]
    exact RingHom.congr_fun h f
  refine ⟨z, ⟨fun k => ?_, fun f hf => ?_⟩, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hrel k
    exact ⟨i, fun h => hi ((hker _).mp h)⟩
  · rw [hev]
    exact (hker f).mpr hf
  · exact (hker f).mp (by rw [← hev]; exact hf)

end GroundTheory.Heights₂.Heights.LowerBoundFree
