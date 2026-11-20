import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsFiniteFibresDimLe
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMaximalIdealHeightFG
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
Establish `hle : (hfin.toFinset.inf fun z => vanishingIdeal ℂ ({z} : Set (Fin n → ℂ))) ≤ P`. Introduce `q hq`. Rewrite using `[← IsPrime.vanishingIdeal_zeroLocus (K := ℂ) P, mem_vanishingIdeal_iff]`. Introduce `z hz`. Establish `hq'` using `(Finset.inf_le (f := fun z => vanishingIdeal ℂ ({z} : Set (Fin n → ℂ))) (hfin.mem_toFinset.2 hz)) hq`.

Conclude with `(mem_vanishingIdeal_iff.1 hq') z rfl`. Take `⟨z, -, hz⟩` from `hP.inf_le'.1 hle`. Establish `hmax : (vanishingIdeal ℂ ({z} : Set (Fin n → ℂ))).IsMaximal` using `isMaximal_iff_eq_vanishingIdeal_singleton.2 ⟨z, rfl⟩`. Rewrite using `[← hmax.eq_of_le hP.ne_top hz]` and apply the resulting hypothesis.
-/
theorem isMaximal_of_zeroLocus_finite {n : ℕ} (P : Ideal (MvPolynomial (Fin n) ℂ)) [hP : P.IsPrime]
    (hfin : (zeroLocus ℂ P : Set (Fin n → ℂ)).Finite) : P.IsMaximal := by
  have hle : (hfin.toFinset.inf fun z => vanishingIdeal ℂ ({z} : Set (Fin n → ℂ))) ≤ P := by
    intro q hq
    rw [← IsPrime.vanishingIdeal_zeroLocus (K := ℂ) P, mem_vanishingIdeal_iff]
    intro z hz
    have hq' := (Finset.inf_le (f := fun z => vanishingIdeal ℂ ({z} : Set (Fin n → ℂ)))
      (hfin.mem_toFinset.2 hz)) hq
    exact (mem_vanishingIdeal_iff.1 hq') z rfl
  obtain ⟨z, -, hz⟩ := hP.inf_le'.1 hle
  have hmax : (vanishingIdeal ℂ ({z} : Set (Fin n → ℂ))).IsMaximal :=
    isMaximal_iff_eq_vanishingIdeal_singleton.2 ⟨z, rfl⟩
  rwa [← hmax.eq_of_le hP.ne_top hz]

/- English proof (translation)
Introduce `n d Q A hQ hfin`. Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`. Take `⟨M, hM, hQM⟩` from `Ideal.exists_le_maximal Q hQ.ne_top`. Take `⟨x, hx⟩` from `isMaximal_iff_eq_vanishingIdeal_singleton.1 hM`.

Use `set y : Fin d → ℂ := A.mulVec x with hy`. Set `B` to `MvPolynomial (Fin n) ℂ ⧸ Q`. Set `_ : CommRing B` to `Ideal.Quotient.commRing Q`. Set `_ : IsDomain B` to `Ideal.Quotient.isDomain Q`. Set `_ : Algebra ℂ B` to `Ideal.Quotient.algebra ℂ`.

Set `_ : Algebra.FiniteType ℂ B` to `inferInstanceAs (Algebra.FiniteType ℂ (MvPolynomial (Fin n) ℂ ⧸ Q))`. Set `m : Ideal B` to `M.map (Ideal.Quotient.mk Q)`. Establish `hm : m.IsMaximal` using `Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hQM)`. Establish `hmp : m.IsPrime` using `hm.isPrime`. Establish `hmh : (m.height : WithBot ℕ∞) = ringKrullDim B` using `NumbersDVR.MaximalIdealHeightFG.proof ℂ B m hm`.

Establish `hlin : ∀ (z : Fin n → ℂ) (i : Fin d), eval z (ComplexSets.linPoly A i) = A.mulVec z i`. Introduce `z i`. Simplify using `[ComplexSets.linPoly, Matrix.mulVec, dotProduct, mul_comm]`. Set `f : Fin d → B` to `fun i => Ideal.Quotient.mk Q (ComplexSets.linPoly A i - C (y i))`. Establish `hfm : Set.range f ⊆ m`.

Introduce and unpack `_ ⟨i, rfl⟩`. Apply `Ideal.mem_map_of_mem` to reduce the goal to its premises. Rewrite using `[hx, mem_vanishingIdeal_singleton_iff]`. Simplify using `[hlin, hy]`. Establish `hK` using `Ideal.height_le_height_add_encard_of_subset (Set.range f) hfm`.

Establish `hcard : (Set.range f).encard ≤ d`. Rewrite using `[← Set.image_univ]`. Use `(Set.encard_image_le _ _).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Set `I : Ideal B` to `Ideal.span (Set.range f)`.

Establish `hIm : I ≤ m` using `by rw [Ideal.span_le]; exact hfm`. Set `p` to `m.map (Ideal.Quotient.mk I)`. Establish `hpp : p.IsPrime` using `Ideal.isPrime_map_quotientMk_of_isPrime hIm`. Establish `hp0 : p.height ≠ 0`. Introduce `h0`.

Express the relevant statement in the definitionally equal form `m.height ≤ p.height + _ at hK`. Rewrite `hK` using `[h0, zero_add]`. Establish `: (m.height : WithBot ℕ∞) ≤ (d : WithBot ℕ∞)`. Conclude with `hK.trans hcard` after adjusting the coercions. Conclude with `absurd (hmh ▸ this) (not_le.2 hlt)`.

Express the relevant statement in the definitionally equal form `(⟨p, hpp⟩ : PrimeSpectrum (B ⧸ I)).asIdeal.height ≠ 0 at hp0`. Rewrite `hp0` using `[PrimeSpectrum.height_eq_orderHeight, ne_eq, Order.height_eq_zero]`. Take `⟨P, hPlt⟩` from `not_isMin_iff.1 hp0`. Set `π : MvPolynomial (Fin n) ℂ →+* B ⧸ I` to `(Ideal.Quotient.mk I).comp (Ideal.Quotient.mk Q)`. Establish `hπ : Function.Surjective π` using `Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective`.

Set `P' : Ideal (MvPolynomial (Fin n) ℂ)` to `P.asIdeal.comap π`. Establish `hP' : P'.IsPrime` using `Ideal.comap_isPrime π P.asIdeal`. Establish `hP'max : ¬ P'.IsMaximal`. Introduce `hmax`. Establish `hPm : P.asIdeal.IsMaximal`.

Use `Ideal.IsMaximal.map_of_surjective_of_ker_le hπ (m := P') (by` as an intermediate fact. Introduce `a ha`. Express the relevant statement in the definitionally equal form `π a ∈ P.asIdeal`. Rewrite using `[RingHom.mem_ker.1 ha]`. Conclude with `P.asIdeal.zero_mem)`.

Rewrite `this` using `[Ideal.map_comap_of_surjective π hπ]`. Then use the resulting hypothesis. Establish `hle : P.asIdeal ≤ p` using `hPlt.le`. Conclude with `(ne_of_lt hPlt) (PrimeSpectrum.ext (hPm.eq_of_le hpp.ne_top hle))`. Apply `hP'max` to reduce the goal to its premises. Apply `isMaximal_of_zeroLocus_finite` to reduce the goal to its premises.

Use `(hfin y).subset ?_` and prove the remaining obligations. Introduce `z hz`. Rewrite `hz` using `[mem_zeroLocus_iff]`. Establish `hz' : ∀ q ∈ P', eval z q = 0` using `fun q hq => by simpa using hz q hq`. Use `⟨fun q hq => hz' q ?_, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `π q ∈ P.asIdeal`. Establish `: π q = 0`. Simplify using `[π, Ideal.Quotient.eq_zero_iff_mem.2 hq]`. Rewrite using `[this]`. Conclude with `P.asIdeal.zero_mem`.

Use function extensionality and compare the values at `i`. Establish `hmem : ComplexSets.linPoly A i - C (y i) ∈ P'`. Express the relevant statement in the definitionally equal form `π _ ∈ P.asIdeal`. Establish `: π (ComplexSets.linPoly A i - C (y i)) = 0`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk I (f i) = 0`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)`. Rewrite using `[this]`. Conclude with `P.asIdeal.zero_mem`. Use `hz' _ hmem` as an intermediate fact. Rewrite `this` using `[map_sub, eval_C, hlin, sub_eq_zero]`.

Conclude with `this`.
-/
theorem FiniteFibresDimLe.proof : FiniteFibresDimLe.Statement := by
  intro n d Q A hQ hfin
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨M, hM, hQM⟩ := Ideal.exists_le_maximal Q hQ.ne_top
  obtain ⟨x, hx⟩ := isMaximal_iff_eq_vanishingIdeal_singleton.1 hM
  set y : Fin d → ℂ := A.mulVec x with hy
  let B := MvPolynomial (Fin n) ℂ ⧸ Q
  let _ : CommRing B := Ideal.Quotient.commRing Q
  let _ : IsDomain B := Ideal.Quotient.isDomain Q
  let _ : Algebra ℂ B := Ideal.Quotient.algebra ℂ
  let _ : Algebra.FiniteType ℂ B := inferInstanceAs (Algebra.FiniteType ℂ (MvPolynomial (Fin n) ℂ ⧸ Q))
  let m : Ideal B := M.map (Ideal.Quotient.mk Q)
  have hm : m.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hQM)
  have hmp : m.IsPrime := hm.isPrime
  have hmh : (m.height : WithBot ℕ∞) = ringKrullDim B :=
    NumbersDVR.MaximalIdealHeightFG.proof ℂ B m hm
  have hlin : ∀ (z : Fin n → ℂ) (i : Fin d), eval z (ComplexSets.linPoly A i) = A.mulVec z i := by
    intro z i
    simp [ComplexSets.linPoly, Matrix.mulVec, dotProduct, mul_comm]
  let f : Fin d → B := fun i => Ideal.Quotient.mk Q (ComplexSets.linPoly A i - C (y i))
  have hfm : Set.range f ⊆ m := by
    rintro _ ⟨i, rfl⟩
    apply Ideal.mem_map_of_mem
    rw [hx, mem_vanishingIdeal_singleton_iff]
    simp [hlin, hy]
  have hK := Ideal.height_le_height_add_encard_of_subset (Set.range f) hfm
  have hcard : (Set.range f).encard ≤ d := by
    rw [← Set.image_univ]
    refine (Set.encard_image_le _ _).trans ?_
    simp
  let I : Ideal B := Ideal.span (Set.range f)
  have hIm : I ≤ m := by rw [Ideal.span_le]; exact hfm
  let p := m.map (Ideal.Quotient.mk I)
  have hpp : p.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hIm
  have hp0 : p.height ≠ 0 := by
    intro h0
    change m.height ≤ p.height + _ at hK
    rw [h0, zero_add] at hK
    have : (m.height : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by
      exact_mod_cast hK.trans hcard
    exact absurd (hmh ▸ this) (not_le.2 hlt)
  change (⟨p, hpp⟩ : PrimeSpectrum (B ⧸ I)).asIdeal.height ≠ 0 at hp0
  rw [PrimeSpectrum.height_eq_orderHeight, ne_eq, Order.height_eq_zero] at hp0
  obtain ⟨P, hPlt⟩ := not_isMin_iff.1 hp0
  let π : MvPolynomial (Fin n) ℂ →+* B ⧸ I := (Ideal.Quotient.mk I).comp (Ideal.Quotient.mk Q)
  have hπ : Function.Surjective π :=
    Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  let P' : Ideal (MvPolynomial (Fin n) ℂ) := P.asIdeal.comap π
  have hP' : P'.IsPrime := Ideal.comap_isPrime π P.asIdeal
  have hP'max : ¬ P'.IsMaximal := by
    intro hmax
    have hPm : P.asIdeal.IsMaximal := by
      have := Ideal.IsMaximal.map_of_surjective_of_ker_le hπ (m := P') (by
        intro a ha
        change π a ∈ P.asIdeal
        rw [RingHom.mem_ker.1 ha]; exact P.asIdeal.zero_mem)
      rwa [Ideal.map_comap_of_surjective π hπ] at this
    have hle : P.asIdeal ≤ p := hPlt.le
    exact (ne_of_lt hPlt) (PrimeSpectrum.ext (hPm.eq_of_le hpp.ne_top hle))
  apply hP'max
  apply isMaximal_of_zeroLocus_finite
  refine (hfin y).subset ?_
  intro z hz
  rw [mem_zeroLocus_iff] at hz
  have hz' : ∀ q ∈ P', eval z q = 0 := fun q hq => by simpa using hz q hq
  refine ⟨fun q hq => hz' q ?_, ?_⟩
  · change π q ∈ P.asIdeal
    have : π q = 0 := by
      simp [π, Ideal.Quotient.eq_zero_iff_mem.2 hq]
    rw [this]; exact P.asIdeal.zero_mem
  · funext i
    have hmem : ComplexSets.linPoly A i - C (y i) ∈ P' := by
      change π _ ∈ P.asIdeal
      have : π (ComplexSets.linPoly A i - C (y i)) = 0 := by
        change Ideal.Quotient.mk I (f i) = 0
        exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)
      rw [this]; exact P.asIdeal.zero_mem
    have := hz' _ hmem
    rw [map_sub, eval_C, hlin, sub_eq_zero] at this
    exact this

end GroundTheory.Heights₂.Heights
